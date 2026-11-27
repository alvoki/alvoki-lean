import Alvoki.Storage.Disk.Proofs.Checkpoint.MarkedCheckpointReady
import Alvoki.Storage.Disk.Proofs.Read.RecoveredPinRefinement
import Alvoki.Storage.Disk.Proofs.WAL.RetainedWalBoundary
import Alvoki.Storage.Disk.Proofs.Checkpoint.VersionedCheckpointLineage
import Alvoki.Storage.Disk.Proofs.Collection.WalSegmentCollection

namespace Alvoki.Storage

open Sequential (SnapshotTable)
open WAL (Write frameSize)

private theorem ordinals_take {first : Nat} {history : List Write}
    (ordered : WAL.OrdinalsFrom first history) (limit : Nat) : WAL.OrdinalsFrom first (history.take limit) := by
  induction limit generalizing first history with
  | zero => trivial
  | succ limit ih =>
    cases history with
    | nil => trivial
    | cons event rest => exact ⟨ordered.1, ih ordered.2⟩

/-- Both recovery workers use the same selected marker and loaded checkpoint.
The retained reads return the same table and the physical portion of the
selected WAL. The canonical history ends at that marker. -/
structure WalSegmentRecovery (after : WalSegmentImage) (pair : DirectoryPublication.Bindings)
    (range : MarkedWalRange) (history : List Write) (base : PackedTable) (first : Nat) (table : PackedTable) : Prop where
  startCovered : first ≤ range.watermark
  historyRetained : WalSegment.concatenate (after.afterWatermark range.watermark) = WAL.encode (history.drop first)
  count : table.committed.toNat = range.through
  marked : ∃ marker length selected, pair.walBoundary = some marker ∧ WAL.Boundary.decode marker = .ok length ∧
      length.toNat = range.through * frameSize ∧
      selected = WAL.encode ((history.take range.through).drop first) ∧
      WAL.Boundary.recoverRetainedMarked base first length
        (WalSegment.concatenate (after.afterWatermark range.watermark)) = .ok (selected, table) ∧
      WAL.Boundary.recoverMarked base length (WAL.encode history) = .ok (WAL.encode (history.take range.through), table)
  refines : ∃ model, table.Refines model ∧ RepresentsWalHistory (history.take range.through) model

/-- For any pair still selectable after collection, feed the exact retained
run of WAL segments to marked recovery. The loaded base represents the
checkpoint's covered prefix. No success premise is needed for either worker. -/
theorem WalSegmentCollectionRetry.recoversSelected
    {initial after : WalSegmentImage} {history : List Write} (retry : WalSegmentCollectionRetry initial after)
    (valid : initial.Valid history) {pair : DirectoryPublication.Bindings} (chosen : after.Selects pair)
    {range : MarkedWalRange} (decoded : pair.walRange = some range) {base : PackedTable}
    {model : SnapshotTable UInt64} (committed : base.committed.toNat = range.watermark)
    (refines : base.Refines model) (represents : RepresentsWalHistory (history.take range.watermark) model)
    (ordered : WAL.OrdinalsFrom 1 history) :
    ∃ first table, WalSegmentRecovery after pair range history base first table := by
  obtain ⟨found, first, parsed, begins, beforeMarker, within, retained⟩ := retry.retainedBytes valid chosen
  have exactRange := Option.some.inj (parsed.symm.trans decoded)
  subst found
  obtain ⟨_, _, marker, length, visible, decodedMarker, byteCount⟩ :=
    DirectoryPublication.Bindings.walRange_accounting decoded
  let chosenHistory := history.take range.through
  let covered := history.take range.watermark
  let pending := chosenHistory.drop range.watermark
  have watermarkWithin := Nat.le_trans beforeMarker within
  have firstWithin := Nat.le_trans begins watermarkWithin
  have firstBeforeMarker := Nat.le_trans begins beforeMarker
  have chosenLength : chosenHistory.length = range.through := by
    simp [chosenHistory, Nat.min_eq_left within]
  have coveredLength : covered.length = base.committed.toNat := by
    simp [covered, committed, Nat.min_eq_left watermarkWithin]
  have exactCovered : chosenHistory.take range.watermark = covered := by
    simp [chosenHistory, covered, List.take_take, Nat.min_eq_left beforeMarker]
  have splitCovered : covered ++ pending = chosenHistory := by
    simpa [pending, exactCovered] using (List.take_append_drop range.watermark chosenHistory)
  have numbered : WAL.OrdinalsFrom 1 (covered ++ pending) := splitCovered.symm ▸ ordinals_take ordered _
  obtain ⟨table, recovered, count⟩ := recoverSelected_encoded_complete base covered pending numbered coveredLength
  have played := (recoverSelected_encoded base covered pending numbered coveredLength).symm.trans recovered
  rw [splitCovered] at recovered
  have total : table.committed.toNat = range.through := by
    rwa [← List.length_append, splitCovered, chosenLength] at count
  obtain ⟨abstract, replayed, refined⟩ := replay_refines refines played
  have represented := splitCovered ▸ represents.append replayed
  have encodedSize : (WAL.encode chosenHistory).size = length.toNat := by
    rw [WAL.encode_size, chosenLength, byteCount, Nat.mul_comm]
  have countEq : length = (WAL.encode chosenHistory).size.toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [encodedSize, UInt64.toNat_ofNat_of_lt' length.toNat_lt_size]
  have fullSelect : WAL.Boundary.select length (WAL.encode history) = .ok (WAL.encode chosenHistory) := by
    have chosenFits : (WAL.encode chosenHistory).size < UInt64.size := encodedSize.symm ▸ length.toNat_lt_size
    have select := WAL.Boundary.select_encoded chosenHistory (WAL.encode (history.drop range.through)) chosenFits
    rw [← WAL.encode_append, List.take_append_drop, ← countEq] at select
    exact select
  have full : WAL.Boundary.recoverMarked base length (WAL.encode history) = .ok (WAL.encode chosenHistory, table) := by
    simp [WAL.Boundary.recoverMarked, fullSelect, recovered, Bind.bind, Except.bind, Pure.pure, Except.pure]
  let removed := history.take first
  have removedLength : removed.length = first := by simp [removed, Nat.min_eq_left firstWithin]
  have removedCovered : removed.length ≤ base.committed.toNat := by rwa [removedLength, committed]
  have removedBeforeMarker : (WAL.encode removed).size ≤ length.toNat := by
    rw [WAL.encode_size, removedLength, byteCount, Nat.mul_comm frameSize]
    exact Nat.mul_le_mul_right frameSize firstBeforeMarker
  have compared := WAL.Boundary.recoverRetainedMarked_eq_recoverMarked base length (WAL.encode (history.drop first))
    (WAL.decodeOrdinals_encode removed (ordinals_take ordered first)) (by simp) removedCovered removedBeforeMarker
  rw [removedLength, ← WAL.encode_append, List.take_append_drop, ← retained, full] at compared
  have samePrefix : chosenHistory.take first = removed := by
    simp [chosenHistory, removed, List.take_take, Nat.min_eq_left firstBeforeMarker]
  have splitRemoved : WAL.encode chosenHistory = WAL.encode removed ++ WAL.encode (chosenHistory.drop first) := by
    rw [← WAL.encode_append, ← samePrefix, List.take_append_drop]
  cases actual : WAL.Boundary.recoverRetainedMarked base first length
      (WalSegment.concatenate (after.afterWatermark range.watermark)) with
  | error message => rw [actual] at compared; contradiction
  | ok result =>
    obtain ⟨selected, recoveredTable⟩ := result
    rw [actual] at compared
    have installed := Except.ok.inj compared
    have sameBytes := (congrArg Prod.fst installed).symm.trans splitRemoved
    have sameTable : table = recoveredTable := congrArg Prod.snd installed
    subst recoveredTable
    exact ⟨first, table, begins, retained, total,
      ⟨marker, length, selected, visible, decodedMarker, byteCount, (ByteArray.append_right_inj _).mp sameBytes,
        actual, full⟩, abstract, refined, represented⟩

/-- Recover from the exact ordered run bytes loaded for the strict v2
checkpoint selected by the same pair as the WAL marker. -/
theorem WalSegmentCollectionRetry.recoversLoaded
    {initial after : WalSegmentImage} {history : List Write} (retry : WalSegmentCollectionRetry initial after)
    (valid : initial.Valid history) {pair : DirectoryPublication.Bindings} (chosen : after.Selects pair)
    {range : MarkedWalRange} (decoded : pair.walRange = some range)
    {image : CheckpointPublication.Image} {bytes : ByteArray} (manifest : pair.manifest = some bytes)
    (reads : VersionedCheckpointFileReads image.durable (some bytes))
    (accepted : image.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history) (some bytes))
    {base : PackedTable} {generation : UInt64} (loaded : reads.result = .ok (some (base, generation)))
    (ordered : WAL.OrdinalsFrom 1 history) :
    ∃ first table, WalSegmentRecovery after pair range history base first table := by
  have observedWatermark := (DirectoryPublication.Bindings.walRange_accounting decoded).1
  rw [manifest] at observedWatermark
  obtain ⟨selected, integrity, observedClock⟩ := selectedCheckpointWatermark_present_iff.mp observedWatermark
  obtain ⟨files, _, _, ⟨checkpoint, model, written, refined, historyPrefix⟩, _, structural, _, _⟩ :=
    reads.loaded_lineage accepted (Manifest.VersionedCheckpoint.decode_integrity integrity) loaded
  have watermark := observedClock.symm
  have headerClock : selected.header.committed = checkpoint.committed := written.watermark
  obtain ⟨expectedBase, interpreted, same⟩ := written.loads
  have sameBase := Except.ok.inj (interpreted.symm.trans structural)
  subst expectedBase
  have fresh := loadRunSet_clearsPins structural
  obtain ⟨rebound, baseRefines, sameTable, sameClock, sameFloor⟩ := same.refines_rebindPins refined (by simp [fresh])
  have baseClock : base.committed.toNat = range.watermark := by
    rw [same.committed, watermark, headerClock]
  have baseHistory : RepresentsWalHistory (history.take range.watermark) rebound := by
    rw [watermark, headerClock]
    exact historyPrefix.preserve sameClock (UInt64.le_of_eq sameFloor.symm)
      (baseRefines.rowsBounded (same.rowBounds written.rowBounds)) (fun _ _ _ => by rw [sameTable])
  exact retry.recoversSelected valid chosen decoded baseClock baseRefines baseHistory ordered

/-- The absent checkpoint path uses the same empty base and covers zero
frames. Collection still uses the actual selected marked-WAL boundary. -/
theorem WalSegmentCollectionRetry.recoversAbsent
    {initial after : WalSegmentImage} {history : List Write} (retry : WalSegmentCollectionRetry initial after)
    (valid : initial.Valid history) {pair : DirectoryPublication.Bindings} (chosen : after.Selects pair)
    {range : MarkedWalRange} (decoded : pair.walRange = some range) (absent : pair.manifest = none)
    (ordered : WAL.OrdinalsFrom 1 history) :
    ∃ first table, WalSegmentRecovery after pair range history .empty first table := by
  have watermark := (DirectoryPublication.Bindings.walRange_accounting decoded).1
  have emptyWatermark : range.watermark = 0 := by
    have zero : selectedCheckpointWatermark pair.manifest = some 0 := by rw [absent]; rfl
    exact Option.some.inj (watermark.symm.trans zero)
  have committed : PackedTable.empty.committed.toNat = range.watermark := emptyWatermark.symm
  exact retry.recoversSelected valid chosen decoded committed PackedTable.empty_refines
    (by simpa [emptyWatermark] using RepresentsWalHistory.empty) ordered

/-- Any sequence within the recovered floor and marker can be pinned anew.
That pin gives the point and ordered range reads of canonical WAL replay. -/
theorem WalSegmentRecovery.acquireReads {after : WalSegmentImage} {pair : DirectoryPublication.Bindings}
    {range : MarkedWalRange} {history : List Write} {base table : PackedTable} {first : Nat}
    (result : WalSegmentRecovery after pair range history base first table)
    {reference : SnapshotTable UInt64} (replayed : SnapshotWalReplay .empty (history.take range.through) reference)
    {snapshot : UInt64} (retained : table.pins.floor ≤ snapshot) (within : snapshot.toNat ≤ range.through) :
    ∃ pin pinned, table.acquireAt snapshot = some (pin, pinned) ∧
      (∀ key, pinned.lookup pin.handle key = some (reference.table.lookup key snapshot)) ∧
      ∀ start stop, pinned.range pin.handle start stop = some (reference.table.range start stop snapshot) := by
  have committed : snapshot ≤ table.committed := UInt64.le_iff_toNat_le.mpr (result.count.symm ▸ within)
  have same : table.SameData table := ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨pin, pinned, acquired, lookup, scan⟩ := same.acquireAt_reads retained committed
  obtain ⟨_, refined, canonical⟩ := result.refines
  obtain ⟨pointReads, rangeReads⟩ := canonical.reads replayed (refined.pins ▸ retained)
  exact ⟨pin, pinned, acquired, fun key => by rw [lookup, refined.table, pointReads],
    fun start stop => by rw [scan, refined.table, rangeReads]⟩

end Alvoki.Storage
