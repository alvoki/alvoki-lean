import Alvoki.Storage.Disk.MarkedCheckpointReady
import Alvoki.Storage.Disk.MarkedOpenControl
import Alvoki.Storage.Disk.VersionedCheckpointLineage
import Alvoki.Storage.Disk.RecoveredPinRefinement

namespace Alvoki.WAL.Boundary
open Storage Manifest

private theorem runSharedMarkedOpen_exactAligned
    {before : ReopenImage} {history : List WAL.Write}
    {checkpoint : Except String (Option (PackedTable × UInt64))}
    {loaded : Option (PackedTable × UInt64)} {table : PackedTable}
    (checkpointRead : checkpoint = .ok loaded)
    (reads : MarkedWalReads before)
    (markerRead : reads.marker = .ok (some (encode (WAL.encode history).size.toUInt64)))
    (walRead : reads.wal = .ok (some (WAL.encode history)))
    (fits : (WAL.encode history).size < UInt64.size)
    (replayed : recoverSelected (loaded.getD (.empty, 0)).1 (WAL.encode history) = .ok table)
    (report : Publication.Step → RepairReport) :
    runSharedMarkedOpen checkpoint reads.marker reads.wal report .success before =
      .ok (table, (loaded.getD (.empty, 0)).2, (WAL.encode history).size) before.syncDirectory := by
  let wal := WAL.encode history
  have chosen : select wal.size.toUInt64 wal = .ok wal := by
    simpa [wal] using select_encoded history ByteArray.empty fits
  let observations := MarkedReopenReads.mk reads (checkpoint.map fun result => (result.getD (.empty, 0)).1)
  have baseRead : observations.checkpoint = .ok (loaded.getD (.empty, 0)).1 := by
    simp [observations, checkpointRead, Except.map]
  have preflight : observations.preflight = .ok ⟨wal, wal, table⟩ :=
    observations.preflight_succeeds baseRead markerRead walRead (decode_encode _) chosen replayed
  have opened : runMarkedReopen (.ok ⟨wal, wal, table⟩) report false .success before =
      .ok table before.syncDirectory := by
    simp only [runMarkedReopen, Publication.finishReopen, Publication.runReopen, Nat.lt_irrefl, ↓reduceIte]
    rfl
  rw [runSharedMarkedOpen_eq _ _ _ (by simp [markerRead]) _ _ _]
  change (match runMarkedReopen observations.preflight report false .success before with
    | .error message after => EStateM.Result.error message after
    | .ok installed after =>
      .ok (installed, ((checkpoint.toOption.getD none).getD (.empty, 0)).2,
        (observations.preflight.toOption.map (fun value : MarkedPreflight => value.selected.size)).getD 0) after) = _
  rw [preflight, opened, checkpointRead]
  rfl

private theorem alignedSettledFor {before : ReopenImage} {history : List WAL.Write} {manifest : Option ByteArray}
    (visible : before.directory.active.manifest = manifest) (reads : MarkedWalReads before)
    (markerRead : reads.marker = .ok (some (encode (WAL.encode history).size.toUInt64)))
    (walRead : reads.wal = .ok (some (WAL.encode history))) : before.syncDirectory.SettledFor manifest history := by
  refine ⟨?_, rfl, reads.walVisible _ walRead, rfl⟩
  change (⟨before.directory.active.manifest, before.directory.active.walBoundary⟩ :
    DirectoryPublication.Bindings) = ⟨_, _⟩
  rw [visible, reads.markerVisible _ markerRead]

/-- The selected durable runs determine the checkpoint and its replay.
The pure recovery argument supplies the recovered representation before
a reader is used to identify those bytes in a native execution. -/
theorem _root_.Alvoki.Storage.CheckpointPublication.Image.replaysVersionedRuns
    {image : CheckpointPublication.Image} {bytes : ByteArray} {selected : VersionedCheckpoint}
    {history : List WAL.Write}
    (decoded : VersionedCheckpoint.decode bytes = .ok selected)
    (accepted : image.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history) (some bytes))
    (fits : (WAL.encode history).size < UInt64.size) (ordered : WAL.OrdinalsFrom 1 history) :
    ∃ files base table,
      (List.range selected.header.runCount.toNat).mapM
        (image.durable selected.header.generation) = some files ∧
      selected.ValidatesFiles files ∧ loadRunSet selected.header files = .ok base ∧
      replay base (history.drop selected.header.committed.toNat) = .ok table ∧
      recoverSelected base (WAL.encode history) = .ok table ∧
      table.committed.toNat = history.length ∧ table.RowBounds ∧
      ∃ model, table.Refines model ∧ RepresentsWalHistory history model ∧ table.pins.active = [] := by
  obtain ⟨files, durable, ⟨checkpoint, baseModel, written, baseRefines, baseHistory⟩, validated, covered⟩ :=
    image.acceptsVersioned_runs accepted decoded
  have watermark := written.watermark
  obtain ⟨base, structural, same⟩ := written.loads
  have historyFits : history.length < UInt64.size := by
    rw [WAL.encode_size] at fits
    simp [WAL.frameSize] at fits
    omega
  have within : selected.header.committed.toNat ≤ history.length := by
    simpa only [UInt64.toNat_ofNat_of_lt' historyFits] using UInt64.le_iff_toNat_le.mp covered
  let prefixLength := selected.header.committed.toNat
  let coveredPrefix := history.take prefixLength
  let suffix := history.drop prefixLength
  have split : coveredPrefix ++ suffix = history := List.take_append_drop ..
  have clock : coveredPrefix.length = base.committed.toNat := by
    simp [coveredPrefix, prefixLength, same.committed, ← watermark, Nat.min_eq_left within]
  obtain ⟨table, replayed, count⟩ :=
    recoverSelected_encoded_complete base coveredPrefix suffix (split.symm ▸ ordered) clock
  have exactReplay : replay base suffix = .ok table := by
    rw [← recoverSelected_encoded base coveredPrefix suffix (split.symm ▸ ordered) clock]
    exact replayed
  rw [split] at replayed
  have total : table.committed.toNat = history.length := by
    rwa [← List.length_append, split] at count
  obtain ⟨abstract, model, applied, refined, sameTable, sameClock, sameFloor, fresh⟩ :=
    replay_refines_recoveredPins same (loadRunSet_clearsPins structural) baseRefines exactReplay
  have abstractHistory : RepresentsWalHistory history abstract := by
    rw [← split]
    change RepresentsWalHistory (history.take selected.header.committed.toNat ++ suffix) abstract
    rw [watermark]
    exact baseHistory.append applied
  have bounded := replay_rowBounds (same.rowBounds written.rowBounds) exactReplay
  have represented := abstractHistory.preserve sameClock (UInt64.le_of_eq sameFloor.symm)
    (refined.rowsBounded bounded) (fun snapshot _ key => by rw [sameTable])
  exact ⟨files, base, table, durable, validated, structural, exactReplay, replayed, total, bounded,
    model, refined, represented, by rw [refined.pins, fresh]⟩

/-- A checked versioned checkpoint and the exact selected WAL bytes load
and replay independently of the durability branch used to settle them. -/
theorem _root_.Alvoki.Storage.VersionedCheckpointFileReads.replays_selected
    {image : CheckpointPublication.Image} {bytes : ByteArray} {selected : VersionedCheckpoint}
    {history : List WAL.Write}
    (reads : VersionedCheckpointFileReads image.durable (some bytes))
    (decoded : VersionedCheckpoint.decode bytes = .ok selected)
    (accepted : image.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history) (some bytes))
    (manifestRead : reads.readManifest = .ok (some bytes))
    (runReads : ∀ index, index < selected.header.runCount.toNat →
      ∃ payload, reads.readRun selected.header.generation index = .ok payload)
    (fits : (WAL.encode history).size < UInt64.size) (ordered : WAL.OrdinalsFrom 1 history) :
    ∃ files base table,
      (List.range selected.header.runCount.toNat).mapM
        (image.durable selected.header.generation) = some files ∧
      selected.ValidatesFiles files ∧ loadRunSet selected.header files = .ok base ∧
      reads.result = .ok (some (base, selected.header.generation)) ∧
      replay base (history.drop selected.header.committed.toNat) = .ok table ∧
      recoverSelected base (WAL.encode history) = .ok table ∧
      table.committed.toNat = history.length ∧ table.RowBounds ∧
      ∃ model, table.Refines model ∧ RepresentsWalHistory history model ∧ table.pins.active = [] := by
  obtain ⟨files, base, table, durable, validated, structural, exactReplay, replayed, total, bounded,
    model, refined, represented, fresh⟩ := image.replaysVersionedRuns decoded accepted fits ordered
  have loaded := reads.completes_selected manifestRead decoded runReads durable validated structural
  exact ⟨files, base, table, durable, validated, structural, loaded, exactReplay, replayed, total, bounded,
    model, refined, represented, fresh⟩

/-- A marked open with a valid selected versioned checkpoint loads its runs
and replays precisely the suffix above the selected watermark. Success of
the indicated reads and aligned durability operation suffices for recovery
without assuming a successful load or open. -/
theorem VersionedCheckpointFileReads.completes_marked
    {image : CheckpointPublication.Image} {before : ReopenImage}
    {bytes : ByteArray} {selected : VersionedCheckpoint} {history : List WAL.Write}
    (reads : VersionedCheckpointFileReads image.durable (some bytes))
    (visible : before.directory.active.manifest = some bytes)
    (decoded : VersionedCheckpoint.decode bytes = .ok selected)
    (accepted : image.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history) (some bytes))
    (manifestRead : reads.readManifest = .ok (some bytes))
    (runReads : ∀ index, index < selected.header.runCount.toNat →
      ∃ payload, reads.readRun selected.header.generation index = .ok payload)
    (walReads : MarkedWalReads before)
    (markerRead : walReads.marker = .ok (some (encode (WAL.encode history).size.toUInt64)))
    (walRead : walReads.wal = .ok (some (WAL.encode history)))
    (fits : (WAL.encode history).size < UInt64.size) (ordered : WAL.OrdinalsFrom 1 history)
    (report : Publication.Step → RepairReport) :
    ∃ files base table,
      (List.range selected.header.runCount.toNat).mapM
        (image.durable selected.header.generation) = some files ∧
      selected.ValidatesFiles files ∧ loadRunSet selected.header files = .ok base ∧
      reads.result = .ok (some (base, selected.header.generation)) ∧
      replay base (history.drop selected.header.committed.toNat) = .ok table ∧
      runSharedMarkedOpen reads.result walReads.marker walReads.wal report .success before =
        .ok (table, selected.header.generation, (WAL.encode history).size) before.syncDirectory ∧
      before.syncDirectory.SettledFor (some bytes) history ∧ table.committed.toNat = history.length ∧
      table.RowBounds ∧
      ∃ model, table.Refines model ∧ RepresentsWalHistory history model ∧ table.pins.active = [] := by
  obtain ⟨files, base, table, durable, validated, structural, loaded, exactReplay, replayed, total, bounded,
    model, refined, represented, fresh⟩ := reads.replays_selected decoded accepted manifestRead runReads fits ordered
  have installed := runSharedMarkedOpen_exactAligned loaded walReads markerRead walRead fits replayed report
  have settled := alignedSettledFor visible walReads markerRead walRead
  exact ⟨files, base, table, durable, validated, structural, loaded, exactReplay, installed, settled, total, bounded,
    model, refined, represented, fresh⟩

/-- If the first checkpoint was discarded, an absent manifest lets the
same marked open replay the entire WAL from the empty table. -/
theorem VersionedCheckpointFileReads.completes_marked_absent
    {image : CheckpointPublication.Image} {before : ReopenImage} {history : List WAL.Write}
    (reads : VersionedCheckpointFileReads image.durable none)
    (visible : before.directory.active.manifest = none) (manifestRead : reads.readManifest = .ok none)
    (walReads : MarkedWalReads before)
    (markerRead : walReads.marker = .ok (some (encode (WAL.encode history).size.toUInt64)))
    (walRead : walReads.wal = .ok (some (WAL.encode history)))
    (fits : (WAL.encode history).size < UInt64.size) (ordered : WAL.OrdinalsFrom 1 history)
    (report : Publication.Step → RepairReport) :
    ∃ table model, replay .empty history = .ok table ∧
      runSharedMarkedOpen reads.result walReads.marker walReads.wal report .success before =
        .ok (table, 0, (WAL.encode history).size) before.syncDirectory ∧
      before.syncDirectory.SettledFor none history ∧ table.RowBounds ∧ table.Refines model ∧
      RepresentsWalHistory history model ∧ table.pins.active = [] := by
  have loaded : reads.result = .ok none := by
    simp [VersionedCheckpointFileReads.result, readVersionedCheckpoint, manifestRead, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  obtain ⟨table, applied, _⟩ := replay_ordinals_complete .empty history ordered
  have replayed : recoverSelected .empty (WAL.encode history) = .ok table := by
    simpa using (recoverSelected_encoded .empty [] history ordered rfl).trans applied
  have installed := runSharedMarkedOpen_exactAligned loaded walReads markerRead walRead fits replayed report
  obtain ⟨model, abstract, refined⟩ := replay_refines PackedTable.empty_refines applied
  exact ⟨table, model, applied, installed, alignedSettledFor visible walReads markerRead walRead,
    replay_rowBounds PackedTable.empty_rowBounds applied, refined,
    List.nil_append history ▸ RepresentsWalHistory.empty.append abstract, by rw [replay_pins applied]; rfl⟩

/-- The selected binding determines the base and its installed generation.
This also covers a writer that has yet to publish a checkpoint. -/
theorem _root_.Alvoki.Storage.VersionedCheckpointFileReads.replays_history
    {image : CheckpointPublication.Image} {binding : Option ByteArray} {history : List WAL.Write}
    (reads : VersionedCheckpointFileReads image.durable binding)
    (accepted : image.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history) binding)
    (manifestRead : reads.readManifest = .ok binding)
    (runReads : ∀ bytes selected, binding = some bytes → VersionedCheckpoint.decode bytes = .ok selected →
      ∀ index, index < selected.header.runCount.toNat →
        ∃ payload, reads.readRun selected.header.generation index = .ok payload)
    (fits : (WAL.encode history).size < UInt64.size) (ordered : WAL.OrdinalsFrom 1 history) :
    ∃ loaded table model,
      reads.result = .ok loaded ∧
      ((binding.mapM fun bytes => (VersionedCheckpoint.decode bytes).map (·.header.generation)).map
        (·.getD 0) : Except String UInt64) = .ok (loaded.getD (.empty, 0)).2 ∧
      recoverSelected (loaded.getD (.empty, 0)).1 (WAL.encode history) = .ok table ∧
      table.RowBounds ∧ table.Refines model ∧ RepresentsWalHistory history model ∧ table.pins.active = [] := by
  cases binding with
  | none =>
    have loaded : reads.result = .ok none := by
      change readVersionedCheckpoint reads.readManifest reads.readRun id = _
      rw [manifestRead]
      exact readVersionedCheckpoint_absent (m := Except String) reads.readRun id
    obtain ⟨table, applied, _⟩ := replay_ordinals_complete .empty history ordered
    have recovered : recoverSelected .empty (WAL.encode history) = .ok table := by
      simpa using (recoverSelected_encoded .empty [] history ordered rfl).trans applied
    obtain ⟨model, abstract, refined⟩ := replay_refines PackedTable.empty_refines applied
    exact ⟨none, table, model, loaded, rfl, recovered, replay_rowBounds PackedTable.empty_rowBounds applied,
      refined, List.nil_append history ▸ RepresentsWalHistory.empty.append abstract,
      by rw [replay_pins applied]; rfl⟩
  | some bytes =>
    have ⟨selected, decoded, _⟩ := accepted
    obtain ⟨_, base, table, _, _, _, loaded, _, recovered, _, bounded, model, refined, represented, pins⟩ :=
      reads.replays_selected decoded accepted manifestRead (runReads bytes selected rfl decoded) fits ordered
    refine ⟨some (base, selected.header.generation), table, model, loaded, ?_, recovered, bounded, refined,
      represented, pins⟩
    simp [Option.mapM, decoded, Functor.map, Except.map]

end Alvoki.WAL.Boundary
