import Alvoki.Storage.Disk.DiskTable
import Alvoki.Storage.Disk.WalBoundaryModel

namespace Alvoki.Storage
open Alvoki.Compaction (CheckedRun)

/-- A selected manifest and its exact ordered run bytes describe a flushed
checkpoint. An absent manifest uses the same empty base as the Linux adapter. -/
inductive CheckpointForRecovery : Option ByteArray → List ByteArray → PackedTable → Prop where
  | absent : CheckpointForRecovery none [] .empty
  | written (header : Manifest.Checkpoint) (checkpoint : PackedTable)
      (flushed : checkpoint.memory = Alvoki.Sequential.History.empty)
      (count : checkpoint.runs.length = header.runCount.toNat)
      (watermark : header.committed = checkpoint.committed)
      (floor : header.floor = checkpoint.pins.floor)
      (validFloor : header.floor ≤ header.committed)
      (bounded : ∀ run ∈ checkpoint.runs, ∀ row ∈ run.history.rows, row.sequence ≤ header.committed) :
      CheckpointForRecovery (some (Manifest.encode header))
        (checkpoint.runs.map (·.run.bytes)) checkpoint

theorem CheckpointForRecovery.loads {manifest : Option ByteArray} {files : List ByteArray}
    {checkpoint : PackedTable} (written : CheckpointForRecovery manifest files checkpoint) :
    ∃ base, (match manifest with
      | none => Except.ok PackedTable.empty
      | some bytes => do
        let header ← Manifest.decode bytes
        loadRunSet header files) = .ok base ∧ base.SameData checkpoint := by
  cases written with
  | absent => exact ⟨.empty, rfl, ⟨rfl, rfl, rfl, rfl⟩⟩
  | written header checkpoint flushed count watermark floor validFloor bounded =>
    obtain ⟨base, loaded, restored⟩ := loadRunSet_written header checkpoint.runs count validFloor bounded
    rw [watermark, floor] at restored
    refine ⟨base, ?_, PackedTable.restore_sameData flushed restored⟩
    change (do
      let decoded ← Manifest.decode (Manifest.encode header)
      loadRunSet decoded (checkpoint.runs.map fun run : CheckedRun => run.run.bytes)) = .ok base
    rw [Manifest.decode_encode header validFloor]
    exact loaded

private theorem ordinals_prefix {first : Nat} {initial suffix : List WAL.Write}
    (ordered : WAL.OrdinalsFrom first (initial ++ suffix)) : WAL.OrdinalsFrom first initial := by
  induction initial generalizing first with
  | nil => trivial
  | cons event rest ih => exact ⟨ordered.1, ih ordered.2⟩

private theorem PackedTable.SameData.symm {left right : PackedTable} (same : left.SameData right) :
    right.SameData left :=
  ⟨same.runs.symm, same.memory.symm, same.committed.symm, same.floor.symm⟩

/-- For a supplied manifest and marker pair, the production loader, selector
and replay recover the old or extended history. The reference replays from
the original checkpoint and may have a different pin registry. Given an
abstract checkpoint, replay applies the exact selected suffix and newly
acquired pins read that abstract result at every supported snapshot. A trace
invariant must establish that the selected pair is reachable and the checkpoint
represents the covered prefix. -/
theorem recoverWriteCutSelectedPair {manifest marker : Option ByteArray} {files : List ByteArray}
    {checkpoint : PackedTable} {covered pending : List WAL.Write}
    {event : WAL.Write} {wal : ByteArray} {image : Publication.Image}
    (written : CheckpointForRecovery manifest files checkpoint)
    (cut : WAL.Boundary.WriteCut (covered ++ pending) event wal image)
    (chosen : marker = image.active ∨ marker ∈ image.crashImages)
    (oldFits : (WAL.encode (covered ++ pending)).size < UInt64.size)
    (newFits : (WAL.encode ((covered ++ pending) ++ [event])).size < UInt64.size)
    (ordered : WAL.OrdinalsFrom 1 ((covered ++ pending) ++ [event]))
    (watermark : covered.length = checkpoint.committed.toNat) :
    ∃ markerBytes events base reopened reference, marker = some markerBytes ∧
      (match manifest with
      | none => Except.ok PackedTable.empty
      | some bytes => do
        let header ← Manifest.decode bytes
        loadRunSet header files) = .ok base ∧
      (do
        let count ← WAL.Boundary.decode markerBytes
        WAL.Boundary.select count wal) = .ok (WAL.encode events) ∧
      recoverSelected base (WAL.encode events) = .ok reopened ∧
      (events = covered ++ pending ∨ events = (covered ++ pending) ++ [event]) ∧
      reopened.committed.toNat = events.length ∧
      replay checkpoint (events.drop covered.length) = .ok reference ∧
      reference.SameData reopened ∧
      (∀ model : Sequential.SnapshotTable UInt64, checkpoint.Refines model →
        ∃ abstract, SnapshotWalReplay model (events.drop covered.length) abstract ∧
          abstract.committed.toNat = events.length ∧
          ∀ snapshot : UInt64, abstract.pins.floor ≤ snapshot → snapshot.toNat ≤ events.length →
            ∃ pin pinned, reopened.acquireAt snapshot = some (pin, pinned) ∧
              (∀ key, pinned.lookup pin.handle key = some (abstract.table.lookup key snapshot)) ∧
              (∀ start stop, pinned.range pin.handle start stop =
                some (abstract.table.range start stop snapshot))) := by
  obtain ⟨base, loaded, same⟩ := written.loads
  obtain ⟨markerBytes, events, bound, history, selected⟩ :=
    WAL.Boundary.write_cut_selects_old_or_new cut oldFits newFits chosen
  obtain ⟨suffix, split, ordinals⟩ :
      ∃ suffix, events = covered ++ suffix ∧ WAL.OrdinalsFrom 1 (covered ++ suffix) := by
    rcases history with prior | advanced
    · exact ⟨pending, prior, ordinals_prefix ordered⟩
    · exact ⟨pending ++ [event], by simpa only [List.append_assoc] using advanced,
        by simpa only [List.append_assoc] using ordered⟩
  subst events
  have count : covered.length = base.committed.toNat := by simpa only [same.committed] using watermark
  obtain ⟨reopened, recovered, sequence⟩ := recoverSelected_encoded_complete base covered suffix ordinals count
  have replayed := (recoverSelected_encoded base covered suffix ordinals count).symm.trans recovered
  obtain ⟨reference, expected, agrees⟩ := replay_sameData same.symm suffix replayed
  have finalCount : reopened.committed.toNat = (covered ++ suffix).length := by
    simpa only [List.length_append] using sequence
  refine ⟨markerBytes, covered ++ suffix, base, reopened, reference, bound, loaded, selected,
    recovered, history, finalCount, by simpa only [List.drop_left] using expected, agrees, ?_⟩
  intro model represents
  obtain ⟨abstract, modeled, refined⟩ := replay_refines represents expected
  refine ⟨abstract, by simpa only [List.drop_left] using modeled, ?_, ?_⟩
  · rw [← refined.committed, agrees.committed, finalCount]
  · intro snapshot retained within
    have floor : reference.pins.floor ≤ snapshot := by simpa only [refined.pins] using retained
    have committed : snapshot ≤ reference.committed := UInt64.le_iff_toNat_le.mpr (by
      simpa only [agrees.committed, finalCount] using within)
    simpa only [refined.table] using agrees.symm.acquireAt_reads floor committed

end Alvoki.Storage
