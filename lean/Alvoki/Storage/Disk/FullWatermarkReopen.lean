import Alvoki.Storage.Disk.DiskRecoveryModel

namespace Alvoki.Storage

open Alvoki.Compaction (CheckedRun)
open Alvoki.Sequential (SnapshotTable)

private theorem loadRunSet_clearsPins {header : Manifest.Checkpoint} {files : List ByteArray}
    {table : PackedTable} (loaded : loadRunSet header files = .ok table) :
    table.pins.active = [] := by
  unfold loadRunSet at loaded
  split at loaded
  · contradiction
  · cases decoded : files.mapM CheckedRun.openBytes with
    | error => rw [decoded] at loaded; contradiction
    | ok runs =>
      rw [decoded] at loaded
      change (match PackedTable.restore runs header.committed header.floor with
        | none => Except.error _
        | some restored => Except.ok restored) = Except.ok table at loaded
      split at loaded
      · contradiction
      · rename_i restored restoredEq
        cases loaded
        exact (PackedTable.restore_spec restoredEq).2.2.2.2

/-- The exact manifest and runs prepared from a refined table can reopen with
its entire committed WAL still present. Every selected frame is validated, but
the full checkpoint watermark leaves nothing to replay. Old snapshot pins
are cleared, and freshly acquired pins read the original model. -/
theorem reopenFullWatermarkCheckpoint_refines
    {before checkpoint : PackedTable} {model : SnapshotTable UInt64}
    (prepared : (flushForCheckpoint before id : Except String PackedTable) = .ok checkpoint)
    (refines : before.Refines model) (fits : checkpoint.runs.length < UInt64.size)
    (runBound : ∀ run ∈ before.runs, ∀ row ∈ run.history.rows, row.sequence ≤ before.committed)
    (memoryBound : ∀ row ∈ before.memory.rows, row.sequence ≤ before.committed)
    (generation : UInt64) (history : List WAL.Write) (tail : ByteArray)
    (ordered : WAL.OrdinalsFrom 1 history) (watermark : history.length = before.committed.toNat)
    (walFits : (WAL.encode history).size < UInt64.size) :
    let header := checkpointHeader checkpoint generation
    let wal := WAL.encode history
    ∃ reopened, (do
        let decoded ← Manifest.decode (Manifest.encode header)
        loadRunSet decoded (checkpoint.runs.map fun run : CheckedRun => run.run.bytes)) = .ok reopened ∧
      (do
        let count ← WAL.Boundary.decode (WAL.Boundary.encode wal.size.toUInt64)
        WAL.Boundary.recoverMarked reopened count (wal ++ tail)) = .ok (wal, reopened) ∧
      reopened.SameData checkpoint ∧ reopened.pins.active = [] ∧
      reopened.committed = model.committed ∧ reopened.pins.floor = model.pins.floor ∧
      ∀ snapshot : UInt64, model.pins.floor ≤ snapshot → snapshot ≤ model.committed →
        ∃ pin pinned, reopened.acquireAt snapshot = some (pin, pinned) ∧
          (∀ key, pinned.lookup pin.handle key = some (model.table.lookup key snapshot)) ∧
          (∀ start stop, pinned.range pin.handle start stop =
            some (model.table.range start stop snapshot)) := by
  dsimp only
  obtain ⟨written, committed, relation⟩ :=
    CheckpointForRecovery.of_flushForCheckpoint prepared refines fits runBound memoryBound generation
  obtain ⟨reopened, loaded, same⟩ := written.loads
  have floor : checkpoint.pins.floor = model.pins.floor := by
    rw [relation.pins]
    split <;> rfl
  have validFloor : (checkpointHeader checkpoint generation).floor ≤
      (checkpointHeader checkpoint generation).committed := by
    change checkpoint.pins.floor ≤ checkpoint.committed
    rw [floor, committed, refines.committed]
    exact model.floor_committed
  change (do
    let decoded ← Manifest.decode (Manifest.encode (checkpointHeader checkpoint generation))
    loadRunSet decoded (checkpoint.runs.map fun run : CheckedRun => run.run.bytes)) = .ok reopened at loaded
  have loadedRuns := loaded
  rw [Manifest.decode_encode _ validFloor] at loadedRuns
  change loadRunSet (checkpointHeader checkpoint generation) (checkpoint.runs.map (·.run.bytes)) =
    .ok reopened at loadedRuns
  have skip : recoverSelected reopened (WAL.encode history) = .ok reopened := by
    have count : history.length = reopened.committed.toNat := by
      simpa only [same.committed, committed] using watermark
    change recoverSelected reopened (WAL.encode history) = replay reopened []
    simpa only [List.append_nil] using
      recoverSelected_encoded reopened history [] (by simpa only [List.append_nil] using ordered) count
  refine ⟨reopened, loaded, ?_, same, loadRunSet_clearsPins loadedRuns,
    same.committed.trans (committed.trans refines.committed), same.floor.trans floor, ?_⟩
  · rw [WAL.Boundary.decode_encode]
    change WAL.Boundary.recoverMarked reopened (WAL.encode history).size.toUInt64
      (WAL.encode history ++ tail) = .ok (WAL.encode history, reopened)
    unfold WAL.Boundary.recoverMarked
    rw [WAL.Boundary.select_encoded history tail walFits]
    change (do
      let result ← recoverSelected reopened (WAL.encode history)
      pure (WAL.encode history, result)) = .ok (WAL.encode history, reopened)
    rw [skip]
    rfl
  · intro snapshot retained supported
    have checkpointFloor : checkpoint.pins.floor ≤ snapshot := floor ▸ retained
    have checkpointCommit : snapshot ≤ checkpoint.committed :=
      (committed.trans refines.committed) ▸ supported
    obtain ⟨pin, pinned, acquired, lookup, range⟩ := same.acquireAt_reads checkpointFloor checkpointCommit
    refine ⟨pin, pinned, acquired, ?_, ?_⟩
    · intro key
      rw [lookup, relation.table]
      split
      · rfl
      · rw [SnapshotTable.flush, Sequential.Table.flush_lookup]
    · intro start stop
      rw [range, relation.table]
      split
      · rfl
      · rw [SnapshotTable.flush, Sequential.Table.flush_range]

end Alvoki.Storage
