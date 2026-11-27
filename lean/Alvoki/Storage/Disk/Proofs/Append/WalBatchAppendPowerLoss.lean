import Alvoki.Storage.Disk.WalBatchCommitEffects
import Alvoki.Storage.Disk.Proofs.Append.WalSegmentAppendPowerLoss

namespace Alvoki.Storage.DiskSession.FirstAppendCut

open System WAL.Boundary WalSegmentCommit WalSegmentRepair

/-- Stop the shared batch schedule at its first callback, recording the
requested path and payload in the interpreter's stop tag. Power loss
supplies the cut's tail observations without a returned write error. -/
theorem interruptsBatch (cut : FirstAppendCut) (directory : DiskDirectory) (first newBytes : Nat)
    (history batch : List WAL.Write) (scratch : Option (ByteArray × Bool))
    (stage : FilePath → ByteArray → EStateM (FilePath × ByteArray) WriteFiles Unit)
    (sync : Array FilePath → EStateM (FilePath × ByteArray) WriteFiles Unit)
    (rename : FilePath → FilePath → EStateM (FilePath × ByteArray) WriteFiles Unit) :
    commitBytesAt directory first (WAL.encodeBatch batch) newBytes
      (fun path bytes _ => .error (path, bytes) (cut.writeFiles history scratch))
      stage sync rename (WriteFiles.initial history scratch) =
    .error (directory.file (.walSegment first), WAL.encodeBatch batch)
      (writeFilesAfter (runBatchEffects history batch cut.writeEffects scratch)) := rfl

/-- A crash during the batch append starts retries with exactly the prior
checkpoint binding and marked keeper prefix. Every observed surviving tail lies
outside the old marker, including a full or partial copy of the batch. -/
theorem batchPowerLoss (cut : FirstAppendCut) {directory descriptor before}
    (ready : before.RetainedReady directory descriptor) (batch : List WAL.Write)
    {tail : ByteArray} (survives : tail ∈ ByteArray.empty :: cut.crashTails) :
    let crashed := cut.crashed before directory tail
    BoundedReopenTrace directory (fun target => target = before.target)
      ⟨cut.physical before, before.owners⟩ crashed ∧
    BatchRetryTarget before.history batch before.wal.active.first before.target ∧
    crashed.image.directory = .settled before.target.pair ∧ crashed.image.kept = before.files.kept ∧
    crashed.image.later.DurablyEmpty ∧
    crashed.image.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode before.history).size.toUInt64) ∧
    let bytes := WAL.encode (before.history.drop before.wal.active.first) ++ tail
    crashed.image.keeper.active = some bytes ∧
    selectRetained before.installed.activeFirst (WAL.encode before.history).size.toUInt64 bytes =
      .ok before.wal.active.bytes := by
  intro crashed
  obtain ⟨marker, selected⟩ := ready.selectPriorKeeper tail
  have old : BatchRetryTarget before.history batch before.wal.active.first before.target := by
    refine ⟨ready.active, before.history, .inl rfl, marker, ready.resumed.through, ?_⟩
    rw [ready.resumed.contents, ready.active]
  exact ⟨cut.powersOff ready _ survives, old, rfl, rfl, ⟨rfl, rfl⟩, marker, rfl, selected⟩

end Alvoki.Storage.DiskSession.FirstAppendCut
