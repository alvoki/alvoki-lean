import Alvoki.Storage.Disk.Proofs.WAL.WalBatchCommitEffects

namespace Alvoki.Storage.DiskSession

open System WalSegmentCommit WAL.Boundary

/-- Primitive reports from the reached callbacks for a batch publication.
The writer keeps the original I/O error. Only effect accounting erases it. -/
structure BatchCommitReports (directory : DiskDirectory) (first : Nat) (before batch : List WAL.Write)
    (newBytes : Nat) (effects : WriteEffects) (scratch : Option (ByteArray × Bool))
    (append stage : FilePath → ByteArray → EStateM IO.Error WriteFiles Unit)
    (sync : Array FilePath → EStateM IO.Error WriteFiles Unit)
    (rename : FilePath → FilePath → EStateM IO.Error WriteFiles Unit) : Prop where
  appended : forgetError (append (directory.file (.walSegment first)) (WAL.encodeBatch batch))
      (WriteFiles.initial before scratch) = appendBatch effects batch (WriteFiles.initial before scratch)
  marker : ∀ appended, appendBatch effects batch (WriteFiles.initial before scratch) = .ok () appended →
    ∀ prior action remaining state, Publication.steps = prior ++ action :: remaining →
    (prior.forM (effects.markerStep (WAL.Boundary.encode newBytes.toUInt64))) appended = .ok () state →
    forgetError (performMarkerAt directory first newBytes stage sync rename action) state =
      effects.markerStep (WAL.Boundary.encode newBytes.toUInt64) action state

theorem BatchCommitReports.run {directory first before batch newBytes effects scratch append stage sync rename}
    (reports : BatchCommitReports directory first before batch newBytes effects scratch append stage sync rename)
    (count : newBytes = (WAL.encode (before ++ batch)).size) :
    forgetError (commitBytesAt directory first (WAL.encodeBatch batch) newBytes append stage sync rename)
      (WriteFiles.initial before scratch) = runBatchEffects before batch effects scratch := by
  rw [forgetError_commitBytesAt]
  apply batch_reports directory first before batch newBytes count effects scratch _ _ _ _ reports.appended
  intro appended added prior action remaining state schedule reached
  have agree := reports.marker appended added prior action remaining state schedule reached
  cases action <;> exact agree

theorem BatchCommitReports.cut_eq_of_error
    {directory first before batch newBytes effects scratch append stage sync rename}
    (reports : BatchCommitReports directory first before batch newBytes effects scratch append stage sync rename)
    (count : newBytes = (WAL.encode (before ++ batch)).size)
    {cause : IO.Error} {files : WriteFiles}
    (failed : commitBytesAt directory first (WAL.encodeBatch batch) newBytes append stage sync rename
      (WriteFiles.initial before scratch) = .error cause files) :
    writeFilesAfter (runBatchEffects before batch effects scratch) = files := by
  rw [← reports.run count, forgetError, failed]
  rfl

/-- The actual successful callbacks settle the marker for the complete batch. -/
theorem BatchCommitReports.settled_of_success
    {directory first before batch newBytes effects scratch append stage sync rename}
    (reports : BatchCommitReports directory first before batch newBytes effects scratch append stage sync rename)
    (count : newBytes = (WAL.encode (before ++ batch)).size) (starts : first ≤ before.length)
    {files : WriteFiles}
    (ran : commitBytesAt directory first (WAL.encodeBatch batch) newBytes append stage sync rename
      (WriteFiles.initial before scratch) = .ok () files) (manifest : Option ByteArray) :
    let after := files.reopenSegment first before manifest
    after.directory.active =
        ⟨manifest, some (WAL.Boundary.encode (WAL.encode (before ++ batch)).size.toUInt64)⟩ ∧
      after.directory.crashImages = [after.directory.active] ∧
      after.wal.active = some (WAL.encode ((before ++ batch).drop first)) ∧
      after.wal.crashImages = [after.wal.active] := by
  have modeled := reports.run count
  rw [forgetError, ran] at modeled
  exact settledSegment_ofBatchSuccess starts modeled.symm manifest

end Alvoki.Storage.DiskSession
