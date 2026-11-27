import Alvoki.Storage.Disk.Proofs.Recovery.CachedOpenRejection

namespace Alvoki.Storage.DiskSession

open System Manifest WalSegmentRepair

/-- The read-only manifest callback supplies the exact visible bytes
and the decoded checkpoint that selects the run addresses. -/
structure CachedOpenAttempt.CheckpointManifestRead {directory : DiskDirectory} {before : LockedFileState FileImage}
    (attempt : CachedOpenAttempt directory before) where
  manifestBytes : ByteArray
  visibleManifest : before.image.directory.active.manifest = some manifestBytes
  manifestRead : attempt.readOptional (directory.file .manifest) before.image = .ok (some manifestBytes) before.image
  manifest : IntegrityCheckpoint
  decoded : IntegrityCheckpoint.decode manifestBytes = .ok manifest

/-- Every reported run size and prefix read up to the specified index
returned successfully without changing the file image. -/
def CachedOpenAttempt.CheckpointManifestRead.RunReads {directory : DiskDirectory} {before : LockedFileState FileImage}
    {attempt : CachedOpenAttempt directory before} (read : attempt.CheckpointManifestRead)
    (stop : Nat) (payload : Nat → ByteArray) : Prop :=
  ∀ index < stop, ∃ stamp,
    read.manifest.runs[index]? = some stamp ∧ stamp.byteCount.toNat < USize.size ∧
    (payload index).size = stamp.byteCount.toNat ∧
    attempt.readRunSize (directory.file (.run read.manifest.header.generation index)) before.image =
      .ok stamp.byteCount.toNat before.image ∧
    attempt.readRunPrefix (directory.file (.run read.manifest.header.generation index))
      stamp.byteCount.toNat before.image = .ok (payload index) before.image

/-- The first rejected run extent follows the earlier admitted payloads. -/
structure CachedOpenAttempt.CheckpointExtentReads {directory : DiskDirectory} {before : LockedFileState FileImage}
    (attempt : CachedOpenAttempt directory before) extends CachedOpenAttempt.CheckpointManifestRead attempt where
  index : Nat
  within : index < manifest.header.runCount.toNat
  stamp : RunIntegrity
  stampAt : manifest.runs[index]? = some stamp
  payload : Nat → ByteArray
  earlier : toCheckpointManifestRead.RunReads index payload
  actual : Nat
  measured : attempt.readRunSize (directory.file (.run manifest.header.generation index)) before.image =
    .ok actual before.image
  invalid : ¬ (actual = stamp.byteCount.toNat ∧ stamp.byteCount.toNat < USize.size)

private def CachedOpenRejection.ofSizedCheckpointFailure {directory : DiskDirectory} {before : LockedFileState FileImage}
    (attempt : CachedOpenAttempt directory before) {cause : IO.Error}
    (rejected : readIntegrityCheckpointSized directory (attempt.readOptional (directory.file .manifest))
      attempt.readRunSize attempt.readRunPrefix before.image = .error cause before.image) :
    CachedOpenRejection directory before := by
  refine ⟨attempt, cause, ?_⟩
  simp only [CachedOpenAttempt.prepare, prepareBoundedMarkedFromReaders, Bind.bind, EStateM.bind, rejected]

/-- A wrong selected run extent stops preparation after the observed size
request. The same rejection edge handles local unlock and later retries. -/
def CachedOpenRejection.ofCheckpointRunExtent {directory : DiskDirectory} {before : LockedFileState FileImage}
    {attempt : CachedOpenAttempt directory before} (reads : attempt.CheckpointExtentReads) :
    CachedOpenRejection directory before := by
  have earlier := readIntegrityRunBytesSized_prefix_of_reports directory reads.manifest attempt.readRunSize
    attempt.readRunPrefix before.image reads.index (Nat.lt_trans reads.within reads.manifest.header.runCount.toNat_lt_size)
    reads.payload reads.earlier
  have rejected := readIntegrityCheckpointSized_rejectsExtent directory (attempt.readOptional (directory.file .manifest))
    attempt.readRunSize attempt.readRunPrefix reads.manifestRead reads.decoded reads.within reads.stampAt earlier
    reads.measured reads.invalid
  exact ofSizedCheckpointFailure attempt rejected

/-- Even when every selected extent and payload read succeeds, a digest
that differs from its recorded value stops recovery before table restore
or WAL reads. -/
def CachedOpenRejection.ofCheckpointRunDigest {directory : DiskDirectory} {before : LockedFileState FileImage}
    {attempt : CachedOpenAttempt directory before} (read : attempt.CheckpointManifestRead) (payload : Nat → ByteArray)
    (reported : read.RunReads read.manifest.header.runCount.toNat payload)
    {index : Nat} {stamp : RunIntegrity} (within : index < read.manifest.header.runCount.toNat)
    (stampAt : read.manifest.runs[index]? = some stamp) (digest : checksumRun (payload index) ≠ stamp.checksum) :
    CachedOpenRejection directory before := by
  let files := (List.range read.manifest.header.runCount.toNat).map payload
  have readRuns : readIntegrityRunBytesSized directory read.manifest attempt.readRunSize
      attempt.readRunPrefix before.image = .ok files before.image := by
    simpa [files] using readIntegrityRunBytesSized_prefix_of_reports directory read.manifest attempt.readRunSize
      attempt.readRunPrefix before.image read.manifest.header.runCount.toNat
      read.manifest.header.runCount.toNat_lt_size payload reported
  have atIndex : files[index]? = some (payload index) := by
    simp [files, List.getElem?_map, List.getElem?_range within]
  have rejected := IntegrityCheckpoint.rejects_run stampAt atIndex (.inr digest)
  have loadFailed : loadIntegrityRunSet read.manifest files = .error checkpointIntegrityMismatch := by
    simp [loadIntegrityRunSet, rejected]
  refine ofSizedCheckpointFailure attempt (cause := IO.userError checkpointIntegrityMismatch) ?_
  simp [readIntegrityCheckpointSized, read.manifestRead, read.decoded, readRuns, loadFailed, Bind.bind, EStateM.bind,
    liftExcept, Except.mapError, Pure.pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

end Alvoki.Storage.DiskSession
