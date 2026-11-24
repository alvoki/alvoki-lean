import Alvoki.Storage.Disk.CachedOpenRejection

namespace Alvoki.Storage.DiskSession

open System Manifest WalSegmentRepair

/-- The held manifest selects the run addresses. The earlier size and
payload callbacks and the failed run's size observation are read-only. -/
structure CachedOpenAttempt.CheckpointExtentReads {directory : DiskDirectory} {before : LockedFileState FileImage}
    (attempt : CachedOpenAttempt directory before) where
  manifestBytes : ByteArray
  visibleManifest : before.image.directory.active.manifest = some manifestBytes
  manifestRead : attempt.readOptional (directory.file .manifest) before.image = .ok (some manifestBytes) before.image
  manifest : IntegrityCheckpoint
  decoded : IntegrityCheckpoint.decode manifestBytes = .ok manifest
  index : Nat
  within : index < manifest.header.runCount.toNat
  stamp : RunIntegrity
  stampAt : manifest.runs[index]? = some stamp
  payload : Nat → ByteArray
  earlier : ∀ previous < index, ∃ expected,
    manifest.runs[previous]? = some expected ∧ expected.byteCount.toNat < USize.size ∧
    (payload previous).size = expected.byteCount.toNat ∧
    attempt.readRunSize (directory.file (.run manifest.header.generation previous)) before.image =
      .ok expected.byteCount.toNat before.image ∧
    attempt.readRunPrefix (directory.file (.run manifest.header.generation previous))
      expected.byteCount.toNat before.image = .ok (payload previous) before.image
  actual : Nat
  measured : attempt.readRunSize (directory.file (.run manifest.header.generation index)) before.image =
    .ok actual before.image
  invalid : ¬ (actual = stamp.byteCount.toNat ∧ stamp.byteCount.toNat < USize.size)

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
  refine ⟨attempt, IO.userError checkpointIntegrityMismatch, ?_⟩
  simp only [CachedOpenAttempt.prepare, prepareBoundedMarkedFromReaders, Bind.bind, EStateM.bind, rejected]

end Alvoki.Storage.DiskSession
