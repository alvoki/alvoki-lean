import Alvoki.Storage.Disk.SizedCheckpointOpenFailure

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- Callbacks for the marked cached worker after observed lock acquisition. -/
structure CachedOpenAttempt (directory : DiskDirectory) (before : LockedFileState FileImage) where
  descriptor : Nat
  nextRef : Nat
  acquisition : TryLockObserves before.owners directory (.ok true)
  unlock : UnlockReport
  localUnlock : unlock.LocalFlock
  readOptional : FilePath → EStateM IO.Error FileImage (Option ByteArray)
  readRunSize : FilePath → EStateM IO.Error FileImage Nat
  readRunPrefix : FilePath → Nat → EStateM IO.Error FileImage ByteArray
  list : FilePath → EStateM IO.Error FileImage (Array IO.FS.DirEntry)
  lstat : FilePath → EStateM IO.Error FileImage (Except IO.Error IO.FS.Metadata)
  readSeal : FilePath → Nat → EStateM IO.Error FileImage ByteArray
  readKeeper : FilePath → Nat → Nat → EStateM IO.Error FileImage ByteArray
  removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit)
  write : FilePath → ByteArray → EStateM IO.Error FileImage Unit
  sync : Array FilePath → EStateM IO.Error FileImage Unit
  renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit

namespace CachedOpenAttempt

variable {directory : DiskDirectory} {before : LockedFileState FileImage}

def prepare (attempt : CachedOpenAttempt directory before) :
    EStateM IO.Error FileImage (Plan × Reopened × Nat) :=
  prepareBoundedMarkedFromReaders directory
    (readIntegrityCheckpointSized directory (attempt.readOptional (directory.file .manifest))
      attempt.readRunSize attempt.readRunPrefix) attempt.readOptional
    (fun watermark length => readSelectedWithCachedExtents directory watermark length
      attempt.list attempt.lstat attempt.readSeal attempt.readKeeper)

def recover (attempt : CachedOpenAttempt directory before) : EStateM IO.Error FileImage Reopened :=
  reopenMarkedBoundedWithCachedExtents directory attempt.readOptional attempt.readRunSize attempt.readRunPrefix
    attempt.list attempt.lstat attempt.readSeal attempt.readKeeper attempt.removeFile attempt.write attempt.sync
    attempt.renameFile

def run (attempt : CachedOpenAttempt directory before) :
    EStateM.Result IO.Error (LockedFileState FileImage) SegmentedSession :=
  runOpenWithInstallation directory attempt.descriptor attempt.nextRef (.ok true) attempt.unlock attempt.recover before

end CachedOpenAttempt

/-- A read-only preparation error certifies that the cached worker never
started repair. Cleanup may still change ownership of the selected lock. -/
structure CachedOpenRejection (directory : DiskDirectory) (before : LockedFileState FileImage) where
  attempt : CachedOpenAttempt directory before
  cause : IO.Error
  rejected : attempt.prepare before.image = .error cause before.image

namespace CachedOpenRejection

variable {directory : DiskDirectory} {before : LockedFileState FileImage}

def after (rejection : CachedOpenRejection directory before) : LockedFileState FileImage :=
  let owner := match rejection.attempt.unlock with
    | .success => none
    | .failure _ _ => some rejection.attempt.descriptor
  { before with owners := before.owners.set (directory.file .lock) owner }

def error (rejection : CachedOpenRejection directory before) : IO.Error :=
  match rejection.attempt.unlock with
  | .success => rejection.cause
  | .failure cleanup _ => cleanup

/-- Preparation failure stops the actual cached run before repair and
installation. The local cleanup report determines the error and owner. -/
theorem run_error (rejection : CachedOpenRejection directory before) :
    rejection.attempt.run = .error rejection.error rejection.after := by
  have failed : rejection.attempt.recover before.image = .error rejection.cause before.image := by
    unfold CachedOpenAttempt.recover reopenMarkedBoundedWithCachedExtents
    change (rejection.attempt.prepare >>= _) before.image = _
    simp only [Bind.bind, EStateM.bind, rejection.rejected]
  unfold CachedOpenAttempt.run
  rw [runOpenWithInstallation_acquiredRecoveryError _ _ _ _ _ _ failed]
  cases observed : rejection.attempt.unlock with
  | success => simp [after, error, observed]
  | failure cleanup released =>
    have retained : released = false := by
      simpa [UnlockReport.LocalFlock, observed] using rejection.attempt.localUnlock
    simp [after, error, observed, retained]

/-- Successful local cleanup permits the next opener to acquire immediately. -/
theorem immediateReacquire (rejection : CachedOpenRejection directory before) :
    TryLockObserves rejection.after.owners directory (.ok true) ↔ rejection.attempt.unlock = .success := by
  cases observed : rejection.attempt.unlock <;> simp [TryLockObserves, after, observed, LockOwners.set]

end CachedOpenRejection

end Alvoki.Storage.DiskSession
