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

/-- The recovery error and the reached file image go to the local unlock.
A failed unlock returns its own error and retains the acquired owner. -/
def cleanupError (attempt : CachedOpenAttempt directory before) (cause : IO.Error) (reached : FileImage) :
    IO.Error × LockedFileState FileImage :=
  let (error, owner) := match attempt.unlock with
    | .success => (cause, none)
    | .failure cleanup _ => (cleanup, some attempt.descriptor)
  (error, ⟨reached, before.owners.set (directory.file .lock) owner⟩)

theorem cleanupError_keepsFiles (attempt : CachedOpenAttempt directory before)
    (cause : IO.Error) (reached : FileImage) :
    (attempt.cleanupError cause reached).2.image = reached := by
  cases report : attempt.unlock <;> simp [cleanupError, report]

theorem run_error (attempt : CachedOpenAttempt directory before) {cause : IO.Error} {reached : FileImage}
    (failed : attempt.recover before.image = .error cause reached) :
    attempt.run = .error (attempt.cleanupError cause reached).1 (attempt.cleanupError cause reached).2 := by
  unfold CachedOpenAttempt.run
  rw [runOpenWithInstallation_acquiredRecoveryError _ _ _ _ _ _ failed]
  cases observed : attempt.unlock with
  | success => simp [cleanupError, observed]
  | failure cleanup released =>
    have retained : released = false := by
      simpa [UnlockReport.LocalFlock, observed] using attempt.localUnlock
    simp [cleanupError, observed, retained]

/-- Acquire again immediately when local cleanup succeeds. An unlock
error leaves the original open description responsible for the lock. -/
theorem immediateReacquire (attempt : CachedOpenAttempt directory before) (cause : IO.Error) (reached : FileImage) :
    TryLockObserves (attempt.cleanupError cause reached).2.owners directory (.ok true) ↔ attempt.unlock = .success := by
  cases observed : attempt.unlock <;> simp [TryLockObserves, cleanupError, observed, LockOwners.set]

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
  (rejection.attempt.cleanupError rejection.cause before.image).2

def error (rejection : CachedOpenRejection directory before) : IO.Error :=
  (rejection.attempt.cleanupError rejection.cause before.image).1

/-- Preparation failure stops the actual cached run before repair and
installation. The local cleanup report determines the error and owner. -/
theorem run_error (rejection : CachedOpenRejection directory before) :
    rejection.attempt.run = .error rejection.error rejection.after := by
  have failed : rejection.attempt.recover before.image = .error rejection.cause before.image := by
    unfold CachedOpenAttempt.recover reopenMarkedBoundedWithCachedExtents
    change (rejection.attempt.prepare >>= _) before.image = _
    simp only [Bind.bind, EStateM.bind, rejection.rejected]
  exact rejection.attempt.run_error failed

/-- Successful local cleanup permits the next opener to acquire immediately. -/
theorem immediateReacquire (rejection : CachedOpenRejection directory before) :
    TryLockObserves rejection.after.owners directory (.ok true) ↔ rejection.attempt.unlock = .success :=
  rejection.attempt.immediateReacquire rejection.cause before.image

end CachedOpenRejection

/-- An acquired cached marked open has prepared a valid bounded layout,
but its first directory sync reports an error. The reached image records
whether directory settlement took effect. No later repair was attempted. -/
structure CachedOpenAuthorizationFailure (directory : DiskDirectory) (before : LockedFileState FileImage) where
  attempt : CachedOpenAttempt directory before
  target : Target
  full : Plan
  opened : Reopened
  prepared : Prepared before.image target full
  preparedRead : attempt.prepare before.image =
    .ok ({ full with keeperBytes := full.keeperBytes.extract 0 full.keeperSize }, opened, full.keeperBytes.size) before.image
  cause : IO.Error
  reached : FileImage
  failed : attempt.sync #[directory.path] before.image = .error cause reached
  metadata : MetadataReport before.image (attempt.sync #[directory.path])

namespace CachedOpenAuthorizationFailure

variable {directory : DiskDirectory} {before : LockedFileState FileImage}

def after (failure : CachedOpenAuthorizationFailure directory before) : LockedFileState FileImage :=
  (failure.attempt.cleanupError failure.cause failure.reached).2

def error (failure : CachedOpenAuthorizationFailure directory before) : IO.Error :=
  (failure.attempt.cleanupError failure.cause failure.reached).1

theorem run_error (failure : CachedOpenAuthorizationFailure directory before) :
    failure.attempt.run = .error failure.error failure.after := by
  apply failure.attempt.run_error
  have stopped := finishBoundedMarkedOpen_authorizationError directory failure.full failure.prepared.valid
    failure.attempt.removeFile failure.attempt.write failure.attempt.sync failure.attempt.renameFile failure.failed
  change (failure.attempt.prepare >>= _) before.image = _
  simp only [Bind.bind, EStateM.bind, failure.preparedRead, stopped]

theorem imageOutcome (failure : CachedOpenAuthorizationFailure directory before) :
    failure.after.image = before.image ∨ failure.after.image = before.image.syncDirectory := by
  have metadata := failure.metadata
  unfold MetadataReport at metadata
  rw [failure.failed] at metadata
  simpa only [after, CachedOpenAttempt.cleanupError_keepsFiles] using metadata

theorem errorFiles (failure : CachedOpenAuthorizationFailure directory before) {admits : Target → Prop}
    (admitted : admits failure.target) :
    failure.after.image = before.image ∨ ∃ target plan, admits target ∧ Prepared before.image target plan ∧
      EffectTrace target before.image failure.after.image := by
  rcases failure.imageOutcome with unchanged | settled
  · exact .inl unchanged
  · exact .inr ⟨failure.target, failure.full, admitted, failure.prepared, settled.symm ▸ .authorized⟩

theorem immediateReacquire (failure : CachedOpenAuthorizationFailure directory before) :
    TryLockObserves failure.after.owners directory (.ok true) ↔ failure.attempt.unlock = .success :=
  failure.attempt.immediateReacquire failure.cause failure.reached

end CachedOpenAuthorizationFailure

end Alvoki.Storage.DiskSession
