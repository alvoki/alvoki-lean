import Alvoki.Storage.Disk.Proofs.Recovery.BoundedOpenReadFailure
import Alvoki.Storage.Disk.WalSegmentOpenFastEffects

namespace Alvoki.Storage.WalSegmentRepair

open System

/-- The bounded finish uses the same file effects and keeps the same exact
post-effect image on failure. The witness supplies the observed physical
size separately from the byte prefix passed to the bounded worker. -/
theorem finishBoundedMarkedOpen_safe {initial : FileImage} {target : Target} {full : Plan}
    (prepared : Prepared initial target full) (directory : DiskDirectory)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit)
    (metadata : MetadataReport initial (sync #[directory.path]))
    (effects : EffectReports target initial.syncDirectory full.finishActions
      (performPaths directory full removeFile throw write sync renameFile)) :
    match finishBoundedMarkedOpen directory { full with keeperBytes := full.keeperBytes.extract 0 full.keeperSize }
        full.keeperBytes.size removeFile write sync renameFile initial with
    | .ok _ after => EffectTrace target initial after ∧ after.Ready target
    | .error _ after => after = initial ∨ EffectTrace target initial after := by
  rw [finishBoundedMarkedOpen_eq_full directory full prepared.valid]
  exact finishMarkedOpen_safe prepared directory removeFile write sync renameFile metadata effects

end Alvoki.Storage.WalSegmentRepair

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- Interpret the actual bounded worker under the native lock schedule.
A failed read-only preparation preserves the input image, and an accepted
preparation only needs a matching full keeper witness for the repair effects.
Cleanup uses the exact image left by recovery and keeps the lock outcome
separate from the original recovery error. -/
theorem runOpenWithImage_boundedSegmented
    (directory : DiskDirectory) (descriptor : Nat) (before : LockedFileState FileImage) (target : Target)
    (acquired : Except IO.Error Bool) (acquisition : TryLockObserves before.owners directory acquired)
    (unlock : UnlockReport)
    (readOptional : FilePath → Except IO.Error (Option ByteArray))
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → Except IO.Error ByteArray)
    (readPrefix : FilePath → Nat → Except IO.Error KeeperPrefix)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit) :
    let prepare := prepareBoundedMarkedWith directory readOptional list lstat readBin readPrefix
    let recover := reopenMarkedBoundedWith directory (fun path => liftExcept (readOptional path))
      (fun path => liftExcept (list path)) (fun path => liftExcept (lstat path)) (fun path => liftExcept (readBin path))
      (fun path count => liftExcept (readPrefix path count)) removeFile write sync renameFile
    (acquired = .ok true → match prepare with
      | .error _ => True
      | .ok (bounded, _, physicalSize) =>
        ∃ full, Prepared before.image target full ∧
          bounded = { full with keeperBytes := full.keeperBytes.extract 0 full.keeperSize } ∧
          physicalSize = full.keeperBytes.size ∧ MetadataReport before.image (sync #[directory.path]) ∧
          EffectReports target before.image.syncDirectory full.finishActions
            (performPaths directory full removeFile throw write sync renameFile)) →
    match runOpenWithImage directory descriptor acquired unlock recover before with
    | .ok reopened after =>
      acquired = .ok true ∧ before.owners (directory.file .lock) = none ∧
        after.owners = before.owners.set (directory.file .lock) (some descriptor) ∧
        (∃ bounded physicalSize, prepare = .ok (bounded, reopened, physicalSize)) ∧
        EffectTrace target before.image after.image ∧ after.image.Ready target
    | .error error after =>
      (acquired ≠ .ok true ∧ after = before) ∨
      (acquired = .ok true ∧ before.owners (directory.file .lock) = none ∧
        (after.image = before.image ∨ EffectTrace target before.image after.image) ∧
        ∃ recoveryError, recover before.image = .error recoveryError after.image ∧
          match unlock with
          | .success => error = recoveryError ∧ after.owners = before.owners.set (directory.file .lock) none
          | .failure cleanup released => error = cleanup ∧
            after.owners = before.owners.set (directory.file .lock) (if released then none else some descriptor)) := by
  intro prepare recover reported
  by_cases held : acquired = .ok true
  · subst acquired
    have free := acquisition rfl
    have observations := reported rfl
    clear reported
    have safety : match recover before.image with
      | .ok reopened after =>
        (∃ bounded physicalSize, prepare = .ok (bounded, reopened, physicalSize)) ∧
          EffectTrace target before.image after ∧ after.Ready target
      | .error _ after => after = before.image ∨ EffectTrace target before.image after := by
      revert observations
      have route := reopenMarkedBoundedWith_readOutcome directory readOptional list lstat readBin readPrefix
        removeFile write sync renameFile before.image
      change recover before.image = _ at route
      rw [route]
      cases read : prepare with
      | error error =>
        intro _
        have failed : prepareBoundedMarkedWith directory readOptional list lstat readBin readPrefix = .error error := read
        rw [failed]
        exact Or.inl rfl
      | ok result =>
        obtain ⟨bounded, reopened, physicalSize⟩ := result
        have accepted : prepareBoundedMarkedWith directory readOptional list lstat readBin readPrefix =
          .ok (bounded, reopened, physicalSize) := read
        rw [accepted]
        intro observations
        obtain ⟨full, prepared, rfl, rfl, metadata, effects⟩ := observations
        have safe := finishBoundedMarkedOpen_safe prepared directory removeFile write sync renameFile metadata effects
        dsimp only
        cases result : finishBoundedMarkedOpen directory
          { full with keeperBytes := full.keeperBytes.extract 0 full.keeperSize }
          full.keeperBytes.size removeFile write sync renameFile before.image with
        | ok _ after => exact ⟨⟨_, _, rfl⟩, by simpa only [result] using safe⟩
        | error _ after => simpa only [result] using safe
    rw [runOpenWithImage_acquired]
    cases outcome : recover before.image with
    | ok reopened after =>
      rw [outcome] at safety
      exact ⟨rfl, free, rfl, safety⟩
    | error error after =>
      rw [outcome] at safety
      cases unlock <;> exact Or.inr ⟨rfl, free, safety, error, rfl, rfl, rfl⟩
  · obtain ⟨error, denied⟩ :=
      runOpenWithImage_notAcquired directory descriptor acquired unlock recover before held
    rw [denied]
    exact Or.inl ⟨held, rfl⟩

end Alvoki.Storage.DiskSession
