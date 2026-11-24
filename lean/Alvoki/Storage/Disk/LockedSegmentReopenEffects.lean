import Alvoki.Storage.Disk.DiskLockLifecycle
import Alvoki.Storage.Disk.WalSegmentOpenFastEffects

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- Interpret the marked segmented route under the shared native lock
schedule. The reports describe the same owned directory and stable file
identities while the lock is held. Read-only preparation leaves the file
image intact. After preparation, the repair reports apply only to the
reached actions of the selected route. -/
theorem runOpenWithImage_segmented
    (directory : DiskDirectory) (descriptor : Nat) (before : LockedFileState FileImage) (target : Target)
    (acquired : Except IO.Error Bool) (acquisition : TryLockObserves before.owners directory acquired)
    (unlock : UnlockReport) (localUnlock : unlock.LocalFlock)
    (readOptional : FilePath → EStateM IO.Error FileImage (Option ByteArray))
    (list : FilePath → EStateM IO.Error FileImage (Array IO.FS.DirEntry))
    (lstat : FilePath → EStateM IO.Error FileImage (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → EStateM IO.Error FileImage ByteArray)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit) :
    let prepare := prepareMarkedWith directory readOptional list lstat readBin
    let recover := reopenMarkedFastWith directory readOptional list lstat readBin removeFile write sync renameFile
    (acquired = .ok true → match prepare before.image with
      | .error _ after => after = before.image
      | .ok (plan, _) after =>
        after = before.image ∧ Prepared before.image target plan ∧
        MetadataReport before.image (sync #[directory.path]) ∧
        EffectReports target before.image.syncDirectory plan.finishActions
          (performPaths directory plan removeFile throw write sync renameFile)) →
    match runOpenWithImage directory descriptor acquired unlock recover before with
    | .ok reopened after =>
      acquired = .ok true ∧ before.owners (directory.file .lock) = none ∧
        after.owners = before.owners.set (directory.file .lock) (some descriptor) ∧
        (∃ plan, prepare before.image = .ok (plan, reopened) before.image) ∧
        EffectTrace target before.image after.image ∧ after.image.Ready target
    | .error error after =>
      (acquired ≠ .ok true ∧ after = before) ∨
      (acquired = .ok true ∧ before.owners (directory.file .lock) = none ∧
        (after.image = before.image ∨ EffectTrace target before.image after.image) ∧
        ∃ recoveryError, recover before.image = .error recoveryError after.image ∧
          match unlock with
          | .success => error = recoveryError ∧ after.owners = before.owners.set (directory.file .lock) none
          | .failure cleanup _ => error = cleanup ∧
            after.owners = before.owners.set (directory.file .lock) (some descriptor)) := by
  intro prepare recover reported
  by_cases held : acquired = .ok true
  · subst acquired
    have free := acquisition rfl
    have observations := reported rfl
    have safety : match recover before.image with
      | .ok reopened after =>
        (∃ plan, prepare before.image = .ok (plan, reopened) before.image) ∧
          EffectTrace target before.image after ∧ after.Ready target
      | .error _ after => after = before.image ∨ EffectTrace target before.image after := by
      cases read : prepare before.image with
      | error cause after =>
        rw [read] at observations
        have fails : recover before.image = .error cause after := by
          change prepareMarkedWith directory readOptional list lstat readBin before.image = _ at read
          simp only [recover, reopenMarkedFastWith, Bind.bind, EStateM.bind, read]
        rw [fails]
        exact Or.inl observations
      | ok result after =>
        obtain ⟨plan, reopened⟩ := result
        rw [read] at observations
        obtain ⟨unchanged, prepared, metadata, effects⟩ := observations
        subst after
        have bridge := reopenMarkedFastWith_afterPreparation directory readOptional list lstat readBin
          removeFile write sync renameFile read
        rw [show recover before.image = _ from bridge]
        have safe := finishMarkedOpen_safe prepared directory removeFile write sync renameFile metadata effects
        cases finished : finishMarkedOpen directory plan removeFile write sync renameFile before.image with
        | ok _ image => exact ⟨⟨plan, rfl⟩, by simpa only [finished] using safe⟩
        | error _ image => simpa only [finished] using safe
    rw [runOpenWithImage_acquired]
    cases outcome : recover before.image with
    | ok reopened after =>
      rw [outcome] at safety
      exact ⟨rfl, free, rfl, safety⟩
    | error error after =>
      rw [outcome] at safety
      cases unlock with
      | success => exact Or.inr ⟨rfl, free, safety, error, rfl, rfl, rfl⟩
      | failure cleanup applied =>
        change applied = false at localUnlock
        subst applied
        exact Or.inr ⟨rfl, free, safety, error, rfl, rfl, rfl⟩
  · obtain ⟨error, denied⟩ :=
      runOpenWithImage_notAcquired directory descriptor acquired unlock recover before held
    rw [denied]
    exact Or.inl ⟨held, rfl⟩

end Alvoki.Storage.DiskSession
