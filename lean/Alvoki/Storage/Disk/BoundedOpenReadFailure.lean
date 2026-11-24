import Alvoki.Storage.Disk.SegmentedSessionInstall
import Alvoki.Storage.Disk.WalSegmentBoundedOpenEffects

namespace Alvoki.Storage.WalSegmentRepair

open System

/-- Execute the bounded marked reader on its raw primitive reports. A
preparation error returns the original image before any repair callback.
Successful preparation supplies the exact plan and physical keeper size
to the actual repair worker. -/
theorem reopenMarkedBoundedWith_readOutcome {image : Type} (directory : DiskDirectory)
    (readOptional : FilePath → Except IO.Error (Option ByteArray))
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → Except IO.Error ByteArray)
    (readPrefix : FilePath → Nat → Except IO.Error KeeperPrefix)
    (removeFile : FilePath → EStateM IO.Error image (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error image Unit)
    (sync : Array FilePath → EStateM IO.Error image Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error image Unit) (before : image) :
    reopenMarkedBoundedWith directory
      (fun path => liftExcept (readOptional path)) (fun path => liftExcept (list path))
      (fun path => liftExcept (lstat path)) (fun path => liftExcept (readBin path))
      (fun path size => liftExcept (readPrefix path size)) removeFile write sync renameFile before =
      match prepareBoundedMarkedWith directory readOptional list lstat readBin readPrefix with
      | .error cause => .error cause before
      | .ok (plan, opened, size) =>
        match finishBoundedMarkedOpen directory plan size removeFile write sync renameFile before with
        | .error cause after => .error cause after
        | .ok _ after => .ok opened after := by
  unfold reopenMarkedBoundedWith
  rw [prepareBoundedMarkedWith_liftReports]
  cases prepareBoundedMarkedWith directory readOptional list lstat readBin readPrefix with
  | error cause => rfl
  | ok prepared =>
    obtain ⟨plan, opened, size⟩ := prepared
    simp only [liftExcept, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
    cases finishBoundedMarkedOpen directory plan size removeFile write sync renameFile before <;> rfl

end Alvoki.Storage.WalSegmentRepair

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- A denied acquisition returns its original error or the busy error,
without starting the marked reader. If acquisition succeeded, a rejected
preparation installs no session and leaves the file image untouched.
In that branch the unlock report determines ownership and error precedence. -/
theorem runOpenWithInstallation_boundedPreparationError {image : Type}
    (directory : DiskDirectory) (descriptor nextRef : Nat) (acquired : Except IO.Error Bool) (unlock : UnlockReport)
    (readOptional : FilePath → Except IO.Error (Option ByteArray))
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → Except IO.Error ByteArray)
    (readPrefix : FilePath → Nat → Except IO.Error KeeperPrefix)
    (removeFile : FilePath → EStateM IO.Error image (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error image Unit)
    (sync : Array FilePath → EStateM IO.Error image Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error image Unit)
    (before : LockedFileState image) {cause : IO.Error}
    (failed : acquired = .ok true →
      prepareBoundedMarkedWith directory readOptional list lstat readBin readPrefix = .error cause) :
    let recover := reopenMarkedBoundedWith directory
      (fun path => liftExcept (readOptional path)) (fun path => liftExcept (list path))
      (fun path => liftExcept (lstat path)) (fun path => liftExcept (readBin path))
      (fun path size => liftExcept (readPrefix path size)) removeFile write sync renameFile
    runOpenWithInstallation directory descriptor nextRef acquired unlock recover before =
      match acquired with
      | .error lockError => .error lockError before
      | .ok false => .error (IO.userError s!"database already open: {directory.path}") before
      | .ok true => match unlock with
        | .success => .error cause ⟨before.image, before.owners.set (directory.file .lock) none⟩
        | .failure cleanup released =>
          .error cleanup ⟨before.image, before.owners.set (directory.file .lock)
            (if released then none else some descriptor)⟩ := by
  intro recover
  rw [runOpenWithInstallation_outcome]
  rcases acquired with lockError | (_ | _)
  · rfl
  · rfl
  · have rejected : recover before.image = .error cause before.image := by
      dsimp only [recover]
      rw [reopenMarkedBoundedWith_readOutcome, failed rfl]
    rw [runOpenWithImage_acquired, rejected]
    cases unlock <;> rfl

end Alvoki.Storage.DiskSession
