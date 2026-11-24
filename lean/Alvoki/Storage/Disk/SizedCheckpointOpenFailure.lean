import Alvoki.Storage.Disk.BoundedOpenReadFailure
import Alvoki.Storage.Disk.WalSegmentCachedExtentOpen

namespace Alvoki.Storage.WalSegmentRepair

open System

/-- The sized checkpoint stage runs before the marker, WAL selection and
repair. When it fails, those callbacks cannot affect the returned image. -/
theorem reopenMarkedBoundedWithCachedExtents_checkpointError {image : Type} (directory : DiskDirectory)
    (readOptional : FilePath → EStateM IO.Error image (Option ByteArray))
    (readRunSize : FilePath → EStateM IO.Error image Nat)
    (readRunPrefix : FilePath → Nat → EStateM IO.Error image ByteArray)
    (list : FilePath → EStateM IO.Error image (Array IO.FS.DirEntry))
    (lstat : FilePath → EStateM IO.Error image (Except IO.Error IO.FS.Metadata))
    (readSeal : FilePath → Nat → EStateM IO.Error image ByteArray)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error image ByteArray)
    (removeFile : FilePath → EStateM IO.Error image (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error image Unit)
    (sync : Array FilePath → EStateM IO.Error image Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error image Unit)
    {before reached : image} {cause : IO.Error}
    (failed : readIntegrityCheckpointSized directory (readOptional (directory.file .manifest))
      readRunSize readRunPrefix before = .error cause reached) :
    reopenMarkedBoundedWithCachedExtents directory readOptional readRunSize readRunPrefix list lstat
      readSeal readKeeper removeFile write sync renameFile before = .error cause reached := by
  simp only [reopenMarkedBoundedWithCachedExtents, prepareBoundedMarkedFromReaders, Bind.bind, EStateM.bind, failed]

end Alvoki.Storage.WalSegmentRepair

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- A rejected sized checkpoint reaches neither WAL acquisition nor
repair. Successful cleanup clears ownership and returns the read error.
A local flock cleanup error takes precedence and retains the owner. -/
theorem runOpenWithInstallation_cachedCheckpointError {image : Type}
    (directory : DiskDirectory) (descriptor nextRef : Nat) (acquired : Except IO.Error Bool)
    (unlock : UnlockReport) (localUnlock : unlock.LocalFlock)
    (readOptional : FilePath → EStateM IO.Error image (Option ByteArray))
    (readRunSize : FilePath → EStateM IO.Error image Nat)
    (readRunPrefix : FilePath → Nat → EStateM IO.Error image ByteArray)
    (list : FilePath → EStateM IO.Error image (Array IO.FS.DirEntry))
    (lstat : FilePath → EStateM IO.Error image (Except IO.Error IO.FS.Metadata))
    (readSeal : FilePath → Nat → EStateM IO.Error image ByteArray)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error image ByteArray)
    (removeFile : FilePath → EStateM IO.Error image (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error image Unit)
    (sync : Array FilePath → EStateM IO.Error image Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error image Unit)
    (before : LockedFileState image) {cause : IO.Error} {reached : image}
    (failed : acquired = .ok true →
      readIntegrityCheckpointSized directory (readOptional (directory.file .manifest))
        readRunSize readRunPrefix before.image = .error cause reached) :
    let recover := reopenMarkedBoundedWithCachedExtents directory readOptional readRunSize readRunPrefix list lstat
      readSeal readKeeper removeFile write sync renameFile
    runOpenWithInstallation directory descriptor nextRef acquired unlock recover before =
      match acquired with
      | .error lockError => .error lockError before
      | .ok false => .error (IO.userError s!"database already open: {directory.path}") before
      | .ok true => match unlock with
        | .success => .error cause ⟨reached, before.owners.set (directory.file .lock) none⟩
        | .failure cleanup _ =>
          .error cleanup ⟨reached, before.owners.set (directory.file .lock) (some descriptor)⟩ := by
  intro recover
  rcases acquired with lockError | (_ | _)
  · rfl
  · rfl
  · have failedRecovery : recover before.image = .error cause reached :=
      reopenMarkedBoundedWithCachedExtents_checkpointError directory readOptional readRunSize readRunPrefix
        list lstat readSeal readKeeper removeFile write sync renameFile (failed rfl)
    rw [runOpenWithInstallation_acquiredRecoveryError directory descriptor nextRef unlock recover before failedRecovery]
    cases unlock with
    | success => rfl
    | failure cleanup released =>
      change released = false at localUnlock
      subst released
      rfl

end Alvoki.Storage.DiskSession
