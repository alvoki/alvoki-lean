import Alvoki.Storage.Disk.CachedWalOpenFailure
import Alvoki.Storage.Disk.SyncHandleRouting

namespace Alvoki.Storage.SyncHandleRouting

open System

/-- The native keeper reader rejects a short or unrepresentable held extent
before opening the path, reading any bytes or remembering a handle. -/
theorem readKeeperWith_rejectsExtent {image handle : Type}
    (openRead : FilePath → EStateM IO.Error image handle)
    (readPrefix : handle → Nat → EStateM IO.Error image ByteArray)
    (remember : FilePath → handle → EStateM IO.Error image Unit)
    (path : FilePath) (count fileSize : Nat) (before : image)
    (invalid : ¬ (count ≤ fileSize ∧ count < USize.size)) :
    readKeeperWith openRead readPrefix remember path count fileSize before =
      .error (IO.userError s!"WAL keeper does not cover its selected prefix: '{path}'") before := by
  simp [readKeeperWith, invalid, Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

end Alvoki.Storage.SyncHandleRouting

namespace Alvoki.Storage.WalSegmentRepair

open System SyncHandleRouting
open WAL (frameSize)

/-- Earlier exact seal reads may reach a short keeper. The cached opener
returns the pathname-specific diagnostic before replay or any repair. -/
theorem CachedWalOpenSelection.reopen_keeperExtentError {image handle : Type} {directory : DiskDirectory}
    {readOptional : FilePath → EStateM IO.Error image (Option ByteArray)}
    {readRunSize : FilePath → EStateM IO.Error image Nat}
    {readRunPrefix : FilePath → Nat → EStateM IO.Error image ByteArray}
    {list : FilePath → EStateM IO.Error image (Array IO.FS.DirEntry)}
    {lstat : FilePath → EStateM IO.Error image (Except IO.Error IO.FS.Metadata)}
    {readSeal : FilePath → Nat → EStateM IO.Error image ByteArray}
    {before reached : image} {keeper : Nat} {metadata : IO.FS.Metadata}
    (report : CachedWalOpenSelection directory readOptional readRunSize readRunPrefix list lstat before)
    (openRead : FilePath → EStateM IO.Error image handle)
    (readPrefix : handle → Nat → EStateM IO.Error image ByteArray)
    (remember : FilePath → handle → EStateM IO.Error image Unit)
    (removeFile : FilePath → EStateM IO.Error image (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error image Unit)
    (sync : Array FilePath → EStateM IO.Error image Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error image Unit)
    (seals : CachedWalKeeperReached directory readSeal keeper metadata report.required report.afterScan reached)
    (invalid : ¬ ((report.length.toNat / frameSize - keeper) * frameSize ≤ metadata.byteSize.toNat ∧
      (report.length.toNat / frameSize - keeper) * frameSize < USize.size)) :
    reopenMarkedBoundedWithCachedExtents directory readOptional readRunSize readRunPrefix list lstat readSeal
      (readKeeperWith openRead readPrefix remember) removeFile write sync renameFile before =
      .error (IO.userError s!"WAL keeper does not cover its selected prefix: '{directory.file (.walSegment keeper)}'")
        reached := by
  apply report.reopen_payloadError
  exact seals.read_error (report.length.toNat / frameSize) (readKeeperWith openRead readPrefix remember)
    (readKeeperWith_rejectsExtent openRead readPrefix remember _ _ _ _ invalid)

/-- If all preceding acquisition reports are read-only, the keeper guard
returns the original file image. -/
theorem CachedWalOpenSelection.keeperReached_eq_of_readonly {image : Type} {directory : DiskDirectory}
    {readOptional : FilePath → EStateM IO.Error image (Option ByteArray)}
    {readRunSize : FilePath → EStateM IO.Error image Nat}
    {readRunPrefix : FilePath → Nat → EStateM IO.Error image ByteArray}
    {list : FilePath → EStateM IO.Error image (Array IO.FS.DirEntry)}
    {lstat : FilePath → EStateM IO.Error image (Except IO.Error IO.FS.Metadata)}
    {readSeal : FilePath → Nat → EStateM IO.Error image ByteArray}
    {before reached : image} {keeper : Nat} {metadata : IO.FS.Metadata}
    (report : CachedWalOpenSelection directory readOptional readRunSize readRunPrefix list lstat before)
    (seals : CachedWalKeeperReached directory readSeal keeper metadata report.required report.afterScan reached)
    (checkpointReadOnly : report.afterCheckpoint = before)
    (markerReadOnly : report.afterMarker = report.afterCheckpoint)
    (listReadOnly : report.afterList = report.afterMarker)
    (scanReadOnly : report.afterScan = report.afterList)
    (sealReadOnly : ∀ path count initial bytes after, readSeal path count initial = .ok bytes after → after = initial) :
    reached = before :=
  (seals.reached_eq_of_readonly sealReadOnly).trans
    (report.afterScan_eq_of_readonly checkpointReadOnly markerReadOnly listReadOnly scanReadOnly)

end Alvoki.Storage.WalSegmentRepair

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting
open WAL (frameSize)

/-- After acquiring the lock, rejection of the final keeper prevents
installation. Cleanup preserves the reached image and only changes which
error and owner are returned. -/
theorem runOpenWithInstallation_cachedKeeperExtentError {image handle : Type} (directory : DiskDirectory)
    (descriptor nextRef : Nat) (unlock : UnlockReport) (localUnlock : unlock.LocalFlock)
    {readOptional : FilePath → EStateM IO.Error image (Option ByteArray)}
    {readRunSize : FilePath → EStateM IO.Error image Nat}
    {readRunPrefix : FilePath → Nat → EStateM IO.Error image ByteArray}
    {list : FilePath → EStateM IO.Error image (Array IO.FS.DirEntry)}
    {lstat : FilePath → EStateM IO.Error image (Except IO.Error IO.FS.Metadata)}
    {readSeal : FilePath → Nat → EStateM IO.Error image ByteArray}
    (before : LockedFileState image) {reached : image} {keeper : Nat} {metadata : IO.FS.Metadata}
    (report : CachedWalOpenSelection directory readOptional readRunSize readRunPrefix list lstat before.image)
    (openRead : FilePath → EStateM IO.Error image handle)
    (readPrefix : handle → Nat → EStateM IO.Error image ByteArray)
    (remember : FilePath → handle → EStateM IO.Error image Unit)
    (removeFile : FilePath → EStateM IO.Error image (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error image Unit)
    (sync : Array FilePath → EStateM IO.Error image Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error image Unit)
    (seals : CachedWalKeeperReached directory readSeal keeper metadata report.required report.afterScan reached)
    (invalid : ¬ ((report.length.toNat / frameSize - keeper) * frameSize ≤ metadata.byteSize.toNat ∧
      (report.length.toNat / frameSize - keeper) * frameSize < USize.size)) :
    let recover := reopenMarkedBoundedWithCachedExtents directory readOptional readRunSize readRunPrefix list lstat
      readSeal (readKeeperWith openRead readPrefix remember) removeFile write sync renameFile
    runOpenWithInstallation directory descriptor nextRef (.ok true) unlock recover before =
      match unlock with
      | .success =>
        .error (IO.userError s!"WAL keeper does not cover its selected prefix: '{directory.file (.walSegment keeper)}'")
          ⟨reached, before.owners.set (directory.file .lock) none⟩
      | .failure cleanup _ =>
        .error cleanup ⟨reached, before.owners.set (directory.file .lock) (some descriptor)⟩ := by
  intro recover
  have failed : recover before.image = .error
      (IO.userError s!"WAL keeper does not cover its selected prefix: '{directory.file (.walSegment keeper)}'")
      reached :=
    report.reopen_keeperExtentError openRead readPrefix remember removeFile write sync renameFile seals invalid
  rw [runOpenWithInstallation_acquiredRecoveryError directory descriptor nextRef unlock recover before failed]
  cases unlock with
  | success => rfl
  | failure cleanup released =>
    change released = false at localUnlock
    subst released
    rfl

end Alvoki.Storage.DiskSession
