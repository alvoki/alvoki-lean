import Alvoki.Storage.Disk.SizedCheckpointOpenFailure

namespace Alvoki.WAL.Boundary

/-- Marker length is checked before any version or checksum word. -/
theorem decode_lengthError (bytes : ByteArray) (wrongSize : bytes.size ≠ 24) :
    decode bytes = .error "invalid WAL boundary length" := by
  simp [decode, wrongSize]

end Alvoki.WAL.Boundary

namespace Alvoki.Storage.WalSegmentRepair

open System

/-- The exact sized checkpoint and present marker read reached under the
canonical directory lock. The bytes still need to pass the marker decoder. -/
structure CachedWalMarkerRead {image : Type} (directory : DiskDirectory)
    (readOptional : FilePath → EStateM IO.Error image (Option ByteArray))
    (readRunSize : FilePath → EStateM IO.Error image Nat)
    (readRunPrefix : FilePath → Nat → EStateM IO.Error image ByteArray) (before reached : image) where
  checkpoint : Option (PackedTable × UInt64)
  afterCheckpoint : image
  checkpointRead : readIntegrityCheckpointSized directory (readOptional (directory.file .manifest))
    readRunSize readRunPrefix before = .ok checkpoint afterCheckpoint
  marker : ByteArray
  markerRead : readOptional (directory.file .walBoundary) afterCheckpoint = .ok (some marker) reached

/-- A rejected present marker returns the actual decoder diagnostic and the
reached image. No inventory, WAL payload, replay or repair action runs. -/
theorem CachedWalMarkerRead.reopen_decodeError {image : Type} {directory : DiskDirectory}
    {readOptional : FilePath → EStateM IO.Error image (Option ByteArray)}
    {readRunSize : FilePath → EStateM IO.Error image Nat}
    {readRunPrefix : FilePath → Nat → EStateM IO.Error image ByteArray}
    {before reached : image} (report : CachedWalMarkerRead directory readOptional readRunSize readRunPrefix before reached)
    (list : FilePath → EStateM IO.Error image (Array IO.FS.DirEntry))
    (lstat : FilePath → EStateM IO.Error image (Except IO.Error IO.FS.Metadata))
    (readSeal : FilePath → Nat → EStateM IO.Error image ByteArray)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error image ByteArray)
    (removeFile : FilePath → EStateM IO.Error image (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error image Unit)
    (sync : Array FilePath → EStateM IO.Error image Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error image Unit)
    {message : String} (invalid : WAL.Boundary.decode report.marker = .error message) :
    reopenMarkedBoundedWithCachedExtents directory readOptional readRunSize readRunPrefix list lstat readSeal
      readKeeper removeFile write sync renameFile before = .error (IO.userError message) reached := by
  simp [reopenMarkedBoundedWithCachedExtents, prepareBoundedMarkedFromReaders, report.checkpointRead,
    report.markerRead, invalid, Bind.bind, EStateM.bind, liftExcept, Except.mapError, throw, throwThe,
    MonadExceptOf.throw, EStateM.throw]

/-- Read-only checkpoint and marker reports preserve the file image. -/
theorem CachedWalMarkerRead.reached_eq_of_readonly {image : Type} {directory : DiskDirectory}
    {readOptional : FilePath → EStateM IO.Error image (Option ByteArray)}
    {readRunSize : FilePath → EStateM IO.Error image Nat}
    {readRunPrefix : FilePath → Nat → EStateM IO.Error image ByteArray}
    {before reached : image} (report : CachedWalMarkerRead directory readOptional readRunSize readRunPrefix before reached)
    (checkpointReadOnly : report.afterCheckpoint = before) (markerReadOnly : reached = report.afterCheckpoint) :
    reached = before :=
  markerReadOnly.trans checkpointReadOnly

end Alvoki.Storage.WalSegmentRepair

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- A malformed marker prevents installation. The local unlock outcome
decides which error and lock owner return with the reached image. -/
theorem runOpenWithInstallation_cachedMarkerDecodeError {image : Type} (directory : DiskDirectory)
    (descriptor nextRef : Nat) (unlock : UnlockReport) (localUnlock : unlock.LocalFlock)
    {readOptional : FilePath → EStateM IO.Error image (Option ByteArray)}
    {readRunSize : FilePath → EStateM IO.Error image Nat}
    {readRunPrefix : FilePath → Nat → EStateM IO.Error image ByteArray}
    (before : LockedFileState image) {reached : image}
    (report : CachedWalMarkerRead directory readOptional readRunSize readRunPrefix before.image reached)
    (list : FilePath → EStateM IO.Error image (Array IO.FS.DirEntry))
    (lstat : FilePath → EStateM IO.Error image (Except IO.Error IO.FS.Metadata))
    (readSeal : FilePath → Nat → EStateM IO.Error image ByteArray)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error image ByteArray)
    (removeFile : FilePath → EStateM IO.Error image (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error image Unit)
    (sync : Array FilePath → EStateM IO.Error image Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error image Unit)
    {message : String} (invalid : WAL.Boundary.decode report.marker = .error message) :
    let recover := reopenMarkedBoundedWithCachedExtents directory readOptional readRunSize readRunPrefix list lstat
      readSeal readKeeper removeFile write sync renameFile
    runOpenWithInstallation directory descriptor nextRef (.ok true) unlock recover before =
      match unlock with
      | .success => .error (IO.userError message) ⟨reached, before.owners.set (directory.file .lock) none⟩
      | .failure cleanup _ =>
        .error cleanup ⟨reached, before.owners.set (directory.file .lock) (some descriptor)⟩ := by
  intro recover
  have failed : recover before.image = .error (IO.userError message) reached :=
    report.reopen_decodeError list lstat readSeal readKeeper removeFile write sync renameFile invalid
  rw [runOpenWithInstallation_acquiredRecoveryError directory descriptor nextRef unlock recover before failed]
  cases unlock with
  | success => rfl
  | failure cleanup released =>
    change released = false at localUnlock
    subst released
    rfl

end Alvoki.Storage.DiskSession
