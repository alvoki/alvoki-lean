import Alvoki.Storage.Disk.CachedOpenRejection
import Alvoki.Storage.Disk.OptionalFileRead

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

/-- The selected bytes reach the marker decoder before any WAL request. -/
theorem CachedWalMarkerRead.prepare_decodeError {image : Type} {directory : DiskDirectory}
    {readOptional : FilePath → EStateM IO.Error image (Option ByteArray)}
    {readRunSize : FilePath → EStateM IO.Error image Nat}
    {readRunPrefix : FilePath → Nat → EStateM IO.Error image ByteArray}
    {before reached : image} (report : CachedWalMarkerRead directory readOptional readRunSize readRunPrefix before reached)
    (readWal : Nat → UInt64 → EStateM IO.Error image (WalSegmentMarkerReads × Nat))
    {message : String} (invalid : WAL.Boundary.decode report.marker = .error message) :
    prepareBoundedMarkedFromReaders directory
      (readIntegrityCheckpointSized directory (readOptional (directory.file .manifest)) readRunSize readRunPrefix)
      readOptional readWal before = .error (IO.userError message) reached := by
  simp [prepareBoundedMarkedFromReaders, report.checkpointRead, report.markerRead, invalid,
    Bind.bind, EStateM.bind, liftExcept, Except.mapError, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

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
  simp only [reopenMarkedBoundedWithCachedExtents, Bind.bind, EStateM.bind,
    report.prepare_decodeError _ invalid]

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

/-- After a successful checkpoint read, the actual marker callback can
fail with its own diagnostic before decoding or requesting WAL bytes. -/
def CachedOpenRejection.ofMarkerReadError {directory : DiskDirectory} {before : LockedFileState FileImage}
    (attempt : CachedOpenAttempt directory before) {checkpoint : Option (PackedTable × UInt64)} {cause : IO.Error}
    (checkpointRead : readIntegrityCheckpointSized directory (attempt.readOptional (directory.file .manifest))
      attempt.readRunSize attempt.readRunPrefix before.image = .ok checkpoint before.image)
    (failed : attempt.readOptional (directory.file .walBoundary) before.image = .error cause before.image) :
    CachedOpenRejection directory before := by
  refine ⟨attempt, cause, ?_⟩
  simp only [CachedOpenAttempt.prepare, prepareBoundedMarkedFromReaders, Bind.bind, EStateM.bind, checkpointRead, failed]

/-- The shared optional reader preserves the original payload error after
finding a regular marker, even when the read itself reports ENOENT. -/
def CachedOpenRejection.ofMarkerPayloadReadError {directory : DiskDirectory} {before : LockedFileState FileImage}
    (attempt : CachedOpenAttempt directory before) {checkpoint : Option (PackedTable × UInt64)} {cause : IO.Error}
    (checkpointRead : readIntegrityCheckpointSized directory (attempt.readOptional (directory.file .manifest))
      attempt.readRunSize attempt.readRunPrefix before.image = .ok checkpoint before.image)
    (marker : OptionalPathRead before.image.directory.active.walBoundary)
    (reported : attempt.readOptional (directory.file .walBoundary) before.image =
      (liftExcept (marker.result (directory.file .walBoundary)) : EStateM IO.Error FileImage (Option ByteArray))
        before.image)
    {metadata : IO.FS.Metadata} (found : marker.lookup = .ok metadata) (regular : metadata.type = .file)
    (failed : marker.read = .error cause) : CachedOpenRejection directory before := by
  apply ofMarkerReadError attempt (cause := cause) checkpointRead
  rw [reported]
  have fileCheck : (IO.FS.FileType.file == IO.FS.FileType.file) = true := rfl
  simp [OptionalPathRead.result, readOptionalDatabaseFile, readOptionalDatabaseFileWithMetadata, found, regular,
    fileCheck, failed, Pure.pure, Bind.bind, Except.pure, Except.bind, liftExcept, throw, throwThe,
    MonadExceptOf.throw, EStateM.throw]

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

/-- A cached retry reads the bounded prefix of the visible malformed
marker after taking the lock. The read-only callbacks preserve the retry's
file image, including the unread bytes of an oversized marker. -/
structure CachedMarkerRejection (directory : DiskDirectory) (before : LockedFileState FileImage)
    extends CachedOpenAttempt directory before where
  reads : CachedWalMarkerRead directory readOptional readRunSize readRunPrefix before.image before.image
  checkpointReadOnly : reads.afterCheckpoint = before.image
  storedMarker : ByteArray
  visibleMarker : before.image.directory.active.walBoundary = some storedMarker
  boundedRead : reads.marker = storedMarker.extract 0 (min WAL.Boundary.acquisitionLimit storedMarker.size)
  message : String
  malformed : WAL.Boundary.decode storedMarker = .error message

namespace CachedMarkerRejection

variable {directory : DiskDirectory} {before : LockedFileState FileImage}

/-- The exact prefix reaching the decoder yields the stored marker's error. -/
theorem decodeError (rejection : CachedMarkerRejection directory before) :
    WAL.Boundary.decode rejection.reads.marker = .error rejection.message := by
  rw [rejection.boundedRead, WAL.Boundary.decode_acquisitionPrefix]
  exact rejection.malformed

def certified (rejection : CachedMarkerRejection directory before) : CachedOpenRejection directory before :=
  ⟨rejection.toCachedOpenAttempt, IO.userError rejection.message,
    rejection.reads.prepare_decodeError _ rejection.decodeError⟩

abbrev run (rejection : CachedMarkerRejection directory before) := rejection.toCachedOpenAttempt.run
abbrev after (rejection : CachedMarkerRejection directory before) := rejection.certified.after
abbrev error (rejection : CachedMarkerRejection directory before) := rejection.certified.error

/-- The acquired cached opener returns the exact marker or cleanup error. -/
theorem run_error (rejection : CachedMarkerRejection directory before) :
    rejection.run = .error rejection.error rejection.after :=
  rejection.certified.run_error

/-- The rejected marker read allows immediate retry on successful cleanup. -/
theorem immediateReacquire (rejection : CachedMarkerRejection directory before) :
    TryLockObserves rejection.after.owners directory (.ok true) ↔ rejection.unlock = .success :=
  rejection.certified.immediateReacquire

end CachedMarkerRejection

end Alvoki.Storage.DiskSession
