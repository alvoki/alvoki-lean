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

/-- A cached retry that reads the actual visible malformed marker after
taking the lock. Read-only callbacks cannot change the retry's file image. -/
structure CachedMarkerRejection (directory : DiskDirectory) (before : LockedFileState FileImage) where
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
  reads : CachedWalMarkerRead directory readOptional readRunSize readRunPrefix before.image before.image
  checkpointReadOnly : reads.afterCheckpoint = before.image
  visibleMarker : before.image.directory.active.walBoundary = some reads.marker
  message : String
  malformed : WAL.Boundary.decode reads.marker = .error message

namespace CachedMarkerRejection

variable {directory : DiskDirectory} {before : LockedFileState FileImage}

def run (rejection : CachedMarkerRejection directory before) :
    EStateM.Result IO.Error (LockedFileState FileImage) SegmentedSession :=
  runOpenWithInstallation directory rejection.descriptor rejection.nextRef (.ok true) rejection.unlock
    (reopenMarkedBoundedWithCachedExtents directory rejection.readOptional rejection.readRunSize rejection.readRunPrefix
      rejection.list rejection.lstat rejection.readSeal rejection.readKeeper rejection.removeFile rejection.write
      rejection.sync rejection.renameFile) before

def after (rejection : CachedMarkerRejection directory before) : LockedFileState FileImage :=
  let owner := match rejection.unlock with
    | .success => none
    | .failure _ _ => some rejection.descriptor
  { before with owners := before.owners.set (directory.file .lock) owner }

def error (rejection : CachedMarkerRejection directory before) : IO.Error :=
  match rejection.unlock with
  | .success => IO.userError rejection.message
  | .failure cleanup _ => cleanup

/-- The actual cached callback run returns the computed error and owner.
A prepared plan or completed repair is unnecessary for this retry edge. -/
theorem run_error (rejection : CachedMarkerRejection directory before) :
    rejection.run = .error rejection.error rejection.after := by
  have failed := rejection.reads.reopen_decodeError rejection.list rejection.lstat rejection.readSeal
    rejection.readKeeper rejection.removeFile rejection.write rejection.sync rejection.renameFile rejection.malformed
  unfold run
  rw [runOpenWithInstallation_acquiredRecoveryError _ _ _ _ _ _ failed]
  cases observed : rejection.unlock with
  | success => simp [after, error, observed]
  | failure cleanup released =>
    have retained : released = false := by simpa [UnlockReport.LocalFlock, observed] using rejection.localUnlock
    simp [after, error, observed, retained]

/-- The next cooperating open can acquire immediately exactly when the
local cleanup released this attempt's lock. -/
theorem immediateReacquire (rejection : CachedMarkerRejection directory before) :
    TryLockObserves rejection.after.owners directory (.ok true) ↔ rejection.unlock = .success := by
  cases observed : rejection.unlock <;> simp [TryLockObserves, after, observed, LockOwners.set]

end CachedMarkerRejection

end Alvoki.Storage.DiskSession
