import Alvoki.Storage.Disk.SizedCheckpointOpenFailure

namespace Alvoki.Storage.WalSegmentRepair

open System
open WAL (frameSize)

/-- A payload error after the selected reads returns before replay and repair. -/
theorem readSelectedWithCachedExtents_payloadError {image : Type} (directory : DiskDirectory)
    (watermark : Nat) (length : UInt64)
    (list : FilePath → EStateM IO.Error image (Array IO.FS.DirEntry))
    (lstat : FilePath → EStateM IO.Error image (Except IO.Error IO.FS.Metadata))
    (readSeal : FilePath → Nat → EStateM IO.Error image ByteArray)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error image ByteArray)
    {before listedState scannedState reached : image} {cause : IO.Error}
    (checked : length.toNat % frameSize = 0 ∧ watermark ≤ length.toNat / frameSize)
    {entries : Array IO.FS.DirEntry} (listed : list directory.path before = .ok entries listedState)
    {extents required : List (Nat × IO.FS.Metadata)} {newer : List Nat}
    (scanned : readWalSegmentExtentsWith (m := EStateM IO.Error image) directory lstat
      (entries.toList.map (·.fileName)) listedState = .ok extents scannedState)
    (selected : selectWalExtentsThrough extents watermark (length.toNat / frameSize) = some (required, newer))
    (payloads : readCachedWalPayloads directory (length.toNat / frameSize) readSeal readKeeper required scannedState =
      .error cause reached) :
    readSelectedWithCachedExtents (m := EStateM IO.Error image) directory watermark length list lstat
      readSeal readKeeper before = .error cause reached := by
  simp [readSelectedWithCachedExtents, withAbsoluteWalCutoff_estate, checked, listed, scanned, selected, payloads,
    Bind.bind, EStateM.bind]

/-- The reported selected paths locate the invalid extent after all canonical
probes and any successful earlier seal reads. -/
theorem readSelectedWithCachedExtents_extentFailure {image : Type} (directory : DiskDirectory)
    (watermark : Nat) (length : UInt64)
    (list : FilePath → EStateM IO.Error image (Array IO.FS.DirEntry))
    (lstat : FilePath → EStateM IO.Error image (Except IO.Error IO.FS.Metadata))
    (readSeal : FilePath → Nat → EStateM IO.Error image ByteArray)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error image ByteArray)
    {before listedState scannedState reached : image}
    (checked : length.toNat % frameSize = 0 ∧ watermark ≤ length.toNat / frameSize)
    {entries : Array IO.FS.DirEntry} (listed : list directory.path before = .ok entries listedState)
    {extents required : List (Nat × IO.FS.Metadata)} {newer : List Nat}
    (scanned : readWalSegmentExtentsWith (m := EStateM IO.Error image) directory lstat
      (entries.toList.map (·.fileName)) listedState = .ok extents scannedState)
    (selected : selectWalExtentsThrough extents watermark (length.toNat / frameSize) = some (required, newer))
    (failed : CachedWalExtentFailure directory readSeal required scannedState reached) :
    readSelectedWithCachedExtents (m := EStateM IO.Error image) directory watermark length list lstat
      readSeal readKeeper before = .error selectedWalSpanError reached :=
  readSelectedWithCachedExtents_payloadError directory watermark length list lstat readSeal readKeeper
    checked listed scanned selected (readCachedWalPayloads_extentFailure (length.toNat / frameSize) readKeeper failed)

/-- Checkpoint and inventory observations leading to the cached selected payloads. -/
structure CachedWalOpenSelection {image : Type} (directory : DiskDirectory)
    (readOptional : FilePath → EStateM IO.Error image (Option ByteArray))
    (readRunSize : FilePath → EStateM IO.Error image Nat)
    (readRunPrefix : FilePath → Nat → EStateM IO.Error image ByteArray)
    (list : FilePath → EStateM IO.Error image (Array IO.FS.DirEntry))
    (lstat : FilePath → EStateM IO.Error image (Except IO.Error IO.FS.Metadata))
    (before : image) where
  checkpoint : Option (PackedTable × UInt64)
  afterCheckpoint : image
  checkpointRead : readIntegrityCheckpointSized directory (readOptional (directory.file .manifest))
    readRunSize readRunPrefix before = .ok checkpoint afterCheckpoint
  marker : ByteArray
  afterMarker : image
  markerRead : readOptional (directory.file .walBoundary) afterCheckpoint = .ok (some marker) afterMarker
  length : UInt64
  decoded : WAL.Boundary.decode marker = .ok length
  checked : length.toNat % frameSize = 0 ∧ (checkpoint.getD (.empty, 0)).1.committed.toNat ≤ length.toNat / frameSize
  entries : Array IO.FS.DirEntry
  afterList : image
  listed : list directory.path afterMarker = .ok entries afterList
  extents : List (Nat × IO.FS.Metadata)
  afterScan : image
  scanned : readWalSegmentExtentsWith (m := EStateM IO.Error image) directory lstat
    (entries.toList.map (·.fileName)) afterList = .ok extents afterScan
  required : List (Nat × IO.FS.Metadata)
  newer : List Nat
  selected : selectWalExtentsThrough extents (checkpoint.getD (.empty, 0)).1.committed.toNat
    (length.toNat / frameSize) = some (required, newer)

theorem CachedWalOpenSelection.afterScan_eq_of_readonly {image : Type} {directory : DiskDirectory}
    {readOptional : FilePath → EStateM IO.Error image (Option ByteArray)}
    {readRunSize : FilePath → EStateM IO.Error image Nat}
    {readRunPrefix : FilePath → Nat → EStateM IO.Error image ByteArray}
    {list : FilePath → EStateM IO.Error image (Array IO.FS.DirEntry)}
    {lstat : FilePath → EStateM IO.Error image (Except IO.Error IO.FS.Metadata)}
    {before : image}
    (report : CachedWalOpenSelection directory readOptional readRunSize readRunPrefix list lstat before)
    (checkpointReadOnly : report.afterCheckpoint = before)
    (markerReadOnly : report.afterMarker = report.afterCheckpoint)
    (listReadOnly : report.afterList = report.afterMarker)
    (scanReadOnly : report.afterScan = report.afterList) :
    report.afterScan = before :=
  scanReadOnly.trans (listReadOnly.trans (markerReadOnly.trans checkpointReadOnly))

/-- The exact checkpoint, marker, inventory and seal observations reached by
the cached bounded opener before it rejects a selected extent. -/
structure CachedWalOpenExtentFailure {image : Type} (directory : DiskDirectory)
    (readOptional : FilePath → EStateM IO.Error image (Option ByteArray))
    (readRunSize : FilePath → EStateM IO.Error image Nat)
    (readRunPrefix : FilePath → Nat → EStateM IO.Error image ByteArray)
    (list : FilePath → EStateM IO.Error image (Array IO.FS.DirEntry))
    (lstat : FilePath → EStateM IO.Error image (Except IO.Error IO.FS.Metadata))
    (readSeal : FilePath → Nat → EStateM IO.Error image ByteArray)
    (before reached : image) extends
    CachedWalOpenSelection directory readOptional readRunSize readRunPrefix list lstat before where
  failed : CachedWalExtentFailure directory readSeal required afterScan reached

/-- Selected payload rejection prevents preparation from reaching replay. -/
theorem CachedWalOpenSelection.prepare_payloadError {image : Type} {directory : DiskDirectory}
    {readOptional : FilePath → EStateM IO.Error image (Option ByteArray)}
    {readRunSize : FilePath → EStateM IO.Error image Nat}
    {readRunPrefix : FilePath → Nat → EStateM IO.Error image ByteArray}
    {list : FilePath → EStateM IO.Error image (Array IO.FS.DirEntry)}
    {lstat : FilePath → EStateM IO.Error image (Except IO.Error IO.FS.Metadata)}
    {readSeal : FilePath → Nat → EStateM IO.Error image ByteArray}
    {before reached : image} {cause : IO.Error}
    (report : CachedWalOpenSelection directory readOptional readRunSize readRunPrefix list lstat before)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error image ByteArray)
    (payloads : readCachedWalPayloads directory (report.length.toNat / frameSize) readSeal readKeeper
      report.required report.afterScan = .error cause reached) :
    prepareBoundedMarkedFromReaders directory
      (readIntegrityCheckpointSized directory (readOptional (directory.file .manifest)) readRunSize readRunPrefix)
      readOptional (fun watermark length => readSelectedWithCachedExtents directory watermark length list lstat
        readSeal readKeeper) before = .error cause reached := by
  have wal := readSelectedWithCachedExtents_payloadError directory _ report.length list lstat readSeal readKeeper
    report.checked report.listed report.scanned report.selected payloads
  simp [prepareBoundedMarkedFromReaders, report.checkpointRead, report.markerRead, report.decoded, wal,
    Bind.bind, EStateM.bind, liftExcept, Except.mapError, Pure.pure, EStateM.pure]

/-- The cached marked opener returns a selected read error before repair. -/
theorem CachedWalOpenSelection.reopen_payloadError {image : Type} {directory : DiskDirectory}
    {readOptional : FilePath → EStateM IO.Error image (Option ByteArray)}
    {readRunSize : FilePath → EStateM IO.Error image Nat}
    {readRunPrefix : FilePath → Nat → EStateM IO.Error image ByteArray}
    {list : FilePath → EStateM IO.Error image (Array IO.FS.DirEntry)}
    {lstat : FilePath → EStateM IO.Error image (Except IO.Error IO.FS.Metadata)}
    {readSeal : FilePath → Nat → EStateM IO.Error image ByteArray}
    {before reached : image} {cause : IO.Error}
    (report : CachedWalOpenSelection directory readOptional readRunSize readRunPrefix list lstat before)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error image ByteArray)
    (removeFile : FilePath → EStateM IO.Error image (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error image Unit)
    (sync : Array FilePath → EStateM IO.Error image Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error image Unit)
    (payloads : readCachedWalPayloads directory (report.length.toNat / frameSize) readSeal readKeeper
      report.required report.afterScan = .error cause reached) :
    reopenMarkedBoundedWithCachedExtents directory readOptional readRunSize readRunPrefix list lstat
      readSeal readKeeper removeFile write sync renameFile before = .error cause reached := by
  simp only [reopenMarkedBoundedWithCachedExtents, Bind.bind, EStateM.bind, report.prepare_payloadError readKeeper payloads]

/-- The cached native schedule stops at the invalid extent. The actual
keeper reader, replay and repair callbacks do not enter the outcome. -/
theorem CachedWalOpenExtentFailure.reopen_error {image : Type} {directory : DiskDirectory}
    {readOptional : FilePath → EStateM IO.Error image (Option ByteArray)}
    {readRunSize : FilePath → EStateM IO.Error image Nat}
    {readRunPrefix : FilePath → Nat → EStateM IO.Error image ByteArray}
    {list : FilePath → EStateM IO.Error image (Array IO.FS.DirEntry)}
    {lstat : FilePath → EStateM IO.Error image (Except IO.Error IO.FS.Metadata)}
    {readSeal : FilePath → Nat → EStateM IO.Error image ByteArray}
    {before reached : image}
    (report : CachedWalOpenExtentFailure directory readOptional readRunSize readRunPrefix list lstat readSeal before reached)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error image ByteArray)
    (removeFile : FilePath → EStateM IO.Error image (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error image Unit)
    (sync : Array FilePath → EStateM IO.Error image Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error image Unit) :
    reopenMarkedBoundedWithCachedExtents directory readOptional readRunSize readRunPrefix list lstat
      readSeal readKeeper removeFile write sync renameFile before = .error selectedWalSpanError reached :=
  report.toCachedWalOpenSelection.reopen_payloadError readKeeper removeFile write sync renameFile
    (readCachedWalPayloads_extentFailure (report.length.toNat / frameSize) readKeeper report.failed)

/-- There is no file mutation when the reached preparation observations
are read-only in the file interpreter. -/
theorem CachedWalOpenExtentFailure.reached_eq_of_readonly {image : Type} {directory : DiskDirectory}
    {readOptional : FilePath → EStateM IO.Error image (Option ByteArray)}
    {readRunSize : FilePath → EStateM IO.Error image Nat}
    {readRunPrefix : FilePath → Nat → EStateM IO.Error image ByteArray}
    {list : FilePath → EStateM IO.Error image (Array IO.FS.DirEntry)}
    {lstat : FilePath → EStateM IO.Error image (Except IO.Error IO.FS.Metadata)}
    {readSeal : FilePath → Nat → EStateM IO.Error image ByteArray}
    {before reached : image}
    (report : CachedWalOpenExtentFailure directory readOptional readRunSize readRunPrefix list lstat readSeal before reached)
    (checkpointReadOnly : report.afterCheckpoint = before)
    (markerReadOnly : report.afterMarker = report.afterCheckpoint)
    (listReadOnly : report.afterList = report.afterMarker)
    (scanReadOnly : report.afterScan = report.afterList)
    (sealReadOnly : ∀ path count first bytes after, readSeal path count first = .ok bytes after → after = first) :
    reached = before :=
  (report.failed.reached_eq_of_readonly sealReadOnly).trans
    (report.toCachedWalOpenSelection.afterScan_eq_of_readonly checkpointReadOnly markerReadOnly listReadOnly scanReadOnly)

end Alvoki.Storage.WalSegmentRepair

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- The exact wrong-seal error prevents installation. The local unlock
outcome decides which error and owner are returned with the reached image. -/
theorem runOpenWithInstallation_cachedSealExtentError {image : Type}
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
    (before : LockedFileState image) {reached : image}
    (failed : acquired = .ok true →
      Nonempty (CachedWalOpenExtentFailure directory readOptional readRunSize readRunPrefix list lstat
        readSeal before.image reached)) :
    let recover := reopenMarkedBoundedWithCachedExtents directory readOptional readRunSize readRunPrefix list lstat
      readSeal readKeeper removeFile write sync renameFile
    runOpenWithInstallation directory descriptor nextRef acquired unlock recover before =
      match acquired with
      | .error lockError => .error lockError before
      | .ok false => .error (IO.userError s!"database already open: {directory.path}") before
      | .ok true => match unlock with
        | .success => .error selectedWalSpanError ⟨reached, before.owners.set (directory.file .lock) none⟩
        | .failure cleanup _ =>
          .error cleanup ⟨reached, before.owners.set (directory.file .lock) (some descriptor)⟩ := by
  intro recover
  rcases acquired with lockError | (_ | _)
  · rfl
  · rfl
  · obtain ⟨report⟩ := failed rfl
    have failedRecovery : recover before.image = .error selectedWalSpanError reached :=
      report.reopen_error readKeeper removeFile write sync renameFile
    rw [runOpenWithInstallation_acquiredRecoveryError directory descriptor nextRef unlock recover before failedRecovery]
    cases unlock with
    | success => rfl
    | failure cleanup released =>
      change released = false at localUnlock
      subst released
      rfl

end Alvoki.Storage.DiskSession
