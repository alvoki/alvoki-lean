import Alvoki.Storage.Disk.CachedOpenRejection
import Alvoki.Storage.Disk.CachedWalKeeperOpenFailure

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting
open WAL (frameSize)

/-- The cached opener selects from the visible marker and the observed
inventory. The selected extents reflect the bytes in the reached image. -/
structure CachedOpenAttempt.SelectedReads {directory : DiskDirectory} {before : LockedFileState FileImage}
    (attempt : CachedOpenAttempt directory before) where
  selection : CachedWalOpenSelection directory attempt.readOptional attempt.readRunSize attempt.readRunPrefix
    attempt.list attempt.lstat before.image
  visibleMarker : before.image.directory.active.walBoundary = some selection.marker
  sealExtents : ∀ entry ∈ selection.required.dropLast,
    (before.image.kept entry.1).map ByteArray.size = some entry.2.byteSize.toNat
  keeperExtent : ∀ entry, selection.required.getLast? = some entry →
    before.image.keeper.active.map ByteArray.size = some entry.2.byteSize.toNat
  checkpointReadOnly : selection.afterCheckpoint = before.image
  markerReadOnly : selection.afterMarker = selection.afterCheckpoint
  listReadOnly : selection.afterList = selection.afterMarker
  scanReadOnly : selection.afterScan = selection.afterList
  sealReadOnly : ∀ path count initial bytes after, attempt.readSeal path count initial = .ok bytes after → after = initial

private theorem CachedOpenAttempt.SelectedReads.scan_eq {directory : DiskDirectory} {before : LockedFileState FileImage}
    {attempt : CachedOpenAttempt directory before} (reads : attempt.SelectedReads) :
    reads.selection.afterScan = before.image :=
  reads.selection.afterScan_eq_of_readonly reads.checkpointReadOnly reads.markerReadOnly reads.listReadOnly reads.scanReadOnly

/-- A selected seal's extent can fail after earlier successful seal reads.
The rejected preparation keeps the current files and the seal diagnostic. -/
def CachedOpenRejection.ofSealExtent {directory : DiskDirectory} {before : LockedFileState FileImage}
    {attempt : CachedOpenAttempt directory before} (reads : attempt.SelectedReads) {reached : FileImage}
    (failed : CachedWalExtentFailure directory attempt.readSeal reads.selection.required reads.selection.afterScan reached) :
    CachedOpenRejection directory before := by
  have unchanged := (failed.reached_eq_of_readonly reads.sealReadOnly).trans reads.scan_eq
  have rejected := reads.selection.prepare_payloadError attempt.readKeeper
    (readCachedWalPayloads_extentFailure (reads.selection.length.toNat / frameSize) attempt.readKeeper failed)
  exact ⟨attempt, selectedWalSpanError, unchanged ▸ rejected⟩

/-- The actual keeper guard fails before opening the keeper. Earlier seal
reads preserve the reached image and cleanup owns the exact same local lock. -/
def CachedOpenRejection.ofKeeperExtent {directory : DiskDirectory} {before : LockedFileState FileImage}
    {handle : Type} {attempt : CachedOpenAttempt directory before} (reads : attempt.SelectedReads)
    (openRead : FilePath → EStateM IO.Error FileImage handle)
    (readPrefix : handle → Nat → EStateM IO.Error FileImage ByteArray)
    (remember : FilePath → handle → EStateM IO.Error FileImage Unit)
    (reader : attempt.readKeeper = readKeeperWith openRead readPrefix remember)
    {keeper : Nat} {metadata : IO.FS.Metadata} {reached : FileImage}
    (seals : CachedWalKeeperReached directory attempt.readSeal keeper metadata reads.selection.required
      reads.selection.afterScan reached)
    (invalid : ¬ ((reads.selection.length.toNat / frameSize - keeper) * frameSize ≤ metadata.byteSize.toNat ∧
      (reads.selection.length.toNat / frameSize - keeper) * frameSize < USize.size)) :
    CachedOpenRejection directory before := by
  let path := directory.file (.walSegment keeper)
  let count := (reads.selection.length.toNat / frameSize - keeper) * frameSize
  let cause := IO.userError s!"WAL keeper does not cover its selected prefix: '{path}'"
  have failed : attempt.readKeeper path count metadata.byteSize.toNat reached = .error cause reached := by
    rw [reader]
    exact readKeeperWith_rejectsExtent openRead readPrefix remember path count metadata.byteSize.toNat reached invalid
  have unchanged := (seals.reached_eq_of_readonly reads.sealReadOnly).trans reads.scan_eq
  have rejected := reads.selection.prepare_payloadError attempt.readKeeper
    (seals.read_error (reads.selection.length.toNat / frameSize) attempt.readKeeper failed)
  exact ⟨attempt, cause, unchanged ▸ rejected⟩

end Alvoki.Storage.DiskSession
