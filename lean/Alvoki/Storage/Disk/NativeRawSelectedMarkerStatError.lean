import Alvoki.Storage.Disk.NativeRawManifestStatError
import Alvoki.Storage.Disk.NativeRawPresentManifestListing

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {admission : CensusOpenAdmissionReports input directory (view.descriptors entry) (view.files entry)}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {fileCalls : MarkedTemporaryReadCalls heap} {release : IO.FS.Handle → heap → heap}
  {durable : CheckpointPublication.RunFiles} {checkpoint : Option (PackedTable × UInt64)}

/-- The initial probe selects marked recovery. The same no-follow lookup
then fails for the marker at the heap reached by the selected checkpoint. -/
structure RawSelectedMarkerStatError
    (selected : RawPresentManifestCheckpointPrefix (admitted := admitted) seed fileCalls durable checkpoint) where
  flat : optionalMetadataWith (calls.lookup (directory.file .wal)) seed.afterPending = .ok none seed.afterPending
  metadata : IO.FS.Metadata
  route : optionalMetadataWith (calls.lookup (directory.file .walBoundary)) seed.afterPending =
    .ok (some metadata) seed.afterPending
  sameLookup : fileCalls.stat = calls.lookup
  cause : IO.Error
  reached : heap
  stat : calls.lookup (directory.file .walBoundary) selected.beforeMarker = .ok (.error cause) reached
  notMissing : ∀ name message, cause ≠ .noFileOrDirectory name 2 message
  census : view.descriptors reached = view.descriptors selected.beforeMarker
  frame : MarkedReadCacheFrame seed selected.beforeMarker reached

namespace RawSelectedMarkerStatError

variable {selected : RawPresentManifestCheckpointPrefix (admitted := admitted) seed fileCalls durable checkpoint}
variable (seen : RawSelectedMarkerStatError selected)

theorem rejectsMarker :
    fileCalls.readOptional directory (directory.file .walBoundary) selected.beforeMarker = .error seen.cause seen.reached :=
  fileCalls.readOptionalStatError directory _ (seen.sameLookup.symm ▸ seen.stat) seen.notMissing

/-- The worker has validated the checkpoint and stops before any
marker payload, directory listing, WAL extent or repair callback. -/
theorem stopsMarkedWorker (directoryCalls : MarkedDirectoryReadCalls heap stream)
    (callbacks : AlignedKeeperCacheCallbacks heap) (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit) (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (cache : DiskTable.OpenSyncFiles) :
    calls.recoverMarkedWithCacheRefs fileCalls directoryCalls callbacks seed.directoryRef seed.activeRef seed.pendingRef
      remove write rename bootstrap directory cache seed.afterPending = .error seen.cause seen.reached := by
  simp only [RawOpenAdmissionCallbacks.recoverMarkedWithCacheRefs, recoverSegmentedWalWith, rejectFlatWalWith,
    reopenMarkedBoundedWithCachedExtents, prepareBoundedMarkedFromReaders, Bind.bind, EStateM.bind, seen.flat, seen.route,
    Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte, Pure.pure, EStateM.pure,
    selected.reachesMarker.1, seen.rejectsMarker]

/-- The earlier temporary reads have already been finalized. The
original cache and lock cleanup begins at the failed marker lookup. -/
noncomputable def finalizedAttempt
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed seen.reached)
    (directoryCalls : MarkedDirectoryReadCalls heap stream) (callbacks : AlignedKeeperCacheCallbacks heap)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit) (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap DiskTable)
    (finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner disposal.reached) :
    RawFinalizedOpenAttempt view directory calls init release input entry :=
  RawFinalizedOpenAttempt.ofMarkedRejection (selected.reachesMarker.2.1.trans seen.frame)
    ((congrArg DescriptorInventory.inode seen.census).trans selected.reachesMarker.2.2)
    disposal directoryCalls callbacks remove write rename bootstrap install
    (seen.stopsMarkedWorker directoryCalls callbacks remove write rename bootstrap) finalized

end RawSelectedMarkerStatError

end Alvoki.Storage.DiskSession
