import Alvoki.Storage.Disk.CachedWalMarkerOpenFailure
import Alvoki.Storage.Disk.NativeRawCheckpointDigestError
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

/-- The selected marker's observed payload is the input rejected by
the decoder after the accepted physical checkpoint reads. -/
structure RawSelectedMarkerDecodeError
    (selected : RawPresentManifestCheckpointPrefix (admitted := admitted) seed fileCalls durable checkpoint)
    extends RawPresentManifestMarkerRead selected where
  message : String
  invalid : WAL.Boundary.decode bytes = .error message

namespace RawSelectedMarkerDecodeError

variable {selected : RawPresentManifestCheckpointPrefix (admitted := admitted) seed fileCalls durable checkpoint}
variable (seen : RawSelectedMarkerDecodeError selected)

/-- The byte array returned by the actual optional reader is the one
from the selected inode. Its temporary description has been retired. -/
theorem readsRejectedBytes :
    fileCalls.readOptional directory (directory.file .walBoundary) selected.beforeMarker =
      .ok (some seen.bytes) seen.afterMarker ∧
    (view.files entry).image.directory.active.walBoundary = some seen.bytes ∧
    selected.reads.objectBytes (admission.view.modelObject seen.marker.object) = some seen.bytes ∧
    (view.descriptors seen.afterMarker).references seen.marker.calls.slot.description = [] :=
  ⟨seen.toRawPresentManifestMarkerRead.reachesDecoder.2.1, seen.bound, seen.marker.contents,
    (seen.read.censusAfter seen.custody).2.1⟩

/-- The raw marked worker returns the real decoder message and skips
the listing and every WAL extent or repair operation. -/
theorem stopsMarkedWorker (directoryCalls : MarkedDirectoryReadCalls heap stream)
    (callbacks : AlignedKeeperCacheCallbacks heap) (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit) (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (cache : DiskTable.OpenSyncFiles) :
    calls.recoverMarkedWithCacheRefs fileCalls directoryCalls callbacks seed.directoryRef seed.activeRef seed.pendingRef
      remove write rename bootstrap directory cache seed.afterPending = .error (IO.userError seen.message) seen.afterMarker := by
  obtain ⟨loaded, marker, _⟩ := seen.toRawPresentManifestMarkerRead.reachesDecoder
  let observed : CachedWalMarkerRead directory (fileCalls.readOptional directory) fileCalls.runSize fileCalls.runPrefix
      seed.afterPending seen.afterMarker := ⟨checkpoint, selected.beforeMarker, loaded, seen.bytes, marker⟩
  have rejected := observed.reopen_decodeError directoryCalls.run (MarkedWalExtentReports.inspect fileCalls)
    fileCalls.seal ((callbacks.withFileReads fileCalls).readKeeper seed.pendingRef) remove write
    ((callbacks.withFileReads fileCalls).syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef) rename
    (message := seen.message) seen.invalid
  simp only [RawOpenAdmissionCallbacks.recoverMarkedWithCacheRefs, recoverSegmentedWalWith, rejectFlatWalWith,
    Bind.bind, EStateM.bind, seen.flat, seen.route, Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
    ↓reduceIte, Pure.pure, EStateM.pure, rejected]

/-- The same public read-only failure model enters the cache drop,
unlock, and final lock drop at the heap reached by the marker read. -/
noncomputable def finalizedAttempt
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed seen.afterMarker)
    (directoryCalls : MarkedDirectoryReadCalls heap stream) (callbacks : AlignedKeeperCacheCallbacks heap)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit) (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap DiskTable)
    (finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner disposal.reached) :
    RawFinalizedOpenAttempt view directory calls init release input entry :=
  RawFinalizedOpenAttempt.ofMarkedRejection seen.toRawPresentManifestMarkerRead.reachesDecoder.2.2.1
    seen.toRawPresentManifestMarkerRead.reachesDecoder.2.2.2
    disposal directoryCalls callbacks remove write rename bootstrap install
    (seen.stopsMarkedWorker directoryCalls callbacks remove write rename bootstrap) finalized

end RawSelectedMarkerDecodeError

end Alvoki.Storage.DiskSession
