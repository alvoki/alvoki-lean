import Alvoki.Storage.Disk.Proofs.Recovery.NativeFinalizedOpenRetries
import Alvoki.Storage.Disk.Proofs.Recovery.NativeRawAbsentManifestListing

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory} {entry : heap}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {release : IO.FS.Handle → heap → heap}
  {admission : CensusOpenAdmissionReports input directory (view.descriptors entry) (view.files entry)}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {fileCalls : MarkedTemporaryReadCalls heap}
  {markerPrefix : RawAbsentManifestMarkerPrefix (admitted := admitted) seed fileCalls}
  {directoryCalls : MarkedDirectoryReadCalls heap stream} {slotOf : heap → stream → DescriptorSlot}

/-- A reported failed listing supplies the complete next retry attempt.
The fixed selected reader and stream determine the error and inode
frame. Both observed scope drops feed the same caller-visible heap. -/
noncomputable def RawMarkedListingScanFailure.finalizedAttempt
    (seen : RawMarkedListingScanFailure (admitted := admitted) seed directoryCalls slotOf markerPrefix.atScan)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed seen.reached)
    (callbacks : AlignedKeeperCacheCallbacks heap) (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap DiskTable)
    (finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner disposal.reached) :
    RawFinalizedOpenAttempt view directory calls init release input entry where
  admission := admission
  admitted := admitted
  seed := seed
  beforeCleanup := seen.reached
  disposed := disposal
  recover := fun resolved lock cache =>
    calls.recoverMarkedWithCacheRefs fileCalls directoryCalls callbacks seed.directoryRef seed.activeRef seed.pendingRef
      remove write rename bootstrap resolved cache >>= install resolved lock cache
  cause := seen.cause
  rejected := (seen.returnsAbsentManifest disposal callbacks remove write rename bootstrap install).1
  workerInodes := by
    obtain ⟨_, _, listingCensus⟩ := seen.sameStream
    obtain ⟨_, _, _, _, _, markerCensus, _⟩ := markerPrefix.readsSelected
    rw [listingCensus]
    change (view.descriptors markerPrefix.atScan).inode = (view.descriptors entry).inode
    rw [markerCensus]
    rfl
  finalized := finalized

end Alvoki.Storage.DiskSession
