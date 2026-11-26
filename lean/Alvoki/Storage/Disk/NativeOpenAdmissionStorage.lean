import Alvoki.Storage.Disk.NativeRawOpenAdmission

namespace Alvoki.Storage.DiskSession

open System

/-- Carry a scoped frame from the actual open entry to the heap handed
to the held worker. The path and metadata checks return at the entry
heap. The six subsequent callbacks supply their local frames using
the exact lock, directory handle and cache reference allocations. -/
theorem RawOpenAdmissionReport.framesThroughCache
    {heap image : Type} {input : FilePath} {directory : DiskDirectory} {initial : DescriptorInventory}
    {files : LockedFileState image} {admission : CensusOpenAdmissionReports input directory initial files}
    {view : OpenCloseHeapView heap image} {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
    (seen : RawOpenAdmissionReport admission view calls entry) {init : OpenSyncCacheCallbacks heap}
    (seed : OpenSyncCacheAllocations admission.opened view init seen.afterFlock)
    {frame : heap → heap → Prop}
    (compose : ∀ {before middle reached}, frame before middle → frame middle reached → frame before reached)
    (lockOpen : calls.openAppend (directory.file .lock) entry = .ok seen.lock seen.afterAppend →
      frame entry seen.afterAppend)
    (flock : calls.flock seen.lock seen.afterAppend = .ok true seen.afterFlock →
      frame seen.afterAppend seen.afterFlock)
    (openDirectory : init.openDirectory directory.path seen.afterFlock = .ok seed.handle seed.afterOpen →
      frame seen.afterFlock seed.afterOpen)
    (directoryRef : init.newRef (some seed.handle) seed.afterOpen = .ok seed.directoryRef seed.afterDirectory →
      frame seed.afterOpen seed.afterDirectory)
    (activeRef : init.newRef none seed.afterDirectory = .ok seed.activeRef seed.afterActive →
      frame seed.afterDirectory seed.afterActive)
    (pendingRef : init.newRef [] seed.afterActive = .ok seed.pendingRef seed.afterPending →
      frame seed.afterActive seed.afterPending) :
    frame entry seed.afterPending :=
  compose
    (compose (lockOpen seen.appended) (flock seen.acquired))
    (compose (openDirectory seed.rawOpened) (compose (directoryRef seed.directoryAllocated)
      (compose (activeRef seed.activeAllocated) (pendingRef seed.pendingAllocated))))

end Alvoki.Storage.DiskSession
