import Alvoki.Storage.Disk.Proofs.Native.Open.NativeRawOpenAdmission

namespace Alvoki.Storage.DiskSession

open System

/-- Frames at the actual lock, directory and cache callbacks shared by
successful and failed held opens. -/
structure RawOpenAdmissionReport.CacheFrames
    {heap image : Type} {input : FilePath} {directory : DiskDirectory} {initial : DescriptorInventory}
    {files : LockedFileState image} {admission : CensusOpenAdmissionReports input directory initial files}
    {view : OpenCloseHeapView heap image} {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
    (seen : RawOpenAdmissionReport admission view calls entry) {init : OpenSyncCacheCallbacks heap}
    (seed : OpenSyncCacheAllocations admission.opened view init seen.afterFlock)
    (frame : heap → heap → Prop) : Prop where
  lockOpen : calls.openAppend (directory.file .lock) entry = .ok seen.lock seen.afterAppend →
    frame entry seen.afterAppend
  flock : calls.flock seen.lock seen.afterAppend = .ok true seen.afterFlock →
    frame seen.afterAppend seen.afterFlock
  openDirectory : init.openDirectory directory.path seen.afterFlock = .ok seed.handle seed.afterOpen →
    frame seen.afterFlock seed.afterOpen
  directoryRef : init.newRef (some seed.handle) seed.afterOpen = .ok seed.directoryRef seed.afterDirectory →
    frame seed.afterOpen seed.afterDirectory
  activeRef : init.newRef none seed.afterDirectory = .ok seed.activeRef seed.afterActive →
    frame seed.afterDirectory seed.afterActive
  pendingRef : init.newRef [] seed.afterActive = .ok seed.pendingRef seed.afterPending →
    frame seed.afterActive seed.afterPending

/-- Carry those frames to the heap handed to the held worker. The
path and metadata checks return at the entry heap. -/
theorem RawOpenAdmissionReport.framesThroughCache
    {heap image : Type} {input : FilePath} {directory : DiskDirectory} {initial : DescriptorInventory}
    {files : LockedFileState image} {admission : CensusOpenAdmissionReports input directory initial files}
    {view : OpenCloseHeapView heap image} {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
    (seen : RawOpenAdmissionReport admission view calls entry) {init : OpenSyncCacheCallbacks heap}
    (seed : OpenSyncCacheAllocations admission.opened view init seen.afterFlock)
    {frame : heap → heap → Prop}
    (compose : ∀ {before middle reached}, frame before middle → frame middle reached → frame before reached)
    (effects : seen.CacheFrames seed frame) :
    frame entry seed.afterPending :=
  compose
    (compose (effects.lockOpen seen.appended) (effects.flock seen.acquired))
    (compose (effects.openDirectory seed.rawOpened) (compose (effects.directoryRef seed.directoryAllocated)
      (compose (effects.activeRef seed.activeAllocated) (effects.pendingRef seed.pendingAllocated))))

end Alvoki.Storage.DiskSession
