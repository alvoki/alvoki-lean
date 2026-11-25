import Alvoki.Storage.Disk.NativeMarkedCheckpointHeap

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting

variable {heap : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {seed : OpenSyncCacheAllocations admission.opened view init entry}
  {fileCalls : MarkedTemporaryReadCalls heap} {path : FilePath} {name : String}
  {selected : RunChildLookup admission.root name admission.view} {count : Nat} {before : heap}

/-- Both requests use a temporary handle for the selected child.
The observed scope drop follows the failing remainder request. -/
structure RawTemporaryChunkReadFailure
    (seed : OpenSyncCacheAllocations admission.opened view init entry) (fileCalls : MarkedTemporaryReadCalls heap)
    (path : FilePath) {name : String} (selected : RunChildLookup admission.root name admission.view)
    (count : Nat) (before : heap) where
  openChild : RunChildLookup admission.root name admission.view
  handle : IO.FS.Handle
  slot : DescriptorSlot
  opened : heap
  afterChunk : heap
  failed : heap
  reached : heap
  openRaw : fileCalls.openRead path before = .ok handle opened
  openHandle : view.handle opened handle = (view.descriptors opened, slot, 0)
  identified : (view.descriptors opened).inode slot.description = admission.view.modelObject openChild.child
  beforeOpen : List LockReferenceDrop
  free : ∀ prior ∈ ((view.descriptors before).afterDrops beforeOpen).slots, prior.address ≠ slot.address
  fresh : ((view.descriptors before).afterDrops beforeOpen).references slot.description = []
  allocated : view.descriptors opened = ((view.descriptors before).afterDrops beforeOpen).insert slot free
  bytes : ByteArray
  chunk : ByteArray
  firstBytes : chunk = bytes.extract 0 chunk.size
  positive : 0 < chunk.size
  short : chunk.size < count
  first : fileCalls.readChunk handle count.toUSize opened = .ok chunk afterChunk
  partialHandle : view.handle afterChunk handle = (view.descriptors afterChunk, slot, chunk.size)
  partialCensus : view.descriptors afterChunk = view.descriptors opened
  cause : IO.Error
  second : fileCalls.readChunk handle (count - chunk.size).toUSize afterChunk =
    .error cause failed
  failedHandle : (view.handle failed handle).1 = view.descriptors failed ∧
    (view.handle failed handle).2.1 = slot
  failedCensus : view.descriptors failed = view.descriptors opened
  release : dataErrorDropState fileCalls.release handle failed = reached
  releasedCensus : view.descriptors reached = (view.descriptors failed).afterDrops [slot.closeEvent]
  openFrame : MarkedReadCacheFrame seed before opened
  firstFrame : MarkedReadCacheFrame seed opened afterChunk
  failedFrame : MarkedReadCacheFrame seed afterChunk failed
  releasedFrame : MarkedReadCacheFrame seed failed reached

namespace RawTemporaryChunkReadFailure

variable (seen : RawTemporaryChunkReadFailure seed fileCalls path selected count before)

structure Released : Prop where
  inode : (view.handle seen.opened seen.handle).1.inode (view.handle seen.opened seen.handle).2.1.description =
    admission.view.modelObject selected.child
  afterChunk : view.handle seen.afterChunk seen.handle = (view.descriptors seen.opened, seen.slot, seen.chunk.size)
  failedHandle : (view.handle seen.failed seen.handle).1 = view.descriptors seen.opened ∧
    (view.handle seen.failed seen.handle).2.1 = seen.slot
  live : seen.slot ∈ (view.descriptors seen.opened).slots ∧
    seen.slot ∈ (view.descriptors seen.afterChunk).slots ∧ seen.slot ∈ (view.descriptors seen.failed).slots
  census : view.descriptors seen.reached = (view.descriptors before).afterDrops
    (seen.beforeOpen ++ [seen.slot.closeEvent])
  retired : (view.descriptors seen.reached).references seen.slot.description = []
  frame : MarkedReadCacheFrame seed before seen.reached

/-- The same child and slot remain selected across both chunk callbacks.
The reported close retires the temporary description. -/
theorem releases : seen.Released := by
  have closed := DescriptorInventory.insert_thenClose
    ((view.descriptors before).afterDrops seen.beforeOpen) seen.slot seen.free []
  simp only [List.nil_append] at closed
  have census := seen.releasedCensus
  rw [seen.failedCensus, seen.allocated, closed, DescriptorInventory.afterDrops_append] at census
  have retired : (view.descriptors seen.reached).references seen.slot.description = [] := by
    rw [census, ← DescriptorInventory.afterDrops_append, DescriptorInventory.references_afterDrops, seen.fresh]
    rfl
  have bound := selected.binds
  rw [selected.atRoot, selected.atName] at bound
  have sameChild := seen.openChild.child_eq bound
  have live : seen.slot ∈ (view.descriptors seen.opened).slots := by
    rw [seen.allocated]
    exact List.mem_cons_self
  have afterChunk : view.handle seen.afterChunk seen.handle = (view.descriptors seen.opened, seen.slot, seen.chunk.size) := by
    rw [seen.partialHandle, seen.partialCensus]
  have liveAfterChunk : seen.slot ∈ (view.descriptors seen.afterChunk).slots := seen.partialCensus.symm ▸ live
  have liveAtFailure : seen.slot ∈ (view.descriptors seen.failed).slots := seen.failedCensus.symm ▸ live
  refine ⟨?_, afterChunk, ⟨seen.failedHandle.1.trans seen.failedCensus, seen.failedHandle.2⟩,
    ⟨live, liveAfterChunk, liveAtFailure⟩, census, retired,
    ((seen.openFrame.trans seen.firstFrame).trans seen.failedFrame).trans seen.releasedFrame⟩
  rw [seen.openHandle]
  exact seen.identified.trans (congrArg admission.view.modelObject sameChild)

end RawTemporaryChunkReadFailure

end Alvoki.Storage.DiskSession
