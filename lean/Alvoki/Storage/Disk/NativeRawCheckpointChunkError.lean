import Alvoki.Storage.Disk.NativeRawCheckpointExtentError

namespace Alvoki.Storage.DiskSession

open System Manifest WalSegmentRepair SyncHandleRouting

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {fileCalls : MarkedTemporaryReadCalls heap}

private abbrev runPath (selected : RawSelectedCheckpointRunStat (admitted := admitted) seed fileCalls) : FilePath :=
  directory.file (.run selected.reads.manifest.header.generation selected.index)

private abbrev beforeRun (selected : RawSelectedCheckpointRunStat (admitted := admitted) seed fileCalls) : heap :=
  selected.reads.atRun selected.index

/-- The failing run passed its extent check and opened the selected
inode. Both chunk requests use the same descriptor, and that
unretained descriptor is released before the worker returns. -/
structure RawCheckpointChunkReadError (selected : RawSelectedCheckpointRunStat (admitted := admitted) seed fileCalls) where
  extent : selected.metadata.byteSize.toNat = selected.stamp.byteCount.toNat
  fits : selected.stamp.byteCount.toNat < USize.size
  openChild : RunChildLookup admission.root
    (renderRunFileName selected.reads.manifest.header.generation selected.index) admission.view
  handle : IO.FS.Handle
  slot : DescriptorSlot
  opened : heap
  afterChunk : heap
  failed : heap
  reached : heap
  openRaw : fileCalls.openRead (runPath selected) (beforeRun selected) = .ok handle opened
  openHandle : view.handle opened handle = (view.descriptors opened, slot, 0)
  identified : (view.descriptors opened).inode slot.description = admission.view.modelObject openChild.child
  beforeOpen : List LockReferenceDrop
  free : ∀ prior ∈ ((view.descriptors (beforeRun selected)).afterDrops beforeOpen).slots, prior.address ≠ slot.address
  fresh : ((view.descriptors (beforeRun selected)).afterDrops beforeOpen).references slot.description = []
  allocated : view.descriptors opened = ((view.descriptors (beforeRun selected)).afterDrops beforeOpen).insert slot free
  bytes : ByteArray
  contents : selected.reads.reads.objectBytes (admission.view.modelObject selected.child.child) = some bytes
  physicalExtent : bytes.size = selected.metadata.byteSize.toNat
  chunk : ByteArray
  firstBytes : chunk = bytes.extract 0 chunk.size
  positive : 0 < chunk.size
  short : chunk.size < selected.stamp.byteCount.toNat
  first : fileCalls.readChunk handle selected.stamp.byteCount.toNat.toUSize opened = .ok chunk afterChunk
  partialHandle : view.handle afterChunk handle = (view.descriptors afterChunk, slot, chunk.size)
  partialCensus : view.descriptors afterChunk = view.descriptors opened
  cause : IO.Error
  second : fileCalls.readChunk handle (selected.stamp.byteCount.toNat - chunk.size).toUSize afterChunk =
    .error cause failed
  failedHandle : (view.handle failed handle).1 = view.descriptors failed ∧
    (view.handle failed handle).2.1 = slot
  failedCensus : view.descriptors failed = view.descriptors opened
  release : dataErrorDropState fileCalls.release handle failed = reached
  releasedCensus : view.descriptors reached = (view.descriptors failed).afterDrops [slot.closeEvent]
  openFrame : MarkedReadCacheFrame seed (beforeRun selected) opened
  firstFrame : MarkedReadCacheFrame seed opened afterChunk
  failedFrame : MarkedReadCacheFrame seed afterChunk failed
  releasedFrame : MarkedReadCacheFrame seed failed reached

namespace RawCheckpointChunkReadError

variable {selected : RawSelectedCheckpointRunStat (admitted := admitted) seed fileCalls}

structure Released (seen : RawCheckpointChunkReadError selected) : Prop where
  returned : fileCalls.runPrefix (runPath selected) selected.stamp.byteCount.toNat (beforeRun selected) =
    .error seen.cause seen.reached
  inode : (view.handle seen.opened seen.handle).1.inode (view.handle seen.opened seen.handle).2.1.description =
    admission.view.modelObject selected.child.child
  bytes : selected.reads.reads.objectBytes (admission.view.modelObject selected.child.child) = some seen.bytes
  extent : seen.bytes.size = selected.stamp.byteCount.toNat
  prefixBytes : seen.chunk = seen.bytes.extract 0 seen.chunk.size
  afterChunk : view.handle seen.afterChunk seen.handle = (view.descriptors seen.opened, seen.slot, seen.chunk.size)
  failedHandle : (view.handle seen.failed seen.handle).1 = view.descriptors seen.opened ∧
    (view.handle seen.failed seen.handle).2.1 = seen.slot
  live : seen.slot ∈ (view.descriptors seen.opened).slots ∧
    seen.slot ∈ (view.descriptors seen.afterChunk).slots ∧ seen.slot ∈ (view.descriptors seen.failed).slots
  census : view.descriptors seen.reached = (view.descriptors (beforeRun selected)).afterDrops
    (seen.beforeOpen ++ [seen.slot.closeEvent])
  retired : (view.descriptors seen.reached).references seen.slot.description = []
  frame : MarkedReadCacheFrame seed (beforeRun selected) seen.reached

theorem releasesSelected (seen : RawCheckpointChunkReadError selected) : seen.Released := by
  have body := readExactPrefixWith_shortThenError (IO.userError checkpointIntegrityMismatch)
    (fileCalls.readChunk seen.handle) seen.positive seen.short seen.first seen.second
  have failed := fileCalls.readWith_error (runPath selected)
    (fun handle => readExactPrefixWith (IO.userError checkpointIntegrityMismatch) (fileCalls.readChunk handle)
      selected.stamp.byteCount.toNat ByteArray.empty) seen.openRaw body
  rw [seen.release] at failed
  have closed := DescriptorInventory.insert_thenClose
    ((view.descriptors (beforeRun selected)).afterDrops seen.beforeOpen) seen.slot seen.free []
  simp only [List.nil_append] at closed
  have census := seen.releasedCensus
  rw [seen.failedCensus, seen.allocated, closed, DescriptorInventory.afterDrops_append] at census
  have retired : (view.descriptors seen.reached).references seen.slot.description = [] := by
    rw [census, ← DescriptorInventory.afterDrops_append, DescriptorInventory.references_afterDrops, seen.fresh]
    rfl
  have bound := selected.child.binds
  rw [selected.child.atRoot, selected.child.atName] at bound
  have sameChild := seen.openChild.child_eq bound
  have live : seen.slot ∈ (view.descriptors seen.opened).slots := by
    rw [seen.allocated]
    exact List.mem_cons_self
  have afterChunk : view.handle seen.afterChunk seen.handle = (view.descriptors seen.opened, seen.slot, seen.chunk.size) := by
    rw [seen.partialHandle, seen.partialCensus]
  have liveAfterChunk : seen.slot ∈ (view.descriptors seen.afterChunk).slots := seen.partialCensus.symm ▸ live
  have liveAtFailure : seen.slot ∈ (view.descriptors seen.failed).slots := seen.failedCensus.symm ▸ live
  refine ⟨failed, ?_, seen.contents, seen.physicalExtent.trans seen.extent, seen.firstBytes, afterChunk,
    ⟨seen.failedHandle.1.trans seen.failedCensus, seen.failedHandle.2⟩,
    ⟨live, liveAfterChunk, liveAtFailure⟩, census, retired,
    ((seen.openFrame.trans seen.firstFrame).trans seen.failedFrame).trans seen.releasedFrame⟩
  rw [seen.openHandle]
  exact seen.identified.trans (congrArg admission.view.modelObject sameChild)

/-- A transient run read error returns after the same descriptor has
closed, before restoration, later runs or WAL recovery. -/
theorem rejects (seen : RawCheckpointChunkReadError selected) :
    readIntegrityCheckpointSized directory (fileCalls.readOptional directory (directory.file .manifest))
      fileCalls.runSize fileCalls.runPrefix seed.afterPending = .error seen.cause seen.reached ∧
    MarkedReadCacheFrame seed seed.afterPending seen.reached ∧
    (view.descriptors seen.reached).inode = admission.reached.inode := by
  have released := seen.releasesSelected
  obtain ⟨earlierFrame, inodes⟩ := selected.reads.frames (Nat.le_refl _)
  have sized := selected.measures
  rw [seen.extent] at sized
  refine ⟨readIntegrityCheckpointSized_rejectsRead directory _ _ _ selected.reads.readsManifest selected.reads.decoded
    selected.within selected.stamped selected.readsEarlier seen.fits sized released.returned,
    earlierFrame.trans released.frame, ?_⟩
  rw [released.census]
  exact inodes

end RawCheckpointChunkReadError

section

variable {admission : CensusOpenAdmissionReports input directory (view.descriptors entry) (view.files entry)}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {release : IO.FS.Handle → heap → heap}
  {selected : RawSelectedCheckpointRunStat (admitted := admitted) seed fileCalls}

/-- Scope the same failed reader with the original cache disposal,
the reported unlock, and final lock-slot drop. -/
noncomputable def RawCheckpointChunkReadError.finalizedAttempt
    (seen : RawCheckpointChunkReadError selected)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed seen.reached)
    (directoryCalls : MarkedDirectoryReadCalls heap stream) (callbacks : AlignedKeeperCacheCallbacks heap)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit) (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap DiskTable)
    (finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner disposal.reached) :
    RawFinalizedOpenAttempt view directory calls init release input entry :=
  selected.reads.finalizedAttempt seen.rejects.1 seen.rejects.2.1 seen.rejects.2.2 disposal
    directoryCalls callbacks remove write rename bootstrap install finalized

end

end Alvoki.Storage.DiskSession
