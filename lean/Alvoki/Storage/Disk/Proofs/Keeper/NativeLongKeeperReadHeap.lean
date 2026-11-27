import Alvoki.Storage.Disk.NativeMarkedCheckpointHeap
import Alvoki.Storage.Disk.Proofs.Keeper.NativePrunedAlignedKeeperCache
import Alvoki.Storage.Disk.Proofs.Keeper.CapturedLongKeeperInstallation

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {vacant : TryLockObserves retry.owners directory (.ok true)} {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {calls : CapturedAlignedCallbacks admission} {reads : CapturedMarkedReadReports admission layout published}
  {heap : Type} {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap} {entry : heap}

private def keeperPrefix (reader : MarkedTemporaryReadCalls heap) (count : Nat) (file : IO.FS.Handle) :
    EStateM IO.Error heap ByteArray :=
  readExactPrefixWith (IO.userError "short or oversized WAL keeper read")
    (reader.readChunk file) count ByteArray.empty

/-- The long branch's selected prefix and observed temporary-handle
release. The production bounded read and its pending routing are proved
separately at the same raw open and chunk returns. -/
def MarkedTemporaryReadCalls.readLongKeeper (reader : MarkedTemporaryReadCalls heap)
    (path : FilePath) (count : Nat) : EStateM IO.Error heap ByteArray :=
  reader.readWith path (keeperPrefix reader count)

structure NativeLongKeeperReadHeap (finish : CapturedLongKeeperFinish calls reads vacant selected)
    (seed : OpenSyncCacheAllocations admission.opened view init entry)
    (reader : MarkedTemporaryReadCalls heap) (before : heap) where
  closed : heap
  entryCensus : view.descriptors before = finish.reader.atOpen
  entryFrame : MarkedReadCacheFrame seed seed.afterPending before
  raw : MarkedTemporaryReadReport (reads := reads) seed reader
    (directory.file (.walSegment layout.keeper.first))
    (finish.reader.duringRead ++ [reads.wal.keeper.calls.slot.closeEvent])
    (keeperPrefix reader layout.keeper.bytes.size) layout.keeper.bytes before closed
  openedCensus : view.descriptors raw.opened = reads.wal.keeper.calls.inventory
  readCensus : view.descriptors raw.finished = finish.reader.afterRead

namespace NativeLongKeeperReadHeap

variable {finish : CapturedLongKeeperFinish calls reads vacant selected}
  {seed : OpenSyncCacheAllocations admission.opened view init entry}
  {reader : MarkedTemporaryReadCalls heap} {before : heap}

/-- The production bounded read uses the same open and prefix report.
The longer measured extent bypasses the supplied remember callback. -/
theorem readsBeforeRelease (seen : NativeLongKeeperReadHeap finish seed reader before)
    (remember : FilePath → IO.FS.Handle → EStateM IO.Error heap Unit) :
    readKeeperWith reader.openRead (fun file count => keeperPrefix reader count file) remember
      (directory.file (.walSegment layout.keeper.first)) layout.keeper.bytes.size
      reads.wal.keeper.calls.metadata.byteSize.toNat before =
      .ok layout.keeper.bytes seen.raw.finished := by
  simp [readKeeperWith, Bind.bind, EStateM.bind, Nat.le_of_lt finish.longer, reads.wal.keeperFits,
    seen.raw.openedRaw, seen.raw.readRaw, Nat.ne_of_lt finish.longer, Pure.pure, EStateM.pure]

structure Released (seen : NativeLongKeeperReadHeap finish seed reader before) : Prop where
  returned : reader.readLongKeeper (directory.file (.walSegment layout.keeper.first))
    layout.keeper.bytes.size before = .ok layout.keeper.bytes seen.closed
  releasedSlot : (view.handle seen.raw.finished seen.raw.file).2.1 = reads.wal.keeper.calls.slot
  retired : (view.descriptors seen.closed).references reads.wal.keeper.calls.slot.description = []
  census : view.descriptors seen.closed = finish.reader.afterRead.afterDrops [reads.wal.keeper.calls.slot.closeEvent]
  ownerLive : admission.owner ∈ (view.descriptors seen.closed).slots
  directoryLive : admission.cached ∈ (view.descriptors seen.closed).slots
  frame : MarkedReadCacheFrame seed before seen.closed
  files : view.files seen.closed = admission.held
  cache : view.cacheAt seen.closed seed.directoryRef seed.activeRef seed.pendingRef = admission.cache
  directoryHandle : view.handle seen.closed seed.handle = (admission.reached, admission.cached, 0)

/-- The observed release removes precisely the read slot. The original
directory and lock are still live in the heap entering authorization. -/
theorem readsAndReleases (seen : NativeLongKeeperReadHeap finish seed reader before) : seen.Released := by
  have handle := Except.ok.inj (seen.raw.sameOpened.symm.trans reads.wal.keeper.calls.opened)
  have slot := seen.raw.sameSlot.trans (congrArg (fun raw : CheckpointOpenHandle => raw.2.1) handle)
  have census : view.descriptors seen.closed =
      finish.reader.afterRead.afterDrops [reads.wal.keeper.calls.slot.closeEvent] := by
    rw [seen.raw.census, handle, ← DescriptorInventory.afterDrops_append]
    rfl
  obtain ⟨_, _, _, _, _, references⟩ := finish.reader.openedKeeper
  have retired : (view.descriptors seen.closed).references reads.wal.keeper.calls.slot.description = [] := by
    rw [census, DescriptorInventory.references_afterDrops, references]
    simp [DescriptorSlot.closeEvent, LockReferenceDrop.removes]
  have atAuthorization := census.trans finish.readAndClose.2
  obtain ⟨returned, frame⟩ := seen.raw.returns
  have original := seed.pendingFiles.trans (seed.activeFiles.trans (seed.directoryFiles.trans seed.openedFiles))
  have cachedHandle : view.handle seen.closed seed.handle = (admission.reached, admission.cached, 0) :=
    (frame.directoryHandle.trans seen.entryFrame.directoryHandle).trans (seed.sameHandle.trans seed.openedHandle)
  refine ⟨returned, slot, retired, census, ?_, ?_, frame, frame.files.trans (seen.entryFrame.files.trans original),
    ?_, cachedHandle⟩
  · rw [atAuthorization]
    exact finish.authorization.lockRetained
  · rw [atAuthorization]
    exact finish.authorization.directoryRetained
  · simp only [OpenCloseHeapView.cacheAt, frame.directoryCell, seen.entryFrame.directoryCell,
      seed.directoryKept, seed.directorySet, frame.activeCell, seen.entryFrame.activeCell,
      seed.activeKept, seed.activeSet, frame.pendingCell, seen.entryFrame.pendingCell, seed.pendingSet,
      Option.map_some, Option.map_none, List.map_nil, cachedHandle, CensusOpenAdmissionReports.cache]

end NativeLongKeeperReadHeap

/-- The first directory barrier starts on the returned read heap after
the observed release. It uses the original cache cell and descriptor. -/
structure NativeLongKeeperAuthorizationHeap {finish : CapturedLongKeeperFinish calls reads vacant selected}
    {seed : OpenSyncCacheAllocations admission.opened view init entry}
    {reader : MarkedTemporaryReadCalls heap} {before : heap}
    (read : NativeLongKeeperReadHeap finish seed reader before) (sync : AlignedKeeperCacheCallbacks heap) where
  reached : heap
  loaded : sync.getDirectory seed.directoryRef read.closed = .ok (some seed.handle) read.closed
  synced : sync.sync seed.handle read.closed = .ok () reached
  files : view.files reached = { admission.held with image := retry.image.syncDirectory }
  census : view.descriptors reached =
    (view.descriptors read.closed).afterDrops finish.prune.afterAuthorization
  cells : KeeperCacheCellsFrame view seed.directoryRef seed.activeRef seed.pendingRef read.closed reached
  handle : view.handle reached seed.handle = view.handle read.closed seed.handle

theorem NativeLongKeeperAuthorizationHeap.returns {finish : CapturedLongKeeperFinish calls reads vacant selected}
    {seed : OpenSyncCacheAllocations admission.opened view init entry}
    {reader : MarkedTemporaryReadCalls heap} {before : heap}
    {read : NativeLongKeeperReadHeap finish seed reader before} {sync : AlignedKeeperCacheCallbacks heap}
    (seen : NativeLongKeeperAuthorizationHeap read sync) :
    sync.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef #[directory.path] read.closed =
      .ok () seen.reached ∧
    view.descriptors seen.reached =
      (finish.reader.afterRead.afterDrops [reads.wal.keeper.calls.slot.closeEvent]).afterDrops
        finish.prune.afterAuthorization ∧
    view.files seen.reached = { admission.held with image := retry.image.syncDirectory } ∧
    view.cacheAt seen.reached seed.directoryRef seed.activeRef seed.pendingRef = admission.cache := by
  have closed := read.readsAndReleases
  have census := congrArg (fun inventory => inventory.afterDrops finish.prune.afterAuthorization) closed.census
  refine ⟨sync.syncsDirectory seen.loaded seen.synced, seen.census.trans census, seen.files, ?_⟩
  simp only [OpenCloseHeapView.cacheAt, seen.cells.directory, seen.cells.active, seen.cells.pending,
    closed.frame.directoryCell, read.entryFrame.directoryCell, seed.directoryKept, seed.directorySet,
    closed.frame.activeCell, read.entryFrame.activeCell, seed.activeKept, seed.activeSet,
    closed.frame.pendingCell, read.entryFrame.pendingCell, seed.pendingSet,
    Option.map_some, Option.map_none, List.map_nil, seen.handle, closed.directoryHandle,
    CensusOpenAdmissionReports.cache]

end Alvoki.Storage.DiskSession
