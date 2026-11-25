import Alvoki.Storage.Disk.NativeBootstrapCacheMutations

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

structure FreshBootstrapCacheCalls (heap : Type) extends BootstrapPendingCalls heap where
  list : FilePath → EStateM IO.Error heap (Array IO.FS.DirEntry)
  readEmpty : FilePath → EStateM IO.Error heap (Option ByteArray)
  metadata : FilePath → EStateM IO.Error heap (Option IO.FS.Metadata)
  rename : FilePath → FilePath → EStateM IO.Error heap Unit

def FreshBootstrapCacheCalls.sync (calls : FreshBootstrapCacheCalls heap) (directory : DiskDirectory)
    (directoryRef : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (paths : Array FilePath) : EStateM IO.Error heap Unit :=
  SyncPathGroup.run (fun name => syncWithHandles directory.path name (calls.readDirectory directoryRef)
    (calls.readPending pending) (calls.setPending pending) (calls.readActive active) calls.openRead calls.fsync) paths

def FreshBootstrapCacheCalls.createPending (calls : FreshBootstrapCacheCalls heap)
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (path : FilePath) : EStateM IO.Error heap Unit := do
  let handle ← calls.create path
  calls.remember pending (pushPending path handle)

def FreshBootstrapCacheCalls.stagePending (calls : FreshBootstrapCacheCalls heap)
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (path : FilePath) (bytes : ByteArray) : EStateM IO.Error heap Unit := do
  let handle ← calls.stage path bytes
  calls.remember pending (pushPending path handle)

def FreshBootstrapCacheCalls.run (calls : FreshBootstrapCacheCalls heap) (directory : DiskDirectory)
    (directoryRef : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) : EStateM IO.Error heap Reopened :=
  bootstrapSegmentedWith directory calls.list calls.readEmpty calls.metadata
    (calls.createPending pending) (calls.stagePending pending)
    (calls.sync directory directoryRef active pending) calls.rename

/-- Both successful keeper routes continue with the same zero-marker publication. -/
def FreshBootstrapCacheCalls.publishZeroMarker (calls : FreshBootstrapCacheCalls heap) (directory : DiskDirectory)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) : EStateM IO.Error heap Reopened := do
  Publication.run (Publication.performReplacement
    (calls.stagePending pending · (WAL.Boundary.encode 0)) (calls.sync directory cached active pending) calls.rename
    (directory.file .stagedWalBoundary) directory.path (fun _ => directory.file .walBoundary) #[])
  pure ⟨.empty, 0, 0, 0⟩

/-- The two cache cells unrelated to the pending write keep their contents
across a reported local callback. This frame speaks only about those cells. -/
structure FreshBootstrapCacheFrame (view : OpenCloseHeapView heap image)
    (directoryRef : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (before after : heap) : Prop where
  directory : view.directory after directoryRef = view.directory before directoryRef
  activeUnchanged : view.active after active = view.active before active

private theorem FreshBootstrapCacheFrame.trans
    (first : FreshBootstrapCacheFrame view directoryRef active before middle)
    (last : FreshBootstrapCacheFrame view directoryRef active middle after) :
    FreshBootstrapCacheFrame view directoryRef active before after :=
  ⟨last.directory.trans first.directory, last.activeUnchanged.trans first.activeUnchanged⟩

structure BootstrapPendingObservation.CacheFrames
    (file : BootstrapPendingObservation view calls directory kind pending expected entry)
    (directoryRef : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle))) : Prop where
  openFile : FreshBootstrapCacheFrame view directoryRef active entry file.produced
  remember : FreshBootstrapCacheFrame view directoryRef active file.produced file.recorded
  consume : FreshBootstrapCacheFrame view directoryRef active file.recorded file.consumed
  syncFile : FreshBootstrapCacheFrame view directoryRef active file.consumed file.reached

private theorem BootstrapPendingObservation.CacheFrames.preserves
    {view : OpenCloseHeapView heap image} {calls : BootstrapPendingCalls heap}
    {file : BootstrapPendingObservation view calls directory kind pending expected entry}
    (frames : BootstrapPendingObservation.CacheFrames file directoryRef active) :
    FreshBootstrapCacheFrame view directoryRef active entry file.reached :=
  ((frames.openFile.trans frames.remember).trans frames.consume).trans frames.syncFile

variable {heap image : Type} {directory : DiskDirectory} {initial : DescriptorInventory}
  {owner cached : DescriptorSlot} {files : LockedFileState image} {namespaceView : DirectoryReadNamespace}
  {root : DeviceInode} {opened : DirectoryCacheOpenReports directory initial owner cached files namespaceView root}
  {view : OpenCloseHeapView heap image} {init : OpenSyncCacheCallbacks heap} {entry : heap}

/-- Both bootstrap directory barriers use the original raw directory
handle and the corresponding held slot. Their reports preserve just the
opened cache cells, with file and descriptor state supplied separately. -/
structure FreshBootstrapDirectoryBarrier
    (seed : OpenSyncCacheAllocations opened view init entry)
    (calls : FreshBootstrapCacheCalls heap) (before : heap) where
  reached : heap
  read : calls.readDirectory seed.directoryRef before = .ok (some seed.handle) before
  rawHandle : view.handle before seed.handle = (view.descriptors before, cached, 0)
  live : cached ∈ (view.descriptors before).slots
  sameInode : (view.descriptors before).inode cached.description = (initial.insert cached opened.free).inode cached.description
  synced : calls.fsync seed.handle before = .ok () reached
  frame : FreshBootstrapCacheFrame view seed.directoryRef seed.activeRef before reached
  pending : view.pending reached seed.pendingRef = view.pending before seed.pendingRef

theorem FreshBootstrapDirectoryBarrier.returns
    {seed : OpenSyncCacheAllocations opened view init entry} {calls : FreshBootstrapCacheCalls heap}
    (report : FreshBootstrapDirectoryBarrier seed calls before) :
    calls.sync directory seed.directoryRef seed.activeRef seed.pendingRef #[directory.path] before = .ok () report.reached := by
  unfold FreshBootstrapCacheCalls.sync
  rw [SyncPathGroup.run_single]
  simp [syncWithHandles, Bind.bind, EStateM.bind, report.read, report.synced, Pure.pure, EStateM.pure]

/-- The issued directory handle identifies the same rooted inode selected
by the original cache allocation, in the descriptor report at this call. -/
theorem FreshBootstrapDirectoryBarrier.selectsRoot
    {seed : OpenSyncCacheAllocations opened view init entry} {calls : FreshBootstrapCacheCalls heap}
    (report : FreshBootstrapDirectoryBarrier seed calls before) :
    (view.handle before seed.handle).2.1 = cached ∧ cached ∈ (view.descriptors before).slots ∧
    namespaceView.modelObject root = (view.descriptors before).inode cached.description := by
  obtain ⟨_, _, _, _, object, _⟩ := opened.captures
  exact ⟨congrArg (fun handle : CheckpointOpenHandle => handle.2.1) report.rawHandle, report.live,
    object.trans report.sameInode.symm⟩

/-- The raw marker suffix starts on the heap returned by the keeper's
directory sync. It uses only the original initialized cache cells. -/
structure BootstrapMarkerPublicationHeap
    (seed : OpenSyncCacheAllocations opened view init entry) (calls : FreshBootstrapCacheCalls heap)
    (before : heap) where
  markerHandle : CheckpointOpenHandle
  marker : BootstrapPendingObservation view calls.toBootstrapPendingCalls directory .marker seed.pendingRef markerHandle before
  markerOK : marker.result = .ok ()
  markerFrames : marker.CacheFrames seed.directoryRef seed.activeRef
  afterRename : heap
  renamed : calls.rename (directory.file .stagedWalBoundary) (directory.file .walBoundary) marker.reached = .ok () afterRename
  renameFrame : FreshBootstrapCacheFrame view seed.directoryRef seed.activeRef marker.reached afterRename
  renamePending : view.pending afterRename seed.pendingRef = view.pending marker.reached seed.pendingRef
  markerDirectory : FreshBootstrapDirectoryBarrier seed calls afterRename

theorem BootstrapMarkerPublicationHeap.returns
    {seed : OpenSyncCacheAllocations opened view init entry} {calls : FreshBootstrapCacheCalls heap}
    {before : heap} (seen : BootstrapMarkerPublicationHeap seed calls before) :
    calls.publishZeroMarker directory seed.directoryRef seed.activeRef seed.pendingRef before =
      .ok ⟨.empty, 0, 0, 0⟩ seen.markerDirectory.reached ∧
    FreshBootstrapCacheFrame view seed.directoryRef seed.activeRef before seen.markerDirectory.reached ∧
    view.pending seen.markerDirectory.reached seed.pendingRef = [] := by
  obtain ⟨_, _, cache, _, _, _, references, path, _, _, _, _, _, _, _, _, _⟩ := seed.installs
  obtain ⟨_, staged, synced, _, _, consumed, _⟩ := seen.marker.returns cache references path
  rw [seen.markerOK] at synced
  have stageReturn : calls.stagePending seed.pendingRef (directory.file .stagedWalBoundary) (WAL.Boundary.encode 0)
      before = .ok () seen.marker.recorded := staged
  have fileReturn : calls.sync directory seed.directoryRef seed.activeRef seed.pendingRef
      #[directory.file .stagedWalBoundary] seen.marker.recorded = .ok () seen.marker.reached := synced
  have frame := (seen.markerFrames.preserves.trans seen.renameFrame).trans seen.markerDirectory.frame
  refine ⟨?_, frame, seen.markerDirectory.pending.trans (seen.renamePending.trans consumed)⟩
  unfold FreshBootstrapCacheCalls.publishZeroMarker
  rw [Publication.run_performReplacement]
  simp [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, stageReturn, fileReturn, seen.renamed,
    seen.markerDirectory.returns]

/-- The fresh markerless path prepares and creates its keeper and returns
from the keeper's two syncs on the original cache. -/
structure FreshBootstrapKeeperChronology
    (seed : OpenSyncCacheAllocations opened view init entry) (calls : FreshBootstrapCacheCalls heap) where
  entries : Array IO.FS.DirEntry
  afterList : heap
  afterEmpty : heap
  prepared : heap
  checked : calls.list directory.path seed.afterPending = .ok entries afterList
  clear : entries.any (fun item => conflictsWithBootstrap item.fileName) = false
  empty : calls.readEmpty (directory.file (.walSegment 0)) afterList = .ok none afterEmpty
  absentStage : calls.metadata (directory.file .stagedWalBoundary) afterEmpty = .ok none prepared
  listingFrame : FreshBootstrapCacheFrame view seed.directoryRef seed.activeRef seed.afterPending afterList
  emptyFrame : FreshBootstrapCacheFrame view seed.directoryRef seed.activeRef afterList afterEmpty
  stageProbeFrame : FreshBootstrapCacheFrame view seed.directoryRef seed.activeRef afterEmpty prepared
  keeperHandle : CheckpointOpenHandle
  keeper : BootstrapPendingObservation view calls.toBootstrapPendingCalls directory .keeper seed.pendingRef keeperHandle prepared
  keeperOK : keeper.result = .ok ()
  keeperFrames : keeper.CacheFrames seed.directoryRef seed.activeRef
  keeperDirectory : FreshBootstrapDirectoryBarrier seed calls keeper.reached

namespace FreshBootstrapKeeperChronology

variable {seed : OpenSyncCacheAllocations opened view init entry} {calls : FreshBootstrapCacheCalls heap}

theorem prepares (seen : FreshBootstrapKeeperChronology seed calls) :
    prepareBootstrapWith directory calls.list calls.readEmpty calls.metadata seed.afterPending = .ok none seen.prepared := by
  simp [prepareBootstrapWith, Bind.bind, EStateM.bind, seen.checked, seen.clear, seen.empty, seen.absentStage,
    Pure.pure, EStateM.pure]

/-- The checked missing keeper takes the create branch and reaches the
cached directory sync's return before marker publication begins. -/
theorem rotates (seen : FreshBootstrapKeeperChronology seed calls) :
    WalSegmentRotation.runAt directory 0 (fun _ => EStateM.pure none) (calls.createPending seed.pendingRef)
      (fun path => calls.sync directory seed.directoryRef seed.activeRef seed.pendingRef #[path]) seen.prepared =
      .ok () seen.keeperDirectory.reached := by
  obtain ⟨_, _, cache, _, _, _, references, path, _⟩ := seed.installs
  obtain ⟨_, keeperCreated, keeperSynced, _, _, _, _⟩ := seen.keeper.returns cache references path
  rw [seen.keeperOK] at keeperSynced
  have created : calls.createPending seed.pendingRef (directory.file (.walSegment 0)) seen.prepared =
      .ok () seen.keeper.recorded := keeperCreated
  have keeperSync : calls.sync directory seed.directoryRef seed.activeRef seed.pendingRef
      #[directory.file (.walSegment 0)] seen.keeper.recorded = .ok () seen.keeper.reached := keeperSynced
  rw [WalSegmentRotation.runAt_fileEffects]
  simp [WalSegmentRotation.observeSuccessorWith, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
    created, keeperSync, seen.keeperDirectory.returns]

end FreshBootstrapKeeperChronology

/-- The successful fresh markerless path continues from the keeper's
reached heap through marker publication on the same cache references. -/
structure FreshBootstrapCacheChronology
    (seed : OpenSyncCacheAllocations opened view init entry) (calls : FreshBootstrapCacheCalls heap)
    extends FreshBootstrapKeeperChronology seed calls where
  markerHandle : CheckpointOpenHandle
  marker : BootstrapPendingObservation view calls.toBootstrapPendingCalls directory .marker seed.pendingRef
    markerHandle keeperDirectory.reached
  markerOK : marker.result = .ok ()
  markerFrames : marker.CacheFrames seed.directoryRef seed.activeRef
  afterRename : heap
  renamed : calls.rename (directory.file .stagedWalBoundary) (directory.file .walBoundary) marker.reached = .ok () afterRename
  renameFrame : FreshBootstrapCacheFrame view seed.directoryRef seed.activeRef marker.reached afterRename
  renamePending : view.pending afterRename seed.pendingRef = view.pending marker.reached seed.pendingRef
  markerDirectory : FreshBootstrapDirectoryBarrier seed calls afterRename

namespace FreshBootstrapCacheChronology

variable {seed : OpenSyncCacheAllocations opened view init entry} {calls : FreshBootstrapCacheCalls heap}

def markerPublication (seen : FreshBootstrapCacheChronology seed calls) :
    BootstrapMarkerPublicationHeap seed calls seen.keeperDirectory.reached :=
  ⟨seen.markerHandle, seen.marker, seen.markerOK, seen.markerFrames, seen.afterRename, seen.renamed,
    seen.renameFrame, seen.renamePending, seen.markerDirectory⟩

/-- The raw fresh worker returns on the exact success heap of the last
barrier, with the same raw directory cell and empty active and pending
cells. The initialized synchronization record exposes the same native
create, stage and fsync schedules throughout. -/
theorem returns (seen : FreshBootstrapCacheChronology seed calls) :
    ∃ (action : IO DiskTable.OpenSyncFiles)
      (assemble : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles) (cache : DiskTable.OpenSyncFiles),
      DiskTable.OpenSyncFiles.IsOpenAction directory.path action ∧
      action = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) assemble ∧
      openSyncFilesWith (init.openDirectory directory.path) init.newRef init.newRef init.newRef
        assemble entry = .ok cache seed.afterPending ∧
      cache.UsesBootstrapCacheSchedules directory seed.activeRef seed.pendingRef seed.directoryRef ∧
      calls.run directory seed.directoryRef seed.activeRef seed.pendingRef seed.afterPending =
        .ok ⟨.empty, 0, 0, 0⟩ seen.markerDirectory.reached ∧
      view.directory seen.markerDirectory.reached seed.directoryRef = some seed.handle ∧
      view.active seen.markerDirectory.reached seed.activeRef = none ∧
      view.pending seen.markerDirectory.reached seed.pendingRef = [] := by
  obtain ⟨action, assemble, cache, native, source, allocated, references, path, loaded, activeEmpty,
    _, _, _, _, _, _, _, _⟩ := seed.installs
  obtain ⟨published, markerFrame, pending⟩ := seen.markerPublication.returns
  have guardsFrame := (seen.listingFrame.trans seen.emptyFrame).trans seen.stageProbeFrame
  have keeperFrame := (guardsFrame.trans seen.keeperFrames.preserves).trans seen.keeperDirectory.frame
  have final := keeperFrame.trans markerFrame
  refine ⟨action, assemble, cache, native, source, allocated, cache.bootstrapCacheSchedules references path, ?_, final.directory.trans loaded,
    final.activeUnchanged.trans activeEmpty, pending⟩
  have rawPublication : calls.publishZeroMarker directory seed.directoryRef seed.activeRef seed.pendingRef
      seen.keeperDirectory.reached = .ok ⟨.empty, 0, 0, 0⟩ seen.markerDirectory.reached := published
  simp only [FreshBootstrapCacheCalls.run, bootstrapSegmentedWith, bootstrapEmptyWith,
    Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, seen.toFreshBootstrapKeeperChronology.prepares,
    seen.toFreshBootstrapKeeperChronology.rotates]
  exact rawPublication

end FreshBootstrapCacheChronology

end Alvoki.Storage.DiskSession
