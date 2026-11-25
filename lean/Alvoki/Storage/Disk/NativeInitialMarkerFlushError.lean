import Alvoki.Storage.Disk.BootstrapMarkerFlushError
import Alvoki.Storage.Disk.NativeBootstrapMarkerCollision
import Alvoki.Storage.Disk.NativeOpenErrorLockFinalization
import Alvoki.Storage.Disk.NativeRawRecoveryReturn
import Alvoki.Storage.Disk.NativeReusedBootstrapKeeperHeap

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

private abbrev markerBytes := WAL.Boundary.encode 0

variable {heap : Type} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {fileCalls : BootstrapOpenCalls (Cache CheckpointOpenHandle) directory before}
  {captured : BootstrapCacheOpen fileCalls.toBootstrapAdmissionCalls} {listed : BootstrapCheckedListing captured}
  {selected : BootstrapReusedZeroKeeper listed} {source : BootstrapMarkerFlushError (.reused selected)}
  {view : OpenCloseHeapView heap WalSegmentRotation.State} {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {seed : OpenSyncCacheAllocations captured.opened view init entry} {bootstrap : FreshBootstrapCacheCalls heap}
  {guards : ReusedBootstrapKeeperGuards selected seed bootstrap} {keeper : ReusedBootstrapKeeperHeap guards}

/-- The raw marker stage after the reported reused-keeper barriers.
Each file action is related to the corresponding physical failure report
at its reached heap, including the unretained descriptor's finalizer. -/
structure RawBootstrapMarkerFlushError (keeper : ReusedBootstrapKeeperHeap guards)
    (source : BootstrapMarkerFlushError (.reused selected)) where
  calls : BootstrapMarkerStageCalls heap
  drop : IO.FS.Handle → EStateM IO.Error heap Unit
  names : heap → DirectoryReadNamespace
  handle : IO.FS.Handle
  opened : heap
  written : heap
  stopped : heap
  reached : heap
  stage : bootstrap.stage (directory.file .stagedWalBoundary) markerBytes =
    writeFreshStagedWith calls.tryCreate (removeStaleStagingWith calls.metadata calls.unlink) calls.create
      (fun file bytes => withDataErrorDrop drop file (calls.write file bytes))
      (fun file => withDataErrorDrop drop file (calls.flush file)) (directory.file .stagedWalBoundary) markerBytes
  created : calls.tryCreate (directory.file .stagedWalBoundary) keeper.directoryBarrier.reached = .ok (.ok handle) opened
  openProjection : BootstrapFileProjection.result view keeper.inodes (fun reached => Except.map (view.handle reached))
      (calls.tryCreate (directory.file .stagedWalBoundary) keeper.directoryBarrier.reached) =
    source.tryCreate (directory.file .stagedWalBoundary)
      (BootstrapFileProjection.atHeap view keeper.inodes keeper.directoryBarrier.reached)
  wrote : calls.write handle markerBytes opened = .ok () written
  writeProjection : BootstrapFileProjection.result view keeper.inodes (fun _ result => result)
      (calls.write handle markerBytes opened) =
    source.write (view.handle opened handle) markerBytes (BootstrapFileProjection.atHeap view keeper.inodes opened)
  keptAtFlush : view.handle written handle = view.handle opened handle
  atFlush : view.descriptors written = source.inventory.afterDrops source.beforeFlush
  flushed : calls.flush handle written = .error source.cause stopped
  flushProjection : BootstrapFileProjection.result view keeper.inodes (fun _ result => result)
      (calls.flush handle written) =
    source.flush (view.handle written handle) (BootstrapFileProjection.atHeap view keeper.inodes written)
  sameSlotAtDrop : view.handle stopped handle = view.handle written handle
  atDrop : view.descriptors stopped = view.descriptors written
  dropped : drop handle stopped = match source.dropStatus with
    | .ok () => .ok () reached
    | .error error => .error error reached
  dropProjection : BootstrapFileProjection.result view keeper.inodes (fun _ result => result) (drop handle stopped) =
    source.drop (view.handle stopped handle) (BootstrapFileProjection.atHeap view keeper.inodes stopped)
  finalCensus : view.descriptors reached = (view.descriptors stopped).afterDrops [source.slot.closeEvent]
  finalNames : names reached = source.reachedView
  pending : view.pending reached seed.pendingRef = []
  active : view.active reached seed.activeRef = none
  directoryCell : view.directory reached seed.directoryRef = some seed.handle
  directoryHandle : view.handle reached seed.handle = view.handle keeper.directoryBarrier.reached seed.handle
  owners : (view.files reached).owners = (view.files keeper.directoryBarrier.reached).owners

namespace RawBootstrapMarkerFlushError

variable (seen : RawBootstrapMarkerFlushError keeper source)

private theorem sameOpened {handle : CheckpointOpenHandle} {reached : BootstrapFileProjection}
    (reported : source.tryCreate (directory.file .stagedWalBoundary)
        (⟨before.image.metadata.syncDirectory, .durable⟩, (BootstrapZeroKeeperRoute.reused selected).settledImage) =
      .ok (.ok handle) reached) : handle = source.handle ∧ reached = source.afterOpen := by
  cases source.opening with
  | fresh opened =>
    have equal := EStateM.Result.ok.inj (reported.symm.trans opened)
    exact ⟨Except.ok.inj equal.1, equal.2⟩
  | replaced conflict _ _ =>
    have equal := EStateM.Result.ok.inj (reported.symm.trans conflict)
    cases equal.1

theorem stageFails :
    bootstrap.stage (directory.file .stagedWalBoundary) markerBytes keeper.directoryBarrier.reached =
      .error source.cause seen.reached := by
  have finalized : withDataErrorDrop seen.drop seen.handle (seen.calls.flush seen.handle) seen.written =
      .error source.cause seen.reached := by
    rw [withDataErrorDrop_error _ _ _ seen.flushed, dataErrorDropState, seen.dropped]
    cases status : source.dropStatus with
    | ok result => cases result; rfl
    | error _ => rfl
  have wrote : withDataErrorDrop seen.drop seen.handle (seen.calls.write seen.handle markerBytes) seen.opened =
      .ok () seen.written := by simp only [withDataErrorDrop, seen.wrote]
  rw [seen.stage]
  simp [writeFreshStagedWith, withFreshStaging, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
    seen.created, wrote, finalized]

structure Reached : Prop where
  file : BootstrapFileProjection.atHeap view keeper.inodes seen.reached = (source.reached, source.reachedInodes)
  scratch : (seen.names seen.reached).child captured.root "WAL.commit.next" = some source.child.child
  absent : (seen.names seen.reached).child captured.root "WAL.commit" = none
  slot : view.handle seen.stopped seen.handle = source.handle
  census : view.descriptors seen.reached = (source.inventory.afterDrops source.beforeFlush).afterDrops [source.slot.closeEvent]
  retired : (view.descriptors seen.reached).references source.slot.description = []
  cache : view.cacheAt seen.reached seed.directoryRef seed.activeRef seed.pendingRef = captured.cache
  owned : (view.files seen.reached).owners = before.owners.set (directory.file .lock) (some fileCalls.slot.description)

/-- The reported flush and close leave the exact selected scratch bytes.
The same keeper cache stays live for the failing open's cleanup. -/
theorem reaches : seen.Reached := by
  have rawOpen := seen.openProjection
  rw [seen.created] at rawOpen
  change EStateM.Result.ok (Except.ok (view.handle seen.opened seen.handle))
    (BootstrapFileProjection.atHeap view keeper.inodes seen.opened) = _ at rawOpen
  have settled := keeper.settles
  have initial : BootstrapFileProjection.atHeap view keeper.inodes keeper.directoryBarrier.reached =
      (⟨before.image.metadata.syncDirectory, .durable⟩, (BootstrapZeroKeeperRoute.reused selected).settledImage) :=
    Prod.ext settled.image settled.inodes
  rw [initial] at rawOpen
  obtain ⟨handle, openFiles⟩ := sameOpened rawOpen.symm
  have written := seen.writeProjection
  rw [seen.wrote, handle, openFiles, source.wrote] at written
  have writtenFiles := (EStateM.Result.ok.inj written).2
  have flushing := seen.flushProjection
  rw [seen.flushed, seen.keptAtFlush, handle, writtenFiles, source.failed] at flushing
  have stoppedFiles := (EStateM.Result.error.inj flushing).2
  have stoppedHandle := seen.sameSlotAtDrop.trans (seen.keptAtFlush.trans handle)
  have dropping := seen.dropProjection
  rw [stoppedHandle, stoppedFiles, source.dropped] at dropping
  have reachedFiles : BootstrapFileProjection.atHeap view keeper.inodes seen.reached = (source.reached, source.reachedInodes) := by
    cases status : source.dropStatus with
    | ok value =>
      cases value
      have returned := seen.dropped
      rw [status] at returned
      rw [returned, status] at dropping
      exact (EStateM.Result.ok.inj dropping).2
    | error cause =>
      have returned := seen.dropped
      rw [status] at returned
      rw [returned, status] at dropping
      exact (EStateM.Result.error.inj dropping).2
  have census := seen.finalCensus.trans (congrArg (fun slots : DescriptorInventory => slots.afterDrops [source.slot.closeEvent])
    (seen.atDrop.trans seen.atFlush))
  have retired : (view.descriptors seen.reached).references source.slot.description = [] := by
    rw [census, DescriptorInventory.afterDrops_append, BootstrapMarkerFlushError.inventory, DescriptorInventory.insert_thenClose,
      DescriptorInventory.references_afterDrops, source.fresh]
    rfl
  have cache : view.cacheAt seen.reached seed.directoryRef seed.activeRef seed.pendingRef = captured.cache := by
    simp only [OpenCloseHeapView.cacheAt, seen.directoryCell, seen.active, seen.pending, seen.directoryHandle,
      keeper.keptHandle, seed.sameHandle, seed.openedHandle, Option.map_some, Option.map_none, List.map_nil,
      BootstrapCacheOpen.cache, BootstrapCacheOpen.reached]
  have bound := source.child.binds
  rw [source.child.atRoot, source.child.atName] at bound
  exact ⟨reachedFiles, seen.finalNames.symm ▸ bound,
    seen.finalNames.symm ▸ (source.offTargetNames "WAL.commit" (by decide)).trans source.canonicalAbsent,
    stoppedHandle, census, retired, cache, seen.owners.trans settled.owners⟩

/-- The held opener's actual bootstrap bind stops on the flush error.
The pending insertion, marker barriers and installer are past that return. -/
theorem stops
    (flat : bootstrap.metadata (directory.file .wal) seed.afterPending = .ok none seed.afterPending)
    (absent : bootstrap.metadata (directory.file .walBoundary) seed.afterPending = .ok none seed.afterPending)
    (marked : EStateM IO.Error heap Reopened) :
    recoverSegmentedWalWith (rejectFlatWalWith directory (bootstrap.metadata (directory.file .wal)))
      (bootstrap.metadata (directory.file .walBoundary)) marked
      (bootstrap.run directory seed.directoryRef seed.activeRef seed.pendingRef) seed.afterPending =
      .error source.cause seen.reached := by
  rw [keeper.reachesFromHeld flat absent marked]
  unfold FreshBootstrapCacheCalls.publishZeroMarker
  rw [Publication.run_performReplacement]
  simp [FreshBootstrapCacheCalls.stagePending, Bind.bind, EStateM.bind, seen.stageFails]

end RawBootstrapMarkerFlushError

variable {input : FilePath} {inventory : DescriptorInventory} {beforeOpen : heap}
  {admission : CensusOpenAdmissionReports input directory inventory before} {calls : RawOpenAdmissionCallbacks heap}

/-- The failed markerless worker drops its directory cache before a
successful local unlock. The lock descriptor then has its own finalizer.
The cleanup reports frame the reached scratch image and its inode map. -/
structure RawBootstrapMarkerFlushCleanup
    (admitted : RawOpenAdmissionReport admission view calls beforeOpen)
    {seed : OpenSyncCacheAllocations captured.opened view init admitted.afterFlock}
    {guards : ReusedBootstrapKeeperGuards selected seed bootstrap} {keeper : ReusedBootstrapKeeperHeap guards}
    (failed : RawBootstrapMarkerFlushError keeper source) (release : IO.FS.Handle → heap → heap) where
  dispose : DiskTable.OpenSyncFiles → EStateM IO.Error heap Unit
  afterCache : heap
  disposed : ∀ cache, cache.UsesCacheReferences seed.activeRef seed.pendingRef seed.directoryRef →
    dispose cache failed.reached = .ok () afterCache
  cacheLive : captured.cached ∈ (view.descriptors failed.reached).slots
  cacheCensus : view.descriptors afterCache = (view.descriptors failed.reached).afterDrops [captured.cached.closeEvent]
  cacheFiles : view.files afterCache = view.files failed.reached
  sameLock : view.handle afterCache admitted.lock = view.handle admitted.afterFlock admitted.lock
  lockLive : fileCalls.slot ∈ (view.descriptors afterCache).slots
  afterUnlock : heap
  unlocked : calls.unlock admitted.lock afterCache = .ok () afterUnlock
  unlockCensus : view.descriptors afterUnlock = view.descriptors afterCache
  unlockFiles : view.files afterUnlock =
    { view.files afterCache with owners := (view.files afterCache).owners.set (directory.file .lock) none }
  modelUnlock : fileCalls.unlock = .success
  finalized : RawOpenErrorLockFinalization view directory release admitted.lock fileCalls.slot afterUnlock
  finalNames : failed.names finalized.reached = failed.names failed.reached
  finalInodes : keeper.inodes finalized.reached = keeper.inodes failed.reached

namespace RawBootstrapMarkerFlushCleanup

variable {admitted : RawOpenAdmissionReport admission view calls beforeOpen}
  {seed : OpenSyncCacheAllocations captured.opened view init admitted.afterFlock}
  {guards : ReusedBootstrapKeeperGuards selected seed bootstrap} {keeper : ReusedBootstrapKeeperHeap guards}
  {failed : RawBootstrapMarkerFlushError keeper source} {release : IO.FS.Handle → heap → heap}

def errorScope (seen : RawBootstrapMarkerFlushCleanup admitted failed release)
    (recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α)
    (directory : DiskDirectory) (lock : IO.FS.Handle) (cache : DiskTable.OpenSyncFiles) : EStateM IO.Error heap α :=
  tryCatchThe IO.Error (recover directory lock cache) fun cause => do
    seen.dispose cache
    throw cause

/-- The caller receives the original flush diagnostic after the two
reported drops, with the same scratch and vacant lock for the retry. -/
theorem returns (seen : RawBootstrapMarkerFlushCleanup admitted failed release)
    (modelAdmission : OpenAdmissionReports input directory fileCalls.slot) (valid : BootstrapValid before.image)
    (owner : admission.owner = fileCalls.slot)
    (metadata : ∀ path, bootstrap.metadata path = optionalMetadataWith (calls.lookup path))
    (keeperLookup : guards.metadataLookup (directory.file (.walSegment 0)) = calls.lookup (directory.file (.walSegment 0)))
    (flat : bootstrap.metadata (directory.file .wal) seed.afterPending = .ok none seed.afterPending)
    (absent : bootstrap.metadata (directory.file .walBoundary) seed.afterPending = .ok none seed.afterPending)
    (marked : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap DiskTable) :
    let recover := calls.recoverAndInstall marked (fun resolved _ =>
      bootstrap.run resolved seed.directoryRef seed.activeRef seed.pendingRef) install
    ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles) (cache : DiskTable.OpenSyncFiles),
      DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      openSyncFilesWith (init.openDirectory directory.path) init.newRef init.newRef init.newRef makeCache
        admitted.afterFlock = .ok cache seed.afterPending ∧
      cache.UsesCacheReferences seed.activeRef seed.pendingRef seed.directoryRef ∧
      bootstrap.readEmpty (directory.file (.walSegment 0)) = WalSegmentRotation.readEmptyWith
        (calls.lookup (directory.file (.walSegment 0))) (directory.file (.walSegment 0)) WAL.Boundary.missingOpenMarker ∧
      finishFailedOpen (calls.runOpen input init makeCache (seen.errorScope recover)) release admitted.lock beforeOpen =
        .error source.returnedError seen.finalized.reached ∧
      fileCalls.run modelAdmission = .error source.returnedError source.final ∧
      view.files seen.finalized.reached = source.final ∧
      (view.files seen.finalized.reached).owners (directory.file .lock) = none ∧
      view.descriptors seen.finalized.reached =
        (((view.descriptors failed.stopped).afterDrops [source.slot.closeEvent]).afterDrops [captured.cached.closeEvent]).afterDrops
          [fileCalls.slot.closeEvent] ∧
      captured.cached ∈ (view.descriptors failed.reached).slots ∧ fileCalls.slot ∈ (view.descriptors seen.afterCache).slots ∧
      (view.handle seen.afterCache admitted.lock).2.1 = fileCalls.slot ∧
      keeper.inodes seen.finalized.reached = source.reachedInodes ∧ failed.names seen.finalized.reached = source.reachedView := by
  intro recover
  obtain ⟨cacheOpen, makeCache, cache, isOpen, cacheSource, initialized, refs, _⟩ := seed.installs
  have stops := failed.stops flat absent (marked directory cache)
  have held : recover directory admitted.lock cache seed.afterPending = .error source.cause failed.reached := by
    dsimp only [recover, RawOpenAdmissionCallbacks.recoverAndInstall]
    rw [← metadata, ← metadata]
    simp only [Bind.bind, EStateM.bind, stops]
  have ran := admitted.startsInitializedWorker init initialized (seen.errorScope recover)
  have unlockReturn : calls.runOpen input init makeCache (seen.errorScope recover) beforeOpen =
      .error source.cause seen.afterUnlock := by
    rw [ran]
    simp only [errorScope, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, held, EStateM.Backtrackable.restore,
      EStateM.dummyRestore, Bind.bind, EStateM.bind, seen.disposed cache refs, throw, throwThe,
      MonadExceptOf.throw, EStateM.throw, seen.unlocked]
  have vacant : (view.files seen.afterUnlock).owners (directory.file .lock) = none := by
    simp [seen.unlockFiles, LockOwners.set]
  obtain ⟨returned, _, _, _, _⟩ := seen.finalized.returns _ unlockReturn (.ok ()) vacant
  have live : (view.descriptors seen.afterUnlock).references fileCalls.slot.description ≠ [] :=
    List.ne_nil_of_mem ((view.descriptors seen.afterUnlock).mem_references.mpr ⟨_, seen.finalized.live, rfl, rfl⟩)
  have unowned : (view.files seen.afterUnlock).owners (directory.file .lock) ≠ some fileCalls.slot.description := by
    simp [vacant]
  have finalFiles : view.files seen.finalized.reached = view.files seen.afterUnlock := by
    simp only [seen.finalized.files, DescriptorInventory.dropLockState, dite_eq_left live,
      HeldLockReferences.afterFileDrops_unowned _ unowned]
  have reached := failed.reaches
  have sameScratch := congrArg Prod.fst reached.file
  have sameInodes := congrArg Prod.snd reached.file
  have actualFiles : view.files seen.finalized.reached = source.final := by
    rw [finalFiles, seen.unlockFiles, seen.cacheFiles]
    change LockedFileState.mk _ _ = LockedFileState.mk _ _
    refine (LockedFileState.mk.injEq _ _ _ _).mpr ⟨sameScratch, ?_⟩
    rw [reached.owned]
    funext path
    by_cases same : path = directory.file .lock <;> simp [seen.modelUnlock, LockOwners.set, same]
  have cause : source.returnedError = source.cause := by simp [BootstrapMarkerFlushError.returnedError, seen.modelUnlock]
  have localUnlock : fileCalls.unlock.LocalFlock := by simp [seen.modelUnlock, UnlockReport.LocalFlock]
  have census := seen.finalized.census
  rw [seen.unlockCensus, seen.cacheCensus, failed.finalCensus] at census
  have lock := congrArg (fun raw => raw.2.1) (seen.sameLock.trans (admitted.sameLock.trans admitted.appendHandle))
  exact ⟨cacheOpen, makeCache, cache, isOpen, cacheSource, initialized, refs, by rw [guards.source, keeperLookup],
    cause.symm ▸ returned,
    (source.returns modelAdmission valid localUnlock).1, actualFiles, finalFiles.symm ▸ vacant, census,
    seen.cacheLive, seen.lockLive, lock.trans owner, seen.finalInodes.trans sameInodes, seen.finalNames.trans failed.finalNames⟩

end RawBootstrapMarkerFlushCleanup

end Alvoki.Storage.DiskSession
