import Alvoki.Storage.Disk.NativeFreshTableOpen
import Alvoki.Storage.Disk.NativeOpenedRestartSessions

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- Keep the same process heap, reference contents and descriptor
observations while changing the file-state model projected from it. -/
def OpenCloseHeapView.withFileProjection {heap image nextImage : Type} (view : OpenCloseHeapView heap image)
    (files : heap → LockedFileState nextImage) : OpenCloseHeapView heap nextImage :=
  ⟨view.phase, view.active, view.pending, view.directory, view.handle, files, view.descriptors⟩

variable {heap : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {report : EmptyOpenSuccessReports input directory}
  {admission : CensusOpenAdmissionReports input directory inventory report.before}
  {view : OpenCloseHeapView heap WalSegmentRotation.State} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {bootstrap : FreshBootstrapCacheCalls heap}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}

/-- Start the finite multi-session trace at the exact public bootstrap
return. Later reports use the same process and descriptor observations
and supply the file-image projection of their reached heaps. -/
theorem FreshBootstrapOpenHeap.executesOpenedSessions
    (admitted : RawOpenAdmissionReport admission view calls entry)
    {seed : OpenSyncCacheAllocations report.captured.opened view init admitted.afterFlock}
    {raw : FreshBootstrapCacheChronology seed bootstrap}
    (observed : FreshBootstrapOpenHeap report raw)
    (owner : admission.owner = report.calls.slot)
    (metadata : ∀ path, bootstrap.metadata path = optionalMetadataWith (calls.lookup path))
    (marked : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
      IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files))
    (allocation : OpenReferenceAllocations allocatePhase allocateToken view.phase
      (⟨.empty, 0, 0, 0⟩ : Reopened).installed raw.markerDirectory.reached)
    (phaseID : phaseIdentity allocation.phase = report.calls.nextRef)
    (tokenID : tokenIdentity allocation.token = report.calls.nextRef + 1)
    (phaseFrame : CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef
      raw.markerDirectory.reached allocation.afterPhase)
    (tokenFrame : CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef
      allocation.afterPhase allocation.afterToken)
    (phaseInodes : observed.keeperPhysical.inodes allocation.afterPhase =
      observed.keeperPhysical.inodes raw.markerDirectory.reached)
    (tokenInodes : observed.keeperPhysical.inodes allocation.afterToken =
      observed.keeperPhysical.inodes allocation.afterPhase)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects view.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)
    (fileImage : heap → LockedFileState FileImage) (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray) :
    let clientView := view.withFileProjection fileImage
    let recover := fun (resolved : DiskDirectory) (cache : DiskTable.OpenSyncFiles) =>
      recoverSegmentedWalWith
        (rejectFlatWalWith resolved (optionalMetadataWith (calls.lookup (resolved.file .wal))))
        (optionalMetadataWith (calls.lookup (resolved.file .walBoundary)))
        (marked resolved cache) (bootstrap.run resolved seed.directoryRef seed.activeRef seed.pendingRef)
    ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
      (start : NativeOpenedSessionPoint heap) (after : LockedFileState WalSegmentRotation.State),
      DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      openSyncFilesWith (init.openDirectory directory.path) init.newRef init.newRef init.newRef makeCache
        admitted.afterFlock = .ok start.handle.files seed.afterPending ∧
      calls.runOpen input init makeCache (fun resolved lock cache => do
        let opened ← recover resolved cache
        installReady opened.installed allocatePhase allocateToken
          (fun phase token => pure (assemble resolved lock cache phase token))) entry =
        .ok start.handle.table start.position.reached ∧
      start.handle.directory = directory ∧ start.handle.lock = admitted.lock ∧
      start.handle.files.UsesBootstrapCacheSchedules directory seed.activeRef seed.pendingRef seed.directoryRef ∧
      start.handle.phase = allocation.phase ∧ start.handle.token = allocation.token ∧ start.handle.contents = clientView.phase ∧
      start.handle.get = get ∧ start.handle.set = set ∧ start.handle.ptrEq = ptrEq ∧
      start.position.reached = allocation.afterToken ∧
      view.handle admitted.afterFlock start.handle.lock = (report.captured.initial, report.calls.slot, 0) ∧
      (view.handle admitted.afterFlock start.handle.lock).2.1.description =
        start.position.current.ready.state.session.descriptor ∧
      phaseIdentity start.handle.phase = start.position.current.ready.state.session.phaseRef ∧
      tokenIdentity start.handle.token = start.position.current.ready.state.session.sessionRef ∧
      view.files start.position.reached = after ∧
      clientView.descriptors start.position.reached = start.position.current.ready.state.census ∧
      clientView.cacheAt start.position.reached seed.directoryRef seed.activeRef seed.pendingRef =
        start.position.current.ready.state.cache ∧
      report.calls.run report.admission = .ok start.position.current.ready.state.session after ∧
      (NativeOpenSuccessReports.empty report).UsesReachedState start.position.current.ready.state after ∧
      (observed.keeperPhysical.inodes start.position.reached).crashBytes
        (BootstrapZeroKeeperRoute.settledImage (.fresh observed.keeper)).active = [ByteArray.empty] ∧
      (observed.keeperPhysical.inodes start.position.reached).crashBytes report.marker.inodeState.active = [WAL.Boundary.encode 0] ∧
      start.position.current.history = [] ∧ start.position.current.submissions = [] ∧
      start.position.current.ready.reads = [] ∧ start.position.pins = [] ∧
      ∀ actions, NativeOpenedSessionTrace.Reports clientView names bytes start actions →
        ∃ events last, NativeOpenedSessionTrace clientView names bytes start actions events last ∧
          NativeExecutionTrace start.position.current events last.position.current ∧
          last.position.current.history = events.flatMap NativeExecutionEvent.writes ∧
          last.position.current.submissions = events.flatMap NativeExecutionEvent.submissions ∧
          last.position.current.ready.reads = events.flatMap NativeExecutionEvent.reads ∧
          InstalledClientReplay last.position.current.submissions last.position.current.ready.reads last.position.current.history
            last.position.current.ready.state.writer.installed last.position.current.ready.state.session := by
  intro clientView recover
  obtain ⟨cacheOpen, makeCache, handle, position, after, cacheAction, cacheSource, cacheInitialized, opened,
    path, lock, schedules, phase, token, contents, getter, setter, compared, reached, rawLock, lockRef, phaseRef, tokenRef,
    projected, census, cache, returned, bootState, keeperBytes, markerBytes, emptyHistory, emptyLog, emptyReads, emptyPins⟩ :=
    observed.opensFromAdmission admitted owner metadata marked assemble constructs allocation phaseID tokenID
      phaseFrame tokenFrame phaseInodes tokenInodes effects ptrEq
  let start : NativeOpenedSessionPoint heap := ⟨handle, position⟩
  refine ⟨cacheOpen, makeCache, start, after, cacheAction, cacheSource, cacheInitialized, opened, path, lock,
    schedules, phase, token, contents, getter, setter, compared, reached, rawLock, lockRef, phaseRef, tokenRef,
    projected, census, cache,
    returned, bootState, keeperBytes, markerBytes, emptyHistory, emptyLog, emptyReads, emptyPins, ?_⟩
  intro actions localReports
  obtain ⟨events, last, trace, common, replay⟩ := NativeOpenedSessionTrace.executes start actions localReports
  obtain ⟨history, log, reads⟩ := common.ledgers
  refine ⟨events, last, trace, common, ?_, ?_, ?_, replay⟩
  · simpa only [start, emptyHistory, List.nil_append] using history
  · simpa only [start, emptyLog, List.nil_append] using log
  · simpa only [start, emptyReads, List.nil_append] using reads

end Alvoki.Storage.DiskSession
