import Alvoki.Storage.Disk.Proofs.Bootstrap.NativeFreshBootstrapOpenHeap
import Alvoki.Storage.Disk.NativeRawOpenAdmission

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

namespace FreshBootstrapOpenHeap

/-- The public open returned this handle at the start position used by
the next call. Its client ledger and issued pins start empty. -/
structure Returned {heap : Type} (call : EStateM IO.Error heap DiskTable) (entry : heap) where
  handle : NativeOpenedHandle heap
  start : NativeOpenedPosition handle
  opened : call entry = .ok handle.table start.reached
  emptyHistory : start.current.history = []
  emptySubmissions : start.current.submissions = []
  emptyReads : start.current.ready.reads = []
  emptyPins : start.pins = []

end FreshBootstrapOpenHeap

variable {heap : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {report : EmptyOpenSuccessReports input directory}
  {admission : CensusOpenAdmissionReports input directory inventory report.before}
  {view : OpenCloseHeapView heap WalSegmentRotation.State} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {bootstrap : FreshBootstrapCacheCalls heap}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}

/-- A fresh markerless open takes the cache allocated after its own
flock through the held bootstrap worker and the two table allocations.
The returned table starts the empty client trace on that exact heap. -/
theorem FreshBootstrapOpenHeap.opensFromAdmission
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
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    let recover := fun (resolved : DiskDirectory) (cache : DiskTable.OpenSyncFiles) =>
      recoverSegmentedWalWith
        (rejectFlatWalWith resolved (optionalMetadataWith (calls.lookup (resolved.file .wal))))
        (optionalMetadataWith (calls.lookup (resolved.file .walBoundary)))
        (marked resolved cache) (bootstrap.run resolved seed.directoryRef seed.activeRef seed.pendingRef)
    ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
      (returned : FreshBootstrapOpenHeap.Returned (calls.runOpen input init makeCache (fun resolved lock cache => do
        let opened ← recover resolved cache
        installReady opened.installed allocatePhase allocateToken
          (fun phase token => pure (assemble resolved lock cache phase token)))) entry)
      (after : LockedFileState WalSegmentRotation.State),
      let handle := returned.handle
      let start := returned.start
      DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      openSyncFilesWith (init.openDirectory directory.path) init.newRef init.newRef init.newRef makeCache
        admitted.afterFlock = .ok handle.files seed.afterPending ∧
      handle.directory = directory ∧ handle.lock = admitted.lock ∧
      handle.files.UsesBootstrapCacheSchedules directory seed.activeRef seed.pendingRef seed.directoryRef ∧
      handle.phase = allocation.phase ∧ handle.token = allocation.token ∧ handle.contents = view.phase ∧
      handle.get = get ∧ handle.set = set ∧ handle.ptrEq = ptrEq ∧ start.reached = allocation.afterToken ∧
      view.handle admitted.afterFlock handle.lock = (report.captured.initial, report.calls.slot, 0) ∧
      (view.handle admitted.afterFlock handle.lock).2.1.description = start.current.ready.state.session.descriptor ∧
      phaseIdentity handle.phase = start.current.ready.state.session.phaseRef ∧
      tokenIdentity handle.token = start.current.ready.state.session.sessionRef ∧
      view.files start.reached = after ∧ view.descriptors start.reached = start.current.ready.state.census ∧
      view.cacheAt start.reached seed.directoryRef seed.activeRef seed.pendingRef = start.current.ready.state.cache ∧
      report.calls.run report.admission = .ok start.current.ready.state.session after ∧
      (NativeOpenSuccessReports.empty report).UsesReachedState start.current.ready.state after ∧
      (observed.keeperPhysical.inodes start.reached).crashBytes
        (BootstrapZeroKeeperRoute.settledImage (.fresh observed.keeper)).active = [ByteArray.empty] ∧
      (observed.keeperPhysical.inodes start.reached).crashBytes report.marker.inodeState.active = [WAL.Boundary.encode 0] ∧
      handle.files.UsesCacheReferences seed.activeRef seed.pendingRef seed.directoryRef ∧
      handle.files.AtDirectory directory.path := by
  intro recover
  let lockIdentity := fun handle => (view.handle admitted.afterFlock handle).2.1.description
  have initial := (admitted.lockedCensus.trans admitted.appendCensus).symm.trans seed.entrySlots
  have capturedLock : view.handle admitted.afterFlock admitted.lock = (report.captured.initial, report.calls.slot, 0) := by
    rw [admitted.sameLock.trans admitted.appendHandle, initial, owner]
  have locked : lockIdentity admitted.lock = report.calls.slot.description :=
    congrArg (fun handle => handle.2.1.description) capturedLock
  obtain ⟨state, after, files, db, installer, ⟨cacheOpen, makeCache, action, source, initialized⟩,
    schedules, _, constructor, held, _, _, reachedFiles, reachedCensus, cached, lockRef, phaseRef, tokenRef,
    normalized, alignedState, keeperBytes, markerBytes, position, cacheRefs, atDirectory⟩ :=
    observed.installs admitted.lock lockIdentity locked phaseIdentity tokenIdentity allocatePhase allocateToken allocation
      phaseID tokenID phaseFrame tokenFrame phaseInodes tokenInodes
  let worker := fun resolved lock cache => do
    let opened ← recover resolved cache
    installReady opened.installed allocatePhase allocateToken
      (fun phase token => pure (assemble resolved lock cache phase token))
  have sameConstructor := (constructs directory admitted.lock files).trans constructor.symm
  have returned : worker directory admitted.lock files seed.afterPending = .ok db allocation.afterToken := by
    dsimp only [worker, recover]
    rw [← metadata, ← metadata, sameConstructor]
    exact held (marked directory files)
  have run := admitted.startsInitializedWorker init initialized worker
  have exactOpen : calls.runOpen input init makeCache worker entry = .ok db allocation.afterToken := by
    simpa only [MonadExceptOf.tryCatch, tryCatchThe, EStateM.tryCatch, returned] using run
  obtain ⟨handle, start, table, path, lock, cache, phase, token, contents, getter, setter, compared, reached, ready,
    history, submissions, reads, pins⟩ := position get set effects ptrEq
  have opened : calls.runOpen input init makeCache worker entry = .ok handle.table start.reached := by
    rw [table, reached]
    exact exactOpen
  let fresh := FreshBootstrapOpenHeap.Returned.mk handle start opened history submissions reads pins
  refine ⟨cacheOpen, makeCache, fresh, after, action, source, ?_, path, lock, ?_, phase, token,
    contents, getter, setter, compared, reached, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact initialized.trans (congrArg (fun opened => EStateM.Result.ok opened seed.afterPending) cache.symm)
  · rw [cache]
    exact schedules
  · rw [lock]
    exact capturedLock
  · rw [lock, ready]
    exact lockRef
  · rw [phase, ready]
    exact phaseRef
  · rw [token, ready]
    exact tokenRef
  · rw [reached]
    exact reachedFiles
  · rw [reached, ready]
    exact reachedCensus
  · rw [reached, ready]
    exact cached
  · rw [ready]
    exact normalized
  · rw [ready]
    exact alignedState
  · rw [reached]
    exact keeperBytes
  · rw [reached]
    exact markerBytes
  · rw [cache]
    exact cacheRefs
  · rw [cache]
    exact atDirectory

end Alvoki.Storage.DiskSession
