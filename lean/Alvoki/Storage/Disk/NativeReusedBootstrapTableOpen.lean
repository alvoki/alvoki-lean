import Alvoki.Storage.Disk.NativeReusedBootstrapKeeperHeap
import Alvoki.Storage.Disk.NativeRawOpenAdmission
import Alvoki.Storage.Disk.NativeAlignedOpenHeap

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

variable {heap : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {before : LockedFileState WalSegmentRotation.State}
  {fileCalls : BootstrapOpenCalls (Cache CheckpointOpenHandle) directory before}
  {captured : BootstrapCacheOpen fileCalls.toBootstrapAdmissionCalls} {listed : BootstrapCheckedListing captured}
  {observed : BootstrapReusedZeroKeeper listed} {marker : BootstrapMarkerCustody listed}
  {handoff : BootstrapKeeperMarkerHandoff (.reused observed) marker}
  {effects : BootstrapKeeperMarkerHandoff.ReturnedCensus marker}
  {view : OpenCloseHeapView heap WalSegmentRotation.State} {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {admission : CensusOpenAdmissionReports input directory inventory before}
  {calls : RawOpenAdmissionCallbacks heap} {bootstrap : FreshBootstrapCacheCalls heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}

/-- The public markerless retry admits the same old keeper, publishes its
zero marker and allocates the empty table on that exact reached heap.
The valid pre-bootstrap image may already contain the empty keeper. -/
theorem ReusedBootstrapKeeperHeap.MarkerPublication.opensFromAdmission
    (admitted : RawOpenAdmissionReport admission view calls entry)
    {seed : OpenSyncCacheAllocations captured.opened view init admitted.afterFlock}
    {guards : ReusedBootstrapKeeperGuards observed seed bootstrap} {keeper : ReusedBootstrapKeeperHeap guards}
    (publication : keeper.MarkerPublication handoff effects)
    (modelAdmission : OpenAdmissionReports input directory fileCalls.slot) (valid : BootstrapValid before.image)
    (owner : admission.owner = fileCalls.slot)
    (metadata : ∀ path, bootstrap.metadata path = optionalMetadataWith (calls.lookup path))
    (keeperLookup : guards.metadataLookup (directory.file (.walSegment 0)) = calls.lookup (directory.file (.walSegment 0)))
    (flat : bootstrap.metadata (directory.file .wal) seed.afterPending = .ok none seed.afterPending)
    (absent : bootstrap.metadata (directory.file .walBoundary) seed.afterPending = .ok none seed.afterPending)
    (marked : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
      IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock cache, DiskTable.OpenReferenceAssembly resolved lock cache (assemble resolved lock cache))
    (allocation : OpenReferenceAllocations allocatePhase allocateToken view.phase
      (⟨.empty, 0, 0, 0⟩ : Reopened).installed publication.raw.markerDirectory.reached)
    (phaseID : phaseIdentity allocation.phase = fileCalls.nextRef)
    (tokenID : tokenIdentity allocation.token = fileCalls.nextRef + 1)
    (phaseFrame : CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef
      publication.raw.markerDirectory.reached allocation.afterPhase)
    (tokenFrame : CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef
      allocation.afterPhase allocation.afterToken)
    (phaseInodes : keeper.inodes allocation.afterPhase = keeper.inodes publication.raw.markerDirectory.reached)
    (tokenInodes : keeper.inodes allocation.afterToken = keeper.inodes allocation.afterPhase)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (phaseEffects : OpenPhaseCellEffects view.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    let recover := fun (resolved : DiskDirectory) (cache : DiskTable.OpenSyncFiles) =>
      recoverSegmentedWalWith
        (rejectFlatWalWith resolved (optionalMetadataWith (calls.lookup (resolved.file .wal))))
        (optionalMetadataWith (calls.lookup (resolved.file .walBoundary)))
        (marked resolved cache) (bootstrap.run resolved seed.directoryRef seed.activeRef seed.pendingRef)
    ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle)
      (after : LockedFileState WalSegmentRotation.State),
      DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      openSyncFilesWith (init.openDirectory directory.path) init.newRef init.newRef init.newRef makeCache
        admitted.afterFlock = .ok handle.files seed.afterPending ∧
      bootstrap.readEmpty (directory.file (.walSegment 0)) = WalSegmentRotation.readEmptyWith
        (calls.lookup (directory.file (.walSegment 0))) (directory.file (.walSegment 0)) WAL.Boundary.missingOpenMarker ∧
      calls.runOpen input init makeCache (fun resolved lock cache => do
        let opened ← recover resolved cache
        installReady opened.installed allocatePhase allocateToken
          (fun phase token => pure (assemble resolved lock cache phase token))) entry = .ok handle.table start.reached ∧
      handle.directory = directory ∧ handle.lock = admitted.lock ∧
      handle.files.UsesBootstrapCacheSchedules directory seed.activeRef seed.pendingRef seed.directoryRef ∧
      handle.phase = allocation.phase ∧ handle.token = allocation.token ∧ handle.contents = view.phase ∧
      handle.get = get ∧ handle.set = set ∧ handle.ptrEq = ptrEq ∧ start.reached = allocation.afterToken ∧
      view.handle admitted.afterFlock handle.lock = (captured.initial, fileCalls.slot, 0) ∧
      (view.handle admitted.afterFlock handle.lock).2.1.description = start.current.ready.state.session.descriptor ∧
      phaseIdentity handle.phase = start.current.ready.state.session.phaseRef ∧
      tokenIdentity handle.token = start.current.ready.state.session.sessionRef ∧
      view.files start.reached = after ∧ view.descriptors start.reached = start.current.ready.state.census ∧
      view.cacheAt start.reached seed.directoryRef seed.activeRef seed.pendingRef = start.current.ready.state.cache ∧
      fileCalls.run modelAdmission = .ok start.current.ready.state.session after ∧
      BootstrapReady after.image ∧ (view.descriptors start.reached).references marker.slot.description = [] ∧
      handoff.afterMarkerNames (renderWalSegmentName 0) = [some observed.statChild.child] ∧
      handoff.afterMarkerNames "WAL.commit" = [some marker.stageChild.child] ∧
      (keeper.inodes start.reached).crashBytes (BootstrapZeroKeeperRoute.settledImage (.reused observed)).active = [ByteArray.empty] ∧
      (keeper.inodes start.reached).crashBytes marker.inodeState.active = [WAL.Boundary.encode 0] ∧
      start.current.history = [] ∧ start.current.submissions = [] ∧ start.current.ready.reads = [] ∧ start.pins = [] := by
  intro recover
  obtain ⟨logical, returned, session, finalImage, logicalOwners, _, _, _, _, keeperName, markerName, _, _, ready⟩ :=
    handoff.startsNativeReadPrefixFromValid modelAdmission valid effects
  let state : NativeReadyState :=
    ⟨logical.session, logical.writer, effects.reached, captured.cache, fileCalls.slot, captured.cached⟩
  obtain ⟨cacheOpen, makeCache, cache, action, source, initialized, references, path, _, _, _, _, _, _, _, _, _⟩ := seed.installs
  obtain ⟨allocated, uses, stored⟩ := allocation.installs (constructs directory admitted.lock cache)
  obtain ⟨worker, finalCache, image, finalOwners, census, released, keeperBytes, markerBytes⟩ :=
    publication.returns flat absent (marked directory cache)
  let held := fun resolved lock files => do
    let opened ← recover resolved files
    installReady opened.installed allocatePhase allocateToken
      (fun phase token => pure (assemble resolved lock files phase token))
  have heldReturn : held directory admitted.lock cache seed.afterPending =
      .ok (assemble directory admitted.lock cache allocation.phase allocation.token) allocation.afterToken := by
    dsimp only [held, recover]
    rw [← metadata, ← metadata]
    simp only [Bind.bind, EStateM.bind, worker]
    exact allocated
  have rawOpen := admitted.startsInitializedWorker init initialized held
  have exactOpen : calls.runOpen input init makeCache held entry =
      .ok (assemble directory admitted.lock cache allocation.phase allocation.token) allocation.afterToken := by
    simpa only [MonadExceptOf.tryCatch, tryCatchThe, EStateM.tryCatch, heldReturn] using rawOpen
  have initial := (admitted.lockedCensus.trans admitted.appendCensus).symm.trans seed.entrySlots
  have usedLock : view.handle admitted.afterFlock admitted.lock = (captured.initial, fileCalls.slot, 0) := by
    rw [admitted.sameLock.trans admitted.appendHandle, initial, owner]
  let handle : NativeOpenedHandle heap :=
    ⟨_, directory, admitted.lock, cache, allocation.phase, allocation.token, uses, view.phase, get, set, phaseEffects, ptrEq⟩
  let current : NativeExecutionPosition :=
    ⟨[], [], ⟨.ok state.session (state.census, state.files), state, state, [], ready⟩⟩
  have saved : view.phase allocation.afterToken allocation.phase = some state.session.phase := by
    rw [session]
    exact stored
  let start := NativeOpenedPosition.fromOpen handle current allocation.afterToken logical.canonicalDirectory saved
  have fileState : view.files publication.raw.markerDirectory.reached = logical.final := by
    change LockedFileState.mk _ _ = LockedFileState.mk _ _
    exact (LockedFileState.mk.injEq _ _ _ _).mpr ⟨image.trans finalImage.symm, finalOwners.trans logicalOwners.symm⟩
  have keptInodes := tokenInodes.trans phaseInodes
  have keptCensus := tokenFrame.census.trans phaseFrame.census
  refine ⟨cacheOpen, makeCache, handle, start, logical.final, action, source, initialized, ?_, exactOpen, rfl, rfl,
    cache.bootstrapCacheSchedules references path, rfl, rfl, rfl, rfl, rfl, rfl, rfl, usedLock, ?_, ?_, ?_,
    tokenFrame.files.trans (phaseFrame.files.trans fileState),
    keptCensus.trans census,
    tokenFrame.cache.trans (phaseFrame.cache.trans finalCache), returned,
    logical.bootstrap, keptCensus.symm ▸ released, keeperName, markerName,
    keptInodes.symm ▸ keeperBytes, keptInodes.symm ▸ markerBytes, rfl, rfl, rfl, rfl⟩
  · rw [guards.source, keeperLookup]
  · change (view.handle admitted.afterFlock admitted.lock).2.1.description = state.session.descriptor
    rw [usedLock, session]
  · change phaseIdentity allocation.phase = state.session.phaseRef
    rw [phaseID, session]
  · change tokenIdentity allocation.token = state.session.sessionRef
    rw [tokenID, session]

end Alvoki.Storage.DiskSession
