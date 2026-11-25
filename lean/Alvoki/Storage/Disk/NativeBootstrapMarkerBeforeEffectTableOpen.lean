import Alvoki.Storage.Disk.NativeBootstrapMarkerBeforeEffectReboot
import Alvoki.Storage.Disk.NativeReusedBootstrapTableOpen

namespace Alvoki.Storage.DiskSession.RawBootstrapMarkerDirectoryStop.BeforeEffectMarkerlessReboot

open System SyncHandleRouting WalSegmentRepair

variable {heap : Type} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {fileCalls : BootstrapOpenCalls (Cache CheckpointOpenHandle) directory before}
  {captured : BootstrapCacheOpen fileCalls.toBootstrapAdmissionCalls} {listed : BootstrapCheckedListing captured}
  {view : OpenCloseHeapView heap WalSegmentRotation.State} {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {seed : OpenSyncCacheAllocations captured.opened view init entry} {calls : FreshBootstrapCacheCalls heap}
  {observed : BootstrapReusedZeroKeeper listed} {guards : ReusedBootstrapKeeperGuards observed seed calls}
  {keeper : ReusedBootstrapKeeperHeap guards} {stop : RawBootstrapMarkerDirectoryStop keeper}
  {marker : BootstrapMarkerRenamed listed} {handoff : BootstrapKeeperMarkerRename (.reused observed) marker}
  {physical : stop.Physical handoff}
  {nextFiles : BootstrapOpenCalls (Cache CheckpointOpenHandle) directory stop.markerlessReboot}
  {nextCapture : BootstrapCacheOpen nextFiles.toBootstrapAdmissionCalls}
  {nextListing : BootstrapCheckedListing nextCapture}

/-- The next admission captures the rooted reboot namespace. Its checked
keeper uses the inode image of that same reboot heap. -/
structure SameRestart (reboot : BeforeEffectMarkerlessReboot physical)
    (selected : BootstrapReusedZeroKeeper nextListing) : Prop where
  root : nextCapture.root = captured.root
  names : nextCapture.view = physical.names reboot.rebooted
  inodes : selected.files = keeper.inodes reboot.rebooted

/-- The checked bootstrap reuse route sees the original lock and empty
keeper in that reported restart snapshot. -/
theorem SameRestart.readsSelectedKeeper {reboot : BeforeEffectMarkerlessReboot physical}
    {selected : BootstrapReusedZeroKeeper nextListing} (same : SameRestart reboot selected)
    (valid : BootstrapValid before.image) :
    nextCapture.view.modelObject nextCapture.root = (view.descriptors stop.afterRename).inode captured.cached.description ∧
    nextCapture.initial.inode nextFiles.slot.description = captured.reached.inode fileCalls.slot.description ∧
    selected.statChild.child = observed.statChild.child ∧
    selected.files.active = (physical.names reboot.rebooted).modelObject observed.statChild.child ∧
    selected.files.visible selected.files.active = ByteArray.empty := by
  have chosen := reboot.selects valid
  have lock := nextListing.lifetime.lockEntry
  rw [nextListing.sameView, nextListing.sameRoot, same.names, same.root] at lock
  have sameLock := Option.some.inj (lock.symm.trans chosen.lock)
  have lockInode := nextListing.lifetime.identifiesLock
  rw [nextListing.sameView, same.names, sameLock, chosen.lockObject] at lockInode
  have keeperChild : selected.statChild.child = observed.statChild.child := by
    apply selected.statChild.child_eq
    rw [same.names, same.root]
    exact chosen.keeperBinding
  refine ⟨?_, ?_, keeperChild, (congrArg (·.active) same.inodes).trans reboot.keeperObject,
    same.inodes.symm ▸ chosen.keeperBytes⟩
  · rw [same.root, same.names]
    exact chosen.directory
  · exact lockInode.symm

variable {reboot : BeforeEffectMarkerlessReboot physical} {selected : BootstrapReusedZeroKeeper nextListing}
  {input : FilePath} {inventory : DescriptorInventory}
  {admission : CensusOpenAdmissionReports input directory inventory stop.markerlessReboot}
  {nextCalls : RawOpenAdmissionCallbacks heap} {nextInit : OpenSyncCacheCallbacks heap}
  {admitted : RawOpenAdmissionReport admission view nextCalls reboot.rebooted}
  {nextSeed : OpenSyncCacheAllocations nextCapture.opened view nextInit admitted.afterFlock}
  {bootstrap : FreshBootstrapCacheCalls heap} {nextGuards : ReusedBootstrapKeeperGuards selected nextSeed bootstrap}
  {nextKeeper : ReusedBootstrapKeeperHeap nextGuards} {nextMarker : BootstrapMarkerCustody nextListing}
  {published : BootstrapKeeperMarkerHandoff (.reused selected) nextMarker}
  {effects : BootstrapKeeperMarkerHandoff.ReturnedCensus nextMarker}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}

/-- The selected markerless restart is the input of the next raw open.
The same empty keeper is opened and synced. The shared bootstrap worker
publishes a zero marker, then allocates the actual returned empty table. -/
theorem opensEmptyTable (same : SameRestart reboot selected) (valid : BootstrapValid before.image)
    (publication : nextKeeper.MarkerPublication published effects)
    (modelAdmission : OpenAdmissionReports input directory nextFiles.slot)
    (owner : admission.owner = nextFiles.slot)
    (metadata : ∀ path, bootstrap.metadata path = optionalMetadataWith (nextCalls.lookup path))
    (keeperLookup : nextGuards.metadataLookup (directory.file (.walSegment 0)) =
      nextCalls.lookup (directory.file (.walSegment 0)))
    (flat : bootstrap.metadata (directory.file .wal) nextSeed.afterPending = .ok none nextSeed.afterPending)
    (absent : bootstrap.metadata (directory.file .walBoundary) nextSeed.afterPending = .ok none nextSeed.afterPending)
    (marked : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock cache, DiskTable.OpenReferenceAssembly resolved lock cache (assemble resolved lock cache))
    (allocation : OpenReferenceAllocations allocatePhase allocateToken view.phase
      (⟨.empty, 0, 0, 0⟩ : Reopened).installed publication.raw.markerDirectory.reached)
    (phaseID : phaseIdentity allocation.phase = nextFiles.nextRef)
    (tokenID : tokenIdentity allocation.token = nextFiles.nextRef + 1)
    (phaseFrame : CacheAllocationFrame view nextSeed.directoryRef nextSeed.activeRef nextSeed.pendingRef
      publication.raw.markerDirectory.reached allocation.afterPhase)
    (tokenFrame : CacheAllocationFrame view nextSeed.directoryRef nextSeed.activeRef nextSeed.pendingRef
      allocation.afterPhase allocation.afterToken)
    (phaseInodes : nextKeeper.inodes allocation.afterPhase = nextKeeper.inodes publication.raw.markerDirectory.reached)
    (tokenInodes : nextKeeper.inodes allocation.afterToken = nextKeeper.inodes allocation.afterPhase)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (phaseEffects : OpenPhaseCellEffects view.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    let recover := fun (resolved : DiskDirectory) (cache : DiskTable.OpenSyncFiles) =>
      recoverSegmentedWalWith
        (rejectFlatWalWith resolved (optionalMetadataWith (nextCalls.lookup (resolved.file .wal))))
        (optionalMetadataWith (nextCalls.lookup (resolved.file .walBoundary)))
        (marked resolved cache) (bootstrap.run resolved nextSeed.directoryRef nextSeed.activeRef nextSeed.pendingRef)
    let originalKeeper := (physical.names reboot.rebooted).modelObject observed.statChild.child
    reboot.Selected ∧
    (view.handle admitted.afterFlock admitted.lock).1.inode (view.handle admitted.afterFlock admitted.lock).2.1.description =
      captured.reached.inode fileCalls.slot.description ∧
    (view.descriptors publication.raw.afterRename).inode nextCapture.cached.description =
      (view.descriptors stop.afterRename).inode captured.cached.description ∧
    (view.descriptors nextKeeper.opened).inode (view.handle nextKeeper.opened nextKeeper.descriptor).2.1.description =
      originalKeeper ∧
    ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle)
      (after : LockedFileState WalSegmentRotation.State),
      DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      nextCalls.runOpen input nextInit makeCache (fun resolved lock cache => do
        let opened ← recover resolved cache
        installReady opened.installed allocatePhase allocateToken
          (fun phase token => pure (assemble resolved lock cache phase token))) reboot.rebooted = .ok handle.table start.reached ∧
      handle.lock = admitted.lock ∧ handle.phase = allocation.phase ∧ handle.token = allocation.token ∧
      handle.contents = view.phase ∧ handle.get = get ∧ handle.set = set ∧ handle.ptrEq = ptrEq ∧
      start.reached = allocation.afterToken ∧
      handle.files.UsesBootstrapCacheSchedules directory nextSeed.activeRef nextSeed.pendingRef nextSeed.directoryRef ∧
      view.phase start.reached handle.phase = some (.ready ⟨.empty, 0, 0, 0⟩) ∧
      view.files start.reached = after ∧ view.descriptors start.reached = start.current.ready.state.census ∧
      view.cacheAt start.reached nextSeed.directoryRef nextSeed.activeRef nextSeed.pendingRef = start.current.ready.state.cache ∧
      BootstrapReady after.image ∧
      published.afterMarkerNames (renderWalSegmentName 0) = [some observed.statChild.child] ∧
      published.afterMarkerNames "WAL.commit" = [some nextMarker.stageChild.child] ∧
      (nextKeeper.inodes start.reached).crashBytes originalKeeper = [ByteArray.empty] ∧
      (nextKeeper.inodes start.reached).crashBytes
        (nextMarker.renamedView.modelObject nextMarker.stageChild.child) = [WAL.Boundary.encode 0] ∧
      start.current.history = [] ∧ start.current.submissions = [] ∧ start.current.ready.reads = [] ∧ start.pins = [] := by
  intro recover originalKeeper
  have chosen := reboot.selects valid
  have nextValid : BootstrapValid stop.markerlessReboot.image := reboot.files ▸ chosen.valid
  obtain ⟨rootInode, lockInode, keeperChild, keeperObject, _⟩ := same.readsSelectedKeeper valid
  obtain ⟨cacheOpen, makeCache, handle, start, after, action, source, _, _, ran, _, sameLock, reference, phase, token, contents,
    getEq, setEq, compareEq, reached, locking, _, _, _, files, census, cache, _, ready, _, keeperName, markerName, keeperBytes,
    markerBytes, history, submissions, reads, pins⟩ :=
    publication.opensFromAdmission admitted modelAdmission nextValid owner metadata keeperLookup flat absent marked assemble
      constructs allocation phaseID tokenID phaseFrame tokenFrame phaseInodes tokenInodes phaseEffects ptrEq
  have directoryInode := publication.raw.markerDirectory.selectsRoot.2.2.symm.trans rootInode
  have wasKeeper := nextKeeper.settles
  have rawKeeper : (view.descriptors nextKeeper.opened).inode
      (view.handle nextKeeper.opened nextKeeper.descriptor).2.1.description = originalKeeper := by
    rw [wasKeeper.keeperHandle, ← wasKeeper.sameKeeper, keeperChild, same.names]
  have phaseReady := allocation.keepsPhase.trans allocation.initialized
  refine ⟨chosen, ?_, directoryInode, rawKeeper, cacheOpen, makeCache, handle, start, after, action, source, ran, sameLock,
    phase, token, contents, getEq, setEq, compareEq, reached, reference, ?_, files, census, cache, ready, ?_, markerName,
    ?_, ?_, history, submissions, reads, pins⟩
  · rw [← sameLock, locking]
    exact lockInode
  · rw [reached, phase]
    exact phaseReady
  · rw [← keeperChild]
    exact keeperName
  · change (nextKeeper.inodes start.reached).crashBytes selected.files.active = _ at keeperBytes
    simpa only [originalKeeper, ← keeperObject] using keeperBytes
  · rw [published.renameObjects, ← published.stageObjects, ← nextMarker.stageInode]
    exact markerBytes

end Alvoki.Storage.DiskSession.RawBootstrapMarkerDirectoryStop.BeforeEffectMarkerlessReboot
