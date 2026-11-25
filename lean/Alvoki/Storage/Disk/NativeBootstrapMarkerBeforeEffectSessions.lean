import Alvoki.Storage.Disk.NativeBootstrapMarkerBeforeEffectTableOpen
import Alvoki.Storage.Disk.NativeBootstrapMarkerStopSessions
import Alvoki.Storage.Disk.NativeFreshOpenedSessions

namespace Alvoki.Storage.DiskSession.RawBootstrapMarkerDirectoryStop.BeforeEffectMarkerlessReboot

open System SyncHandleRouting WalSegmentRepair

variable {heap : Type} {firstInput input : FilePath} {directory : DiskDirectory}
  {before : LockedFileState WalSegmentRotation.State}
  {fileCalls : BootstrapOpenCalls (Cache CheckpointOpenHandle) directory before}
  {captured : BootstrapCacheOpen fileCalls.toBootstrapAdmissionCalls} {listed : BootstrapCheckedListing captured}
  {firstInventory : DescriptorInventory} {firstAdmission : CensusOpenAdmissionReports firstInput directory firstInventory before}
  {view : OpenCloseHeapView heap WalSegmentRotation.State}
  {firstCalls : RawOpenAdmissionCallbacks heap} {firstInit : OpenSyncCacheCallbacks heap} {firstEntry : heap}
  {firstAdmitted : RawOpenAdmissionReport firstAdmission view firstCalls firstEntry}
  {seed : OpenSyncCacheAllocations captured.opened view firstInit firstAdmitted.afterFlock}
  {calls : FreshBootstrapCacheCalls heap}
  {observed : BootstrapReusedZeroKeeper listed} {guards : ReusedBootstrapKeeperGuards observed seed calls}
  {keeper : ReusedBootstrapKeeperHeap guards} {stop : RawBootstrapMarkerDirectoryStop keeper}
  {marker : BootstrapMarkerRenamed listed} {handoff : BootstrapKeeperMarkerRename (.reused observed) marker}
  {physical : stop.Physical handoff} {reboot : BeforeEffectMarkerlessReboot physical}
  {nextFiles : BootstrapOpenCalls (Cache CheckpointOpenHandle) directory stop.markerlessReboot}
  {nextCapture : BootstrapCacheOpen nextFiles.toBootstrapAdmissionCalls}
  {nextListing : BootstrapCheckedListing nextCapture} {selected : BootstrapReusedZeroKeeper nextListing}
  {inventory : DescriptorInventory} {admission : CensusOpenAdmissionReports input directory inventory stop.markerlessReboot}
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

/-- The first open stops before the final directory fsync takes effect.
The selected markerless reboot starts the second public open. Its exact
empty returned table and heap start the reported client suffix. -/
theorem executesOpenedSessions (same : SameRestart reboot selected) (valid : BootstrapValid before.image)
    (firstOwner : firstAdmission.owner = fileCalls.slot)
    (firstLock : (view.handle stop.afterRename firstAdmitted.lock).2.1 = firstAdmission.owner)
    (firstMetadata : ∀ path, calls.metadata path = optionalMetadataWith (firstCalls.lookup path))
    (firstKeeper : guards.metadataLookup (directory.file (.walSegment 0)) =
      firstCalls.lookup (directory.file (.walSegment 0)))
    (firstFlat : calls.metadata (directory.file .wal) seed.afterPending = .ok none seed.afterPending)
    (firstAbsent : calls.metadata (directory.file .walBoundary) seed.afterPending = .ok none seed.afterPending)
    (firstMarked : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (firstInstall : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap DiskTable)
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
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)
    (files : heap → LockedFileState FileImage) (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray) :
    let clientView := view.withFileProjection files
    let recover := fun (resolved : DiskDirectory) (cache : DiskTable.OpenSyncFiles) =>
      recoverSegmentedWalWith
        (rejectFlatWalWith resolved (optionalMetadataWith (nextCalls.lookup (resolved.file .wal))))
        (optionalMetadataWith (nextCalls.lookup (resolved.file .walBoundary)))
        (marked resolved cache) (bootstrap.run resolved nextSeed.directoryRef nextSeed.activeRef nextSeed.pendingRef)
    PublicStop firstAdmitted stop firstMarked firstInstall ∧ reboot.Selected ∧
    ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles) (start : NativeOpenedSessionPoint heap),
      DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      nextCalls.runOpen input nextInit makeCache (fun resolved lock cache => do
        let opened ← recover resolved cache
        installReady opened.installed allocatePhase allocateToken
          (fun phase token => pure (assemble resolved lock cache phase token))) reboot.rebooted =
        .ok start.handle.table start.position.reached ∧
      start.handle.lock = admitted.lock ∧ start.handle.phase = allocation.phase ∧ start.handle.token = allocation.token ∧
      start.handle.contents = clientView.phase ∧ start.handle.get = get ∧ start.handle.set = set ∧ start.handle.ptrEq = ptrEq ∧
      start.position.reached = allocation.afterToken ∧
      start.handle.files.UsesBootstrapCacheSchedules directory nextSeed.activeRef nextSeed.pendingRef nextSeed.directoryRef ∧
      clientView.phase start.position.reached start.handle.phase = some (.ready ⟨.empty, 0, 0, 0⟩) ∧
      clientView.descriptors start.position.reached = start.position.current.ready.state.census ∧
      clientView.cacheAt start.position.reached nextSeed.directoryRef nextSeed.activeRef nextSeed.pendingRef =
        start.position.current.ready.state.cache ∧
      start.position.current.history = [] ∧ start.position.current.submissions = [] ∧
      start.position.current.ready.reads = [] ∧ start.position.pins = [] ∧
      NativeOpenedSessionTrace.ReplaysFromEmpty clientView names bytes start := by
  intro clientView recover
  have interrupted := stopsPublicSchedule (admitted := firstAdmitted) physical firstOwner firstLock firstMetadata
    firstKeeper firstFlat firstAbsent firstMarked firstInstall
  obtain ⟨selectedRestart, _, _, _, cacheOpen, makeCache, handle, position, _, action, source, ran, lock,
    phaseRef, tokenRef, contents, got, setEq, compared, reached, cacheRefs, phase, _, census, cache,
    _, _, _, _, _, history, submissions, reads, pins⟩ :=
    opensEmptyTable (admitted := admitted) same valid publication modelAdmission owner metadata keeperLookup flat absent
      marked assemble constructs allocation phaseID tokenID phaseFrame tokenFrame phaseInodes tokenInodes phaseEffects ptrEq
  let start : NativeOpenedSessionPoint heap := ⟨handle, position⟩
  exact ⟨interrupted, selectedRestart, cacheOpen, makeCache, start, action, source, ran, lock, phaseRef, tokenRef,
    contents, got, setEq, compared, reached, cacheRefs, phase, census, cache, history, submissions, reads, pins,
    NativeOpenedSessionTrace.replaysFromEmpty start history submissions reads⟩

end Alvoki.Storage.DiskSession.RawBootstrapMarkerDirectoryStop.BeforeEffectMarkerlessReboot
