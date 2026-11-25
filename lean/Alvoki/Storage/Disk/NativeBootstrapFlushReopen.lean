import Alvoki.Storage.Disk.BootstrapScratchRetry
import Alvoki.Storage.Disk.NativeBootstrapMarkerCollision
import Alvoki.Storage.Disk.NativeReusedBootstrapTableOpen

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

private abbrev scratchName := "WAL.commit.next"
private abbrev keeperName := renderWalSegmentName 0

variable {heap : Type} {input nextInput : FilePath} {directory : DiskDirectory}
  {before : LockedFileState WalSegmentRotation.State}
  {previous : BootstrapOpenCalls (Cache CheckpointOpenHandle) directory before}
  {capture : BootstrapCacheOpen previous.toBootstrapAdmissionCalls} {listing : BootstrapCheckedListing capture}
  {initial : BootstrapZeroKeeperRoute listing} {source : BootstrapMarkerFlushError initial}
  {survivor : BootstrapMarkerFlushSurvivor source}
  {next : BootstrapOpenCalls (Cache CheckpointOpenHandle) directory survivor.state}
  {nextCapture : BootstrapCacheOpen next.toBootstrapAdmissionCalls} {nextListing : BootstrapCheckedListing nextCapture}
  {selected : BootstrapReusedZeroKeeper nextListing} {nextMarker : BootstrapMarkerCustody nextListing}
  {handoff : BootstrapKeeperMarkerHandoff (.reused selected) nextMarker}
  {effects : BootstrapKeeperMarkerHandoff.ReturnedCensus nextMarker}
  {view : OpenCloseHeapView heap WalSegmentRotation.State} {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {inventory : DescriptorInventory} {nextAdmission : CensusOpenAdmissionReports nextInput directory inventory survivor.state}
  {calls : RawOpenAdmissionCallbacks heap} {bootstrap : FreshBootstrapCacheCalls heap}
  {admitted : RawOpenAdmissionReport nextAdmission view calls entry}
  {seed : OpenSyncCacheAllocations nextCapture.opened view init admitted.afterFlock}
  {guards : ReusedBootstrapKeeperGuards selected seed bootstrap} {keeper : ReusedBootstrapKeeperHeap guards}
  {publication : keeper.MarkerPublication handoff effects} {staging : BootstrapMarkerStageCalls heap}

/-- One reader ties the recovered scratch and keeper to the reboot
heap, the same captured directory and the guarded marker stage. The
survivor jointly supplies names and payloads. -/
structure BootstrapFlushRetryReader
    (admitted : RawOpenAdmissionReport nextAdmission view calls entry)
    (publication : keeper.MarkerPublication handoff effects)
    (collision : BootstrapMarkerCollisionHeap publication.raw (.reused selected) nextMarker staging keeper.inodes) where
  emptyCensus : (view.descriptors entry).slots = []
  rebootNames : collision.names entry = survivor.view
  rebootInodes : keeper.inodes entry = survivor.inodes
  sameRoot : nextCapture.root = capture.root
  capturedNames : nextCapture.view = collision.names entry
  selectedInodes : selected.files = keeper.inodes entry
  guardedNames : collision.names guards.afterList = collision.names entry
  staged : guards.staged = some collision.metadata

namespace BootstrapFlushRetryReader

variable {collision : BootstrapMarkerCollisionHeap publication.raw (.reused selected) nextMarker staging keeper.inodes}

/-- Both actual lookups use the selected restart image. The stage's
no-follow probe identifies the earlier scratch and its selected bytes.
The keeper is the same empty inode that survived with it. -/
theorem linksScratch (reader : BootstrapFlushRetryReader admitted publication collision) :
    view.files entry = survivor.state ∧ (view.descriptors entry).slots = [] ∧
    collision.stale.child = source.child.child ∧
    selected.statChild.child = initial.keeperChild ∧
    (keeper.inodes keeper.directoryBarrier.reached).visible
      ((collision.names keeper.directoryBarrier.reached).modelObject collision.stale.child) = survivor.scratchBytes ∧
    survivor.scratchBytes ∈ source.reachedInodes.crashBytes source.reachedInodes.active ∧
    (collision.names guards.afterList).child nextCapture.root scratchName = some source.child.child ∧
    bootstrap.metadata (directory.file .stagedWalBoundary) guards.afterList =
      .ok (some collision.metadata) guards.prepared := by
  obtain ⟨_, oldKeeper, _, _, chosenScratch, _⟩ := survivor.physical
  have sameNames := reader.capturedNames.trans reader.rebootNames
  have guarded : (collision.names guards.afterList).child nextCapture.root scratchName = some source.child.child := by
    rw [reader.guardedNames, reader.rebootNames, reader.sameRoot]
    exact survivor.scratch
  have atStage : (collision.names keeper.directoryBarrier.reached).child nextCapture.root scratchName =
      some source.child.child := by
    rw [collision.atEntry]
    change nextCapture.view.child nextCapture.root scratchName = _
    rw [sameNames, reader.sameRoot]
    exact survivor.scratch
  have stale := Option.some.inj (collision.keepsKeeper.1.symm.trans atStage)
  have existing := selected.settledKeeper.2.2.2.2.1
  have survivedKeeper : nextCapture.view.child nextCapture.root keeperName = some initial.keeperChild := by
    rw [sameNames, reader.sameRoot]
    exact oldKeeper
  have sameKeeper := Option.some.inj (existing.symm.trans survivedKeeper)
  have bytes : (keeper.inodes keeper.directoryBarrier.reached).visible
      ((collision.names keeper.directoryBarrier.reached).modelObject collision.stale.child) = survivor.scratchBytes := by
    rw [stale, collision.atEntry, collision.keeperInodes]
    change selected.files.visible (nextCapture.view.modelObject source.child.child) = _
    rw [reader.selectedInodes, reader.rebootInodes, sameNames]
    rfl
  exact ⟨admitted.entryFiles, reader.emptyCensus, stale, sameKeeper, bytes, chosenScratch,
    guarded, by simpa only [reader.staged] using guards.stageProbe⟩

variable {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}

/-- The earlier reported marker flush error leaves an admitted restart
with an absent marker and the surviving scratch. The next public open
uses that scratch in the guarded replacement and returns the empty table
from the reached publication and allocation heaps. -/
theorem opens (reader : BootstrapFlushRetryReader admitted publication collision)
    (firstAdmission : OpenAdmissionReports input directory previous.slot) (valid : BootstrapValid before.image)
    (unlock : previous.unlock.LocalFlock)
    (modelAdmission : OpenAdmissionReports nextInput directory next.slot)
    (owner : nextAdmission.owner = next.slot)
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
    (phaseID : phaseIdentity allocation.phase = next.nextRef)
    (tokenID : tokenIdentity allocation.token = next.nextRef + 1)
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
    previous.run firstAdmission = .error source.returnedError source.final ∧
    view.files entry = survivor.state ∧ (view.descriptors entry).slots = [] ∧
    survivor.state.owners (directory.file .lock) = none ∧
    survivor.state.image.metadata.active.walBoundary = none ∧
    survivor.state.image.metadata.staged .walBoundary = some (survivor.scratchBytes, false) ∧
    collision.stale.child = source.child.child ∧
    (keeper.inodes keeper.directoryBarrier.reached).visible
      ((collision.names keeper.directoryBarrier.reached).modelObject collision.stale.child) = survivor.scratchBytes ∧
    survivor.scratchBytes ∈ source.reachedInodes.crashBytes source.reachedInodes.active ∧
    (collision.names collision.afterDetach).child nextCapture.root scratchName = none ∧
    ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle)
      (after : LockedFileState WalSegmentRotation.State),
      DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      calls.runOpen nextInput init makeCache (fun resolved lock cache => do
        let opened ← recover resolved cache
        installReady opened.installed allocatePhase allocateToken
          (fun phase token => pure (assemble resolved lock cache phase token))) entry = .ok handle.table start.reached ∧
      view.files start.reached = after ∧ view.descriptors start.reached = start.current.ready.state.census ∧
      view.cacheAt start.reached seed.directoryRef seed.activeRef seed.pendingRef = start.current.ready.state.cache ∧
      next.run modelAdmission = .ok start.current.ready.state.session after ∧ BootstrapReady after.image ∧
      handoff.afterMarkerNames (renderWalSegmentName 0) = [some initial.keeperChild] ∧
      handoff.afterMarkerNames "WAL.commit" = [some collision.replacement.child] ∧
      (keeper.inodes start.reached).crashBytes survivor.inodes.active = [ByteArray.empty] ∧
      (keeper.inodes start.reached).crashBytes
        ((view.descriptors collision.created).inode (view.handle collision.created collision.handle).2.1.description) =
          [WAL.Boundary.encode 0] ∧
      handle.phase = allocation.phase ∧ handle.token = allocation.token ∧ handle.contents = view.phase ∧
      handle.get = get ∧ handle.set = set ∧ handle.ptrEq = ptrEq ∧ start.reached = allocation.afterToken ∧
      start.current.history = [] ∧ start.current.submissions = [] ∧ start.current.ready.reads = [] ∧ start.pins = [] := by
  intro recover
  obtain ⟨failed, canRetry, missing, _, scratch, vacant⟩ := survivor.afterError firstAdmission valid unlock
  obtain ⟨bootFiles, bootCensus, sameScratch, sameKeeper, seenBytes, survived, _, _⟩ := reader.linksScratch
  obtain ⟨cacheOpen, makeCache, handle, start, after, action, cacheSource, _, _, ran, _, _, _, phase, token, contents,
    getter, setter, compared, final, _, _, _, _, returnedFiles, census, cached, logical, ready,
      _, keeperName, markerName, keeperBytes, markerBytes, history, submissions, reads, pins⟩ :=
    publication.opensFromAdmission admitted modelAdmission canRetry owner metadata keeperLookup flat absent
      marked assemble constructs allocation phaseID tokenID phaseFrame tokenFrame phaseInodes tokenInodes phaseEffects ptrEq
  obtain ⟨replacement, _, replacementInode⟩ := collision.replacesChild
  have keptInode : (BootstrapZeroKeeperRoute.reused selected).settledImage.active = survivor.inodes.active := by
    change selected.files.active = survivor.inodes.active
    rw [reader.selectedInodes, reader.rebootInodes]
  rw [sameKeeper] at keeperName
  rw [← replacement] at markerName
  rw [keptInode] at keeperBytes
  rw [replacementInode] at markerBytes
  exact ⟨failed, bootFiles, bootCensus, vacant, missing, scratch, sameScratch, seenBytes, survived, collision.keepsKeeper.2.1,
    cacheOpen, makeCache, handle, start, after, action, cacheSource, ran, returnedFiles, census, cached, logical, ready,
    keeperName, markerName, keeperBytes, markerBytes, phase, token, contents, getter, setter, compared, final,
    history, submissions, reads, pins⟩

end BootstrapFlushRetryReader

end Alvoki.Storage.DiskSession
