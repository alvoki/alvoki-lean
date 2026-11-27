import Alvoki.Storage.Disk.Proofs.Bootstrap.NativeReusedBootstrapKeeperHeap
import Alvoki.Storage.Disk.Proofs.Native.Open.NativeRawOpenAdmission

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

private abbrev MarkerDirectoryIssue := FilePath × IO.FS.Handle
private abbrev StoppedOpen (heap : Type) := ExceptT IO.Error (EStateM MarkerDirectoryIssue heap)

private def returned {heap α : Type} (call : EStateM IO.Error heap α) : StoppedOpen heap α :=
  fun before => match call before with
    | .ok value after => .ok (.ok value) after
    | .error cause after => .ok (.error cause) after

private def issueDirectory {heap : Type} (path : FilePath) (handle : IO.FS.Handle) : StoppedOpen heap Unit :=
  fun before => .error (path, handle) before

private def markerDirectoryCall {heap : Type} (calls : FreshBootstrapCacheCalls heap) (directory : DiskDirectory)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) : StoppedOpen heap Unit :=
  SyncPathGroup.run
    (fun path => syncWithHandles directory.path path (returned (calls.readDirectory cached))
      (returned (calls.readPending pending)) (fun entries => returned (calls.setPending pending entries))
      (returned (calls.readActive active)) (fun path => returned (calls.openRead path)) (issueDirectory directory.path))
    #[directory.path]

private def publishUntilDirectory {heap : Type} (calls : FreshBootstrapCacheCalls heap) (directory : DiskDirectory)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) : StoppedOpen heap Reopened := do
  Publication.run fun step =>
    match step with
    | .syncDirectory => markerDirectoryCall calls directory cached active pending
    | other => returned (Publication.performReplacement
        (calls.stagePending pending · (WAL.Boundary.encode 0)) (calls.toRawSyncCalls.group directory.path cached active pending) calls.rename
        (directory.file .stagedWalBoundary) directory.path (fun _ => directory.file .walBoundary) #[] other)
  pure ⟨.empty, 0, 0, 0⟩

private def bootstrapUntilDirectory {heap : Type} (calls : FreshBootstrapCacheCalls heap) (directory : DiskDirectory)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) : StoppedOpen heap Reopened := do
  let empty ← returned (prepareBootstrapWith directory calls.list calls.readEmpty calls.metadata)
  returned (WalSegmentRotation.runAt directory 0 (fun _ => pure empty)
    (calls.createPending pending) (fun path => calls.toRawSyncCalls.group directory.path cached active pending #[path]))
  publishUntilDirectory calls directory cached active pending

/-- The markerless worker interpreted through its final directory
sync issue, for use at the start of a multi-session proof. -/
abbrev FreshBootstrapCacheCalls.untilMarkerDirectory {heap : Type} (calls : FreshBootstrapCacheCalls heap)
    (directory : DiskDirectory) (cached : IO.Ref (Option IO.FS.Handle))
    (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) : StoppedOpen heap Reopened :=
  bootstrapUntilDirectory calls directory cached active pending

/-- Interpret the native open callbacks with separate returned errors
and a terminal observation of the final bootstrap directory fsync. -/
def RawOpenAdmissionCallbacks.runUntilBootstrapDirectory {heap : Type} (calls : RawOpenAdmissionCallbacks heap)
    (input : FilePath) (init : OpenSyncCacheCallbacks heap)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → StoppedOpen heap Reopened)
    (marked : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap DiskTable) :
    EStateM MarkerDirectoryIssue heap (Except IO.Error DiskTable) :=
  (do
    let (directory, lock) ← returned (DiskTable.withOpenAdmission input calls.realPath calls.lookup calls.openAppend
      (fun resolved handle => pure (resolved, handle)))
    openWithLock (returned (calls.flock lock)) (fun _ => IO.userError s!"database already open: {directory.path}")
      (fun _ => returned (calls.unlock lock)) fun _ => do
        let cache ← returned (openSyncFilesWith (init.openDirectory directory.path) init.newRef init.newRef init.newRef makeCache)
        let opened ← recoverSegmentedWalWith
          (returned (rejectFlatWalWith directory (optionalMetadataWith (calls.lookup (directory.file .wal)))))
          (returned (optionalMetadataWith (calls.lookup (directory.file .walBoundary))))
          (returned (marked directory cache)) (bootstrap directory cache)
        returned (install directory lock cache opened) : StoppedOpen heap DiskTable).run

variable {heap : Type} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {fileCalls : BootstrapOpenCalls (Cache CheckpointOpenHandle) directory before}
  {captured : BootstrapCacheOpen fileCalls.toBootstrapAdmissionCalls} {listed : BootstrapCheckedListing captured}
  {view : OpenCloseHeapView heap WalSegmentRotation.State} {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {seed : OpenSyncCacheAllocations captured.opened view init entry} {calls : FreshBootstrapCacheCalls heap}
  {observed : BootstrapReusedZeroKeeper listed} {guards : ReusedBootstrapKeeperGuards observed seed calls}

/-- Either keeper route feeds the same marker stage, file sync and rename.
The final group selects the original directory handle at its fsync issue. -/
structure BootstrapMarkerDirectoryStopPrefix
    (seed : OpenSyncCacheAllocations captured.opened view init entry) (calls : FreshBootstrapCacheCalls heap)
    (beforeMarker : heap) where
  markerHandle : CheckpointOpenHandle
  marker : BootstrapPendingObservation view calls.toBootstrapPendingCalls directory .marker seed.pendingRef markerHandle
    beforeMarker
  markerOK : marker.result = .ok ()
  afterRename : heap
  renamed : calls.rename (directory.file .stagedWalBoundary) (directory.file .walBoundary) marker.reached =
    .ok () afterRename
  read : calls.readDirectory seed.directoryRef afterRename = .ok (some seed.handle) afterRename
  rawHandle : view.handle afterRename seed.handle = (view.descriptors afterRename, captured.cached, 0)
  live : captured.cached ∈ (view.descriptors afterRename).slots
  sameInode : (view.descriptors afterRename).inode captured.cached.description =
    (captured.initial.insert captured.cached captured.opened.free).inode captured.cached.description

namespace BootstrapMarkerDirectoryStopPrefix

variable {beforeMarker : heap} (seen : BootstrapMarkerDirectoryStopPrefix seed calls beforeMarker)

private theorem issues :
    (markerDirectoryCall calls directory seed.directoryRef seed.activeRef seed.pendingRef).run seen.afterRename =
      .error (directory.path, seed.handle) seen.afterRename := by
  change markerDirectoryCall calls directory seed.directoryRef seed.activeRef seed.pendingRef seen.afterRename = _
  unfold markerDirectoryCall SyncPathGroup.run
  rw [← Array.forIn_toList]
  simp [syncWithHandles, returned, seen.read, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
    EStateM.bind, MonadExcept.tryCatch, MonadExceptOf.tryCatch, tryCatchThe, ExceptT.tryCatch,
    Pure.pure, ExceptT.pure, EStateM.pure, issueDirectory]

private theorem publishesUntil :
    (publishUntilDirectory calls directory seed.directoryRef seed.activeRef seed.pendingRef).run
      beforeMarker =
      .error (directory.path, seed.handle) seen.afterRename := by
  obtain ⟨_, _, cache, _, _, _, references, path, _⟩ := seed.installs
  obtain ⟨_, staged, synced, _⟩ := seen.marker.returns cache references path
  rw [seen.markerOK] at synced
  have stageReturn : calls.stagePending seed.pendingRef (directory.file .stagedWalBoundary) (WAL.Boundary.encode 0)
      beforeMarker = .ok () seen.marker.recorded := staged
  have fileReturn : calls.toRawSyncCalls.group directory.path seed.directoryRef seed.activeRef seed.pendingRef
      #[directory.file .stagedWalBoundary] seen.marker.recorded = .ok () seen.marker.reached := synced
  have issued := seen.issues
  change markerDirectoryCall calls directory seed.directoryRef seed.activeRef seed.pendingRef seen.afterRename = _ at issued
  unfold publishUntilDirectory Publication.run Publication.steps
  simp only [List.forM_eq_forM, List.forM_cons, Publication.performReplacement, Array.push_empty,
    Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run, EStateM.bind, returned,
    stageReturn, fileReturn, seen.renamed, issued]

/-- The returned preparation and keeper callbacks determine the entry
heap of the one shared marker publication. -/
theorem stopsHeld {prepared : heap} {empty : Option ByteArray}
    (prepare : prepareBootstrapWith directory calls.list calls.readEmpty calls.metadata seed.afterPending =
      .ok empty prepared)
    (rotate : WalSegmentRotation.runAt directory 0 (fun _ => EStateM.pure empty) (calls.createPending seed.pendingRef)
      (fun path => calls.toRawSyncCalls.group directory.path seed.directoryRef seed.activeRef seed.pendingRef #[path]) prepared =
      .ok () beforeMarker) :
    (calls.untilMarkerDirectory directory seed.directoryRef seed.activeRef seed.pendingRef).run seed.afterPending =
      .error (directory.path, seed.handle) seen.afterRename := by
  change WalSegmentRotation.runAt directory 0 (fun _ => pure empty) (calls.createPending seed.pendingRef)
    (fun path => calls.toRawSyncCalls.group directory.path seed.directoryRef seed.activeRef seed.pendingRef #[path]) prepared = _ at rotate
  have published := seen.publishesUntil
  change publishUntilDirectory calls directory seed.directoryRef seed.activeRef seed.pendingRef beforeMarker = _ at published
  simp only [FreshBootstrapCacheCalls.untilMarkerDirectory, bootstrapUntilDirectory, returned, prepare, Bind.bind,
    ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run, EStateM.bind, rotate, published]

end BootstrapMarkerDirectoryStopPrefix

/-- The admitted public schedule runs the held markerless worker on the
heap returned by the same cache initialization. A terminal directory issue
does not enter the ordinary unlock handler or install a table. -/
theorem RawOpenAdmissionReport.stopsBootstrapDirectory
    {input : FilePath} {inventory : DescriptorInventory}
    {admission : CensusOpenAdmissionReports input directory inventory before}
    {raw : RawOpenAdmissionCallbacks heap}
    (admitted : RawOpenAdmissionReport admission view raw entry)
    (heldSeed : OpenSyncCacheAllocations captured.opened view init admitted.afterFlock)
    {cache : DiskTable.OpenSyncFiles}
    {makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles}
    (initialized : openSyncFilesWith (init.openDirectory directory.path) init.newRef init.newRef init.newRef makeCache
      admitted.afterFlock = .ok cache heldSeed.afterPending)
    (metadata : ∀ path, calls.metadata path = optionalMetadataWith (raw.lookup path))
    (flat : calls.metadata (directory.file .wal) heldSeed.afterPending = .ok none heldSeed.afterPending)
    (absent : calls.metadata (directory.file .walBoundary) heldSeed.afterPending = .ok none heldSeed.afterPending)
    {cutHeap : heap}
    (cut : (calls.untilMarkerDirectory directory heldSeed.directoryRef heldSeed.activeRef heldSeed.pendingRef).run
      heldSeed.afterPending = .error (directory.path, heldSeed.handle) cutHeap)
    (marked : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap DiskTable) :
    raw.runUntilBootstrapDirectory input init makeCache
      (fun resolved _ => calls.untilMarkerDirectory resolved heldSeed.directoryRef heldSeed.activeRef heldSeed.pendingRef)
      marked install entry = .error (directory.path, heldSeed.handle) cutHeap := by
  have flatGuard : (rejectFlatWalWith directory (optionalMetadataWith (raw.lookup (directory.file .wal))) :
      EStateM IO.Error heap Unit) heldSeed.afterPending = .ok () heldSeed.afterPending := by
    rw [← metadata]
    simp [rejectFlatWalWith, flat, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  have noMarker := (metadata (directory.file .walBoundary)).symm ▸ absent
  change bootstrapUntilDirectory calls directory heldSeed.directoryRef heldSeed.activeRef heldSeed.pendingRef
    heldSeed.afterPending = _ at cut
  have admissionPrefix := DiskTable.withOpenAdmission_lockOpen raw.realPath raw.lookup raw.openAppend
    (fun resolved handle => pure (resolved, handle))
    admitted.resolved admitted.flat admitted.lockProbe admission.safe
  rw [admitted.appended] at admissionPrefix
  change DiskTable.withOpenAdmission input raw.realPath raw.lookup raw.openAppend
    (fun resolved handle => EStateM.pure (resolved, handle)) entry =
      .ok (directory, admitted.lock) admitted.afterAppend at admissionPrefix
  unfold RawOpenAdmissionCallbacks.runUntilBootstrapDirectory
  simp only [openWithLock, recoverSegmentedWalWith, returned, admissionPrefix, admitted.acquired, initialized,
    flatGuard, noMarker, cut, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run,
    EStateM.bind, Pure.pure, MonadExcept.tryCatch, MonadExceptOf.tryCatch,
    tryCatchThe, ExceptT.tryCatch, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]

/-- The same marker stop following a keeper that already existed at the
start of the admitted bootstrap. -/
structure RawBootstrapMarkerDirectoryStop (keeper : ReusedBootstrapKeeperHeap guards)
    extends BootstrapMarkerDirectoryStopPrefix seed calls keeper.directoryBarrier.reached

namespace RawBootstrapMarkerDirectoryStop

variable {keeper : ReusedBootstrapKeeperHeap guards} (seen : RawBootstrapMarkerDirectoryStop keeper)

theorem stopsHeldBootstrap :
    (bootstrapUntilDirectory calls directory seed.directoryRef seed.activeRef seed.pendingRef).run seed.afterPending =
      .error (directory.path, seed.handle) seen.afterRename := by
  let sync := calls.toRawSyncCalls.group directory.path seed.directoryRef seed.activeRef seed.pendingRef
  have rotates : WalSegmentRotation.runAt directory 0 (fun _ => EStateM.pure (some ByteArray.empty))
      (calls.createPending seed.pendingRef) (fun path => sync #[path]) guards.prepared =
      .ok () keeper.directoryBarrier.reached := by
    rw [WalSegmentRotation.runAt_fileEffects]
    simp [WalSegmentRotation.observeSuccessorWith, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
      sync, keeper.syncsKeeper, keeper.directoryBarrier.returns]
  exact seen.toBootstrapMarkerDirectoryStopPrefix.stopsHeld guards.prepare rotates


/-- Project only the completed callbacks before the stop. The physical
prefix uses the original keeper and the same marker write, fsync and
rename. It has no observation of a returned directory fsync. -/
structure Physical {marker : BootstrapMarkerRenamed listed}
    (handoff : BootstrapKeeperMarkerRename (.reused observed) marker) where
  names : heap → DirectoryReadNamespace
  renamedNames : names seen.afterRename = marker.renamedView
  staged : BootstrapFileProjection.result view keeper.inodes view.handle
      (calls.stage (directory.file .stagedWalBoundary) (WAL.Boundary.encode 0) keeper.directoryBarrier.reached) =
    marker.toBootstrapMarkerStaging.stage (directory.file .stagedWalBoundary) (WAL.Boundary.encode 0)
      (BootstrapFileProjection.atHeap view keeper.inodes keeper.directoryBarrier.reached)
  remembered : BootstrapFileProjection.atHeap view keeper.inodes seen.marker.recorded =
    BootstrapFileProjection.atHeap view keeper.inodes seen.marker.produced
  consumed : BootstrapFileProjection.atHeap view keeper.inodes seen.marker.consumed =
    BootstrapFileProjection.atHeap view keeper.inodes seen.marker.recorded
  fileSynced : BootstrapFileProjection.result view keeper.inodes (fun _ value => value)
      (calls.fsync seen.marker.handle seen.marker.consumed) =
    marker.fsync (view.handle seen.marker.consumed seen.marker.handle)
      (BootstrapFileProjection.atHeap view keeper.inodes seen.marker.consumed)
  renamed : BootstrapFileProjection.result view keeper.inodes (fun _ value => value)
      (calls.rename (directory.file .stagedWalBoundary) (directory.file .walBoundary) seen.marker.reached) =
    marker.rename (directory.file .stagedWalBoundary) (directory.file .walBoundary)
      (BootstrapFileProjection.atHeap view keeper.inodes seen.marker.reached)
  census : view.descriptors seen.afterRename = marker.toBootstrapMarkerStaging.inventory.afterDrops
    (marker.beforeFile ++ marker.afterFile)
  owners : (view.files seen.afterRename).owners = (view.files keeper.directoryBarrier.reached).owners

structure Reached {marker : BootstrapMarkerRenamed listed}
    {handoff : BootstrapKeeperMarkerRename (.reused observed) marker}
    (physical : seen.Physical handoff) : Prop where
  image : (view.files seen.afterRename).image = marker.toBootstrapMarkerSynced.renamedState
  inodes : keeper.inodes seen.afterRename = marker.toBootstrapMarkerSynced.inodeSynced
  keeperBinding : (physical.names seen.afterRename).child captured.root (renderWalSegmentName 0) =
    some observed.statChild.child
  keeperBytes : (keeper.inodes seen.afterRename).crashBytes
    ((physical.names seen.afterRename).modelObject observed.statChild.child) = [ByteArray.empty]
  markerBinding : (physical.names seen.afterRename).child captured.root "WAL.commit" = some marker.stageChild.child
  separate : marker.stageChild.child ≠ observed.statChild.child
  markerBytes : (keeper.inodes seen.afterRename).crashBytes
    ((physical.names seen.afterRename).modelObject marker.stageChild.child) = [WAL.Boundary.encode 0]
  scratchGone : (physical.names seen.afterRename).child captured.root "WAL.commit.next" = none
  owner : (view.files seen.afterRename).owners =
    before.owners.set (directory.file .lock) (some fileCalls.slot.description)
  ownerLive : fileCalls.slot ∈ (view.descriptors seen.afterRename).slots
  directoryHandle : view.handle seen.afterRename seed.handle =
    (view.descriptors seen.afterRename, captured.cached, 0)
  directoryLive : captured.cached ∈ (view.descriptors seen.afterRename).slots
  directoryInode : (physical.names seen.afterRename).modelObject captured.root =
    (view.descriptors seen.afterRename).inode captured.cached.description

/-- The stopped raw action reaches the real canonical zero marker
and the unchanged empty keeper on distinct inodes. The owner's
original directory slot is still live at issue. -/
theorem reachesPhysical {marker : BootstrapMarkerRenamed listed}
    {handoff : BootstrapKeeperMarkerRename (.reused observed) marker}
    (raw : seen.Physical handoff) : seen.Reached raw := by
  have settled := keeper.settles
  have stageInput : BootstrapFileProjection.atHeap view keeper.inodes keeper.directoryBarrier.reached =
      (marker.toBootstrapMarkerStaging.inputState, marker.initial) :=
    Prod.ext settled.image (settled.inodes.trans handoff.stageInput.symm)
  have staged := raw.staged
  have rawStage : calls.stage (directory.file .stagedWalBoundary) (WAL.Boundary.encode 0) keeper.directoryBarrier.reached =
      .ok seen.marker.handle seen.marker.produced := seen.marker.returnedHandle
  rw [rawStage, stageInput, marker.toBootstrapMarkerStaging.stageReturns] at staged
  obtain ⟨stageHandle, stageFiles⟩ := EStateM.Result.ok.inj staged
  have handle := seen.marker.sameIssuing.trans (seen.marker.sameProduced.symm.trans stageHandle)
  have synced := raw.fileSynced
  have rawSync := seen.marker.syncReturned
  rw [seen.markerOK] at rawSync
  rw [rawSync, handle, raw.consumed, raw.remembered, stageFiles, marker.fileSynced] at synced
  have syncedFiles := (EStateM.Result.ok.inj synced).2
  have renamed := raw.renamed
  rw [seen.renamed, syncedFiles, marker.renameReturned] at renamed
  have files := (EStateM.Result.ok.inj renamed).2
  have inodes : keeper.inodes seen.afterRename = marker.toBootstrapMarkerSynced.inodeSynced := congrArg Prod.snd files
  obtain ⟨separate, keeperName, keeperInode, _, _, keeperBytes⟩ := handoff.renamedKeeper
  have markerName := marker.liveChild.binds
  rw [marker.liveChild.atRoot, marker.liveChild.atName, marker.sameChild] at markerName
  have markerInode : marker.renamedView.modelObject marker.stageChild.child = marker.inodeState.active := by
    rw [handoff.renameObjects, ← handoff.stageObjects, marker.stageInode]
  refine ⟨congrArg Prod.fst files, inodes, raw.renamedNames.symm ▸ keeperName, ?_,
    raw.renamedNames.symm ▸ markerName, separate, ?_, raw.renamedNames.symm ▸ marker.stageGone,
    raw.owners.trans settled.owners, raw.census.symm ▸ marker.lockLive, seen.rawHandle, seen.live, ?_⟩
  · change marker.renamedView.modelObject observed.statChild.child = _ at keeperInode
    rw [inodes, raw.renamedNames, keeperInode]
    exact keeperBytes
  · rw [inodes, raw.renamedNames, markerInode]
    simp [BootstrapMarkerSynced.inodeSynced, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, marker.stageBytes]
  · obtain ⟨_, _, _, _, object, _⟩ := captured.opened.captures
    rw [raw.renamedNames, handoff.renameObjects]
    exact object.trans seen.sameInode.symm

variable {input : FilePath} {inventory : DescriptorInventory}
  {admission : CensusOpenAdmissionReports input directory inventory before}
  {raw : RawOpenAdmissionCallbacks heap}

/-- The held recovery reaches the fsync issue with no ordinary outcome.
The lock error handler and installation continuation receive no result. -/
theorem stopsPublicOpen
    (admitted : RawOpenAdmissionReport admission view raw entry)
    {heldSeed : OpenSyncCacheAllocations captured.opened view init admitted.afterFlock}
    {heldGuards : ReusedBootstrapKeeperGuards observed heldSeed calls}
    {heldKeeper : ReusedBootstrapKeeperHeap heldGuards}
    (stop : RawBootstrapMarkerDirectoryStop heldKeeper)
    {marker : BootstrapMarkerRenamed listed}
    {handoff : BootstrapKeeperMarkerRename (.reused observed) marker}
    (physical : stop.Physical handoff)
    (owner : admission.owner = fileCalls.slot)
    (lockHandle : (view.handle stop.afterRename admitted.lock).2.1 = admission.owner)
    (metadata : ∀ path, calls.metadata path = optionalMetadataWith (raw.lookup path))
    (keeperLookup : heldGuards.metadataLookup (directory.file (.walSegment 0)) =
      raw.lookup (directory.file (.walSegment 0)))
    (flat : calls.metadata (directory.file .wal) heldSeed.afterPending = .ok none heldSeed.afterPending)
    (absent : calls.metadata (directory.file .walBoundary) heldSeed.afterPending = .ok none heldSeed.afterPending)
    (marked : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap DiskTable) :
    ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles) (cache : DiskTable.OpenSyncFiles),
      DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      openSyncFilesWith (init.openDirectory directory.path) init.newRef init.newRef init.newRef makeCache
        admitted.afterFlock = .ok cache heldSeed.afterPending ∧
      cache.UsesBootstrapCacheSchedules directory heldSeed.activeRef heldSeed.pendingRef heldSeed.directoryRef ∧
      calls.readEmpty (directory.file (.walSegment 0)) = WalSegmentRotation.readEmptyWith
        (raw.lookup (directory.file (.walSegment 0))) (directory.file (.walSegment 0)) WAL.Boundary.missingOpenMarker ∧
      raw.runUntilBootstrapDirectory input init makeCache
        (fun resolved _ => bootstrapUntilDirectory calls resolved heldSeed.directoryRef heldSeed.activeRef heldSeed.pendingRef)
        marked install entry = .error (directory.path, heldSeed.handle) stop.afterRename ∧
      stop.Reached physical ∧
      (view.handle stop.afterRename admitted.lock).2.1 ∈ (view.descriptors stop.afterRename).slots := by
  have reached := stop.reachesPhysical physical
  have lockLive : (view.handle stop.afterRename admitted.lock).2.1 ∈ (view.descriptors stop.afterRename).slots := by
    rw [lockHandle, owner]
    exact reached.ownerLive
  obtain ⟨cacheOpen, makeCache, cache, isOpen, source, initialized, references, path, _⟩ := heldSeed.installs
  have schedules := cache.bootstrapCacheSchedules references path
  refine ⟨cacheOpen, makeCache, cache, isOpen, source, initialized, schedules, ?_, ?_, reached, lockLive⟩
  · rw [heldGuards.source, keeperLookup]
  exact admitted.stopsBootstrapDirectory heldSeed initialized metadata flat absent
    stop.stopsHeldBootstrap marked install

end RawBootstrapMarkerDirectoryStop

end Alvoki.Storage.DiskSession
