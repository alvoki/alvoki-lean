import Alvoki.Storage.Disk.NativeBootstrapMarkerPhysical

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

variable {heap : Type} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {fileCalls : BootstrapOpenCalls (Cache CheckpointOpenHandle) directory before}
  {captured : BootstrapCacheOpen fileCalls.toBootstrapAdmissionCalls}
  {listed : BootstrapCheckedListing captured}
  {view : OpenCloseHeapView heap WalSegmentRotation.State} {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {seed : OpenSyncCacheAllocations captured.opened view init entry} {calls : FreshBootstrapCacheCalls heap}

private abbrev zeroKeeper (directory : DiskDirectory) := directory.file (.walSegment 0)

/-- The markerless worker reaches the already-present keeper through a
complete listing and the no-follow, private, empty regular-file guard.
Neither the checked lookup nor the stage probe puts a handle in the cache. -/
structure ReusedBootstrapKeeperGuards (observed : BootstrapReusedZeroKeeper listed)
    (seed : OpenSyncCacheAllocations captured.opened view init entry) (calls : FreshBootstrapCacheCalls heap) where
  afterList : heap
  prepared : heap
  metadataLookup : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata)
  staged : Option IO.FS.Metadata
  listing : calls.list directory.path seed.afterPending = .ok (listed.scan.scan.entries directory.path) afterList
  listedCensus : view.descriptors afterList = listed.scan.afterClose
  source : calls.readEmpty (zeroKeeper directory) = WalSegmentRotation.readEmptyWith
    (metadataLookup (zeroKeeper directory)) (zeroKeeper directory) WAL.Boundary.missingOpenMarker
  lookup : metadataLookup (zeroKeeper directory) afterList = .ok (.ok observed.metadata) afterList
  stageProbe : calls.metadata (directory.file .stagedWalBoundary) afterList = .ok staged prepared
  stageRegular : ∀ metadata, staged = some metadata → metadata.type = .file
  preparedCensus : view.descriptors prepared = listed.scan.afterClose.afterDrops observed.beforeOpen
  preparedFiles : view.files prepared = view.files seed.afterPending

theorem ReusedBootstrapKeeperGuards.prepare {observed : BootstrapReusedZeroKeeper listed}
    (seen : ReusedBootstrapKeeperGuards observed seed calls) :
    prepareBootstrapWith directory calls.list calls.readEmpty calls.metadata seed.afterPending =
      .ok (some ByteArray.empty) seen.prepared := by
  have regular : (observed.metadata.type == .file) = true := by rw [observed.regular]; rfl
  have lookup : calls.readEmpty (zeroKeeper directory) seen.afterList = .ok (some ByteArray.empty) seen.afterList := by
    rw [seen.source]
    simp [WalSegmentRotation.readEmptyWith, optionalMetadataWith, checkPrivateRegularWith, seen.lookup, regular,
      observed.singleLink, observed.size, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  have stage := seen.stageProbe
  cases value : seen.staged with
  | none =>
    simp [prepareBootstrapWith, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
      seen.listing, listed.entries.2, lookup, stage, value]
  | some metadata =>
    have kind : (metadata.type == .file) = true := by rw [seen.stageRegular metadata value]; rfl
    simp [prepareBootstrapWith, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
      seen.listing, listed.entries.2, lookup, stage, value, kind]

/-- The singleton keeper sync misses the original pending and active
cells. Its successful raw read and fsync identify the checked inode.
The file callback's return includes the reported release of the
unretained read slot before the original directory handle is synced. -/
structure ReusedBootstrapKeeperHeap {observed : BootstrapReusedZeroKeeper listed}
    (guards : ReusedBootstrapKeeperGuards observed seed calls) where
  inodes : heap → WalInodeImage
  descriptor : IO.FS.Handle
  opened : heap
  released : heap
  pendingLoaded : calls.readPending seed.pendingRef guards.prepared = .ok [] guards.prepared
  activeLoaded : calls.readActive seed.activeRef guards.prepared = .ok none guards.prepared
  atKeeper : BootstrapFileProjection.atHeap view inodes guards.prepared = (before.image, observed.files)
  rawOpen : calls.openRead (zeroKeeper directory) guards.prepared = .ok descriptor opened
  openProjection : BootstrapFileProjection.result view inodes view.handle
      (calls.openRead (zeroKeeper directory) guards.prepared) =
    observed.openRead (zeroKeeper directory) (BootstrapFileProjection.atHeap view inodes guards.prepared)
  liveCensus : view.descriptors opened =
    ((listed.scan.afterClose.afterDrops observed.beforeOpen).insert observed.slot observed.free).afterDrops observed.beforeFile
  rawSynced : calls.fsync descriptor opened = .ok () released
  fileProjection : BootstrapFileProjection.result view inodes (fun _ value => value) (calls.fsync descriptor opened) =
    observed.fsync (view.handle opened descriptor) (BootstrapFileProjection.atHeap view inodes opened)
  earlierDrops : List LockReferenceDrop
  retired : observed.afterFile = earlierDrops ++ [observed.slot.closeEvent]
  releasedCensus : view.descriptors released = (view.descriptors opened).afterDrops observed.afterFile
  directoryBarrier : FreshBootstrapDirectoryBarrier seed calls released
  directoryProjection : BootstrapFileProjection.result view inodes (fun _ value => value) (calls.fsync seed.handle released) =
    observed.fsync (captured.reached, captured.cached, 0) (BootstrapFileProjection.atHeap view inodes released)
  finalCensus : view.descriptors directoryBarrier.reached = view.descriptors released
  keptDirectory : view.directory released seed.directoryRef = some seed.handle
  keptActive : view.active released seed.activeRef = none
  keptPending : view.pending released seed.pendingRef = []
  keptHandle : view.handle directoryBarrier.reached seed.handle = view.handle seed.afterPending seed.handle
  openOwners : (view.files opened).owners = (view.files guards.prepared).owners
  fileOwners : (view.files released).owners = (view.files opened).owners
  directoryOwners : (view.files directoryBarrier.reached).owners = (view.files released).owners

namespace ReusedBootstrapKeeperHeap

variable {observed : BootstrapReusedZeroKeeper listed} {guards : ReusedBootstrapKeeperGuards observed seed calls}

theorem syncsKeeper (seen : ReusedBootstrapKeeperHeap guards) :
    calls.sync directory seed.directoryRef seed.activeRef seed.pendingRef #[zeroKeeper directory] guards.prepared =
      .ok () seen.released := by
  rw [FreshBootstrapCacheCalls.sync, SyncPathGroup.run_single]
  simp [syncWithHandles, Bind.bind, EStateM.bind, zeroPath_ne_directory directory, seen.pendingLoaded,
    seen.activeLoaded, seen.rawOpen, seen.rawSynced]

structure Settled (seen : ReusedBootstrapKeeperHeap guards) : Prop where
  keeperHandle : view.handle seen.opened seen.descriptor =
    ((listed.scan.afterClose.afterDrops observed.beforeOpen).insert observed.slot observed.free, observed.slot, 0)
  keeperLive : observed.slot ∈ (view.descriptors seen.opened).slots
  ownerAtFile : (view.files seen.opened).owners =
    before.owners.set (directory.file .lock) (some fileCalls.slot.description)
  canonical : captured.view.child captured.root (renderWalSegmentName 0) = some observed.statChild.child
  sameKeeper : captured.view.modelObject observed.statChild.child = (view.descriptors seen.opened).inode observed.slot.description
  keeperReleased : (view.descriptors seen.released).references observed.slot.description = []
  sameDirectory : captured.view.modelObject captured.root = (view.descriptors seen.released).inode captured.cached.description
  ownerAtDirectory : (view.files seen.released).owners = (view.files seen.opened).owners
  census : view.descriptors seen.directoryBarrier.reached = (BootstrapZeroKeeperRoute.reused observed).settledInventory
  image : (view.files seen.directoryBarrier.reached).image = ⟨before.image.metadata.syncDirectory, .durable⟩
  owners : (view.files seen.directoryBarrier.reached).owners =
    before.owners.set (directory.file .lock) (some fileCalls.slot.description)
  inodes : seen.inodes seen.directoryBarrier.reached = (BootstrapZeroKeeperRoute.reused observed).settledImage
  binding : (seen.inodes seen.directoryBarrier.reached).crashBindings = [observed.files.active]
  bytes : (seen.inodes seen.directoryBarrier.reached).crashBytes observed.files.active = [ByteArray.empty]
  ownerLive : fileCalls.slot ∈ (view.descriptors seen.directoryBarrier.reached).slots
  directoryLive : captured.cached ∈ (view.descriptors seen.directoryBarrier.reached).slots

/-- The same raw cached directory barrier settles the checked empty
inode. The temporary description has been released by the time marker
publication starts, while the owner and original directory remain live. -/
theorem settles (seen : ReusedBootstrapKeeperHeap guards) : seen.Settled := by
  let final := seen.directoryBarrier.reached
  let route : BootstrapZeroKeeperRoute listed := .reused observed
  have physicalOpen := seen.openProjection
  rw [seen.rawOpen, seen.atKeeper, observed.opened] at physicalOpen
  obtain ⟨handle, openedFiles⟩ := EStateM.Result.ok.inj physicalOpen
  have physicalFile := seen.fileProjection
  rw [seen.rawSynced, handle, openedFiles, observed.fileSynced] at physicalFile
  have syncedFiles := (EStateM.Result.ok.inj physicalFile).2
  have physicalDirectory := seen.directoryProjection
  rw [seen.directoryBarrier.synced, syncedFiles, observed.directorySynced] at physicalDirectory
  have settled := (EStateM.Result.ok.inj physicalDirectory).2
  have census : view.descriptors final = route.settledInventory := by
    rw [seen.finalCensus, seen.releasedCensus, seen.liveCensus, DescriptorInventory.afterDrops_append]
    rfl
  have releasedSlot : (view.descriptors seen.released).references observed.slot.description = [] := by
    rw [seen.releasedCensus, seen.liveCensus, DescriptorInventory.afterDrops_append, seen.retired, ← List.append_assoc,
      DescriptorInventory.insert_thenClose, DescriptorInventory.references_afterDrops, observed.fresh]
    rfl
  obtain ⟨live, _, _, _, name, _, inode, _, _, binding, empty⟩ := observed.settledKeeper
  have finalInodes : seen.inodes final = route.settledImage := congrArg Prod.snd settled
  have files := guards.preparedFiles.trans (seed.pendingFiles.trans (seed.activeFiles.trans
    (seed.directoryFiles.trans seed.openedFiles)))
  have fileOwner := seen.openOwners.trans (congrArg LockedFileState.owners files)
  have owners := seen.directoryOwners.trans (seen.fileOwners.trans fileOwner)
  refine ⟨handle, seen.liveCensus.symm ▸ live, fileOwner, name, ?_, releasedSlot,
    seen.directoryBarrier.selectsRoot.2.2, seen.fileOwners, census, congrArg Prod.fst settled, owners,
    finalInodes, finalInodes.symm ▸ binding, finalInodes.symm ▸ empty,
    census.symm ▸ route.settledCustody.1, census.symm ▸ route.settledCustody.2.1⟩
  exact observed.statObject.trans (inode.trans (congrArg (fun slots => slots.inode observed.slot.description) seen.liveCensus).symm)

/-- The actual guarded markerless worker reaches marker publication
from exactly the returned directory fsync heap. The keeper branch has
only the file and directory barriers after the successful empty probe. -/
theorem reachesMarker (seen : ReusedBootstrapKeeperHeap guards) :
    let next := seen.directoryBarrier.reached
    calls.run directory seed.directoryRef seed.activeRef seed.pendingRef seed.afterPending =
      calls.publishZeroMarker directory seed.directoryRef seed.activeRef seed.pendingRef next ∧
    view.cacheAt next seed.directoryRef seed.activeRef seed.pendingRef = captured.cache := by
  intro next
  let sync := calls.sync directory seed.directoryRef seed.activeRef seed.pendingRef
  have rotates : WalSegmentRotation.runAt directory 0 (fun _ => EStateM.pure (some ByteArray.empty))
      (calls.createPending seed.pendingRef) (fun path => sync #[path]) guards.prepared = .ok () next := by
    rw [WalSegmentRotation.runAt_fileEffects]
    simp [WalSegmentRotation.observeSuccessorWith, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
      sync, next, seen.syncsKeeper, seen.directoryBarrier.returns]
  refine ⟨?_, ?_⟩
  · simp [FreshBootstrapCacheCalls.run, bootstrapSegmentedWith, bootstrapEmptyWith, bootstrapEmptyWithMarker, Bind.bind, EStateM.bind,
      Pure.pure, EStateM.pure, guards.prepare, rotates, sync, FreshBootstrapCacheCalls.publishZeroMarker]
  · have cached := seen.directoryBarrier.frame.directory.trans seen.keptDirectory
    have active := seen.directoryBarrier.frame.activeUnchanged.trans seen.keptActive
    have pending := seen.directoryBarrier.pending.trans seen.keptPending
    simp only [next, OpenCloseHeapView.cacheAt, cached, active, pending, seen.keptHandle, seed.sameHandle,
      seed.openedHandle, Option.map_some, Option.map_none, List.map_nil, BootstrapCacheOpen.cache, BootstrapCacheOpen.reached]

/-- The held public opener takes the markerless branch on its exact
cache-allocation heap. After checking the existing keeper, what remains
is the same zero-marker publication on the reached directory-sync heap. -/
theorem reachesFromHeld (seen : ReusedBootstrapKeeperHeap guards)
    (flat : calls.metadata (directory.file .wal) seed.afterPending = .ok none seed.afterPending)
    (marker : calls.metadata (directory.file .walBoundary) seed.afterPending = .ok none seed.afterPending)
    (marked : EStateM IO.Error heap Reopened) :
    recoverSegmentedWalWith (rejectFlatWalWith directory (calls.metadata (directory.file .wal)))
      (calls.metadata (directory.file .walBoundary)) marked
      (calls.run directory seed.directoryRef seed.activeRef seed.pendingRef) seed.afterPending =
    calls.publishZeroMarker directory seed.directoryRef seed.activeRef seed.pendingRef seen.directoryBarrier.reached := by
  simpa [recoverSegmentedWalWith, rejectFlatWalWith, Bind.bind, EStateM.bind, flat, marker,
    Pure.pure, EStateM.pure] using seen.reachesMarker.1

/-- The reused keeper's reached heap supplies the common publication
of the zero marker, with the same inode projection and live cache. -/
structure MarkerPublication (keeper : ReusedBootstrapKeeperHeap guards)
    {marker : BootstrapMarkerCustody listed} (handoff : BootstrapKeeperMarkerHandoff (.reused observed) marker)
    (effects : BootstrapKeeperMarkerHandoff.ReturnedCensus marker) where
  raw : BootstrapMarkerPublicationHeap seed calls keeper.directoryBarrier.reached
  physical : raw.Physical keeper.inodes handoff effects
  keptDirectory : view.handle raw.markerDirectory.reached seed.handle = view.handle keeper.directoryBarrier.reached seed.handle
  owners : (view.files raw.markerDirectory.reached).owners = (view.files keeper.directoryBarrier.reached).owners

variable {keeper : ReusedBootstrapKeeperHeap guards} {marker : BootstrapMarkerCustody listed}
  {handoff : BootstrapKeeperMarkerHandoff (.reused observed) marker} {effects : BootstrapKeeperMarkerHandoff.ReturnedCensus marker}

theorem MarkerPublication.returns (publication : keeper.MarkerPublication handoff effects)
    (flat : calls.metadata (directory.file .wal) seed.afterPending = .ok none seed.afterPending)
    (absent : calls.metadata (directory.file .walBoundary) seed.afterPending = .ok none seed.afterPending)
    (marked : EStateM IO.Error heap Reopened) :
    let final := publication.raw.markerDirectory.reached
    recoverSegmentedWalWith (rejectFlatWalWith directory (calls.metadata (directory.file .wal)))
      (calls.metadata (directory.file .walBoundary)) marked
      (calls.run directory seed.directoryRef seed.activeRef seed.pendingRef) seed.afterPending =
      .ok ⟨.empty, 0, 0, 0⟩ final ∧
    view.cacheAt final seed.directoryRef seed.activeRef seed.pendingRef = captured.cache ∧
    (view.files final).image = marker.publishedState ∧
    (view.files final).owners = before.owners.set (directory.file .lock) (some fileCalls.slot.description) ∧
    view.descriptors final = effects.reached ∧ (view.descriptors final).references marker.slot.description = [] ∧
    (keeper.inodes final).crashBytes (BootstrapZeroKeeperRoute.settledImage (.reused observed)).active = [ByteArray.empty] ∧
    (keeper.inodes final).crashBytes marker.inodeState.active = [WAL.Boundary.encode 0] := by
  intro final
  obtain ⟨published, frame, pending⟩ := publication.raw.returns
  have settled := keeper.settles
  obtain ⟨_, _, _, _, image, _, _, _, keeperBytes, markerBytes, census, released, _, _⟩ :=
    publication.physical.settles settled.image settled.inodes
  have directoryCell := frame.directory.trans (keeper.directoryBarrier.frame.directory.trans keeper.keptDirectory)
  have activeCell := frame.activeUnchanged.trans (keeper.directoryBarrier.frame.activeUnchanged.trans keeper.keptActive)
  have directoryHandle := publication.keptDirectory.trans (keeper.keptHandle.trans (seed.sameHandle.trans seed.openedHandle))
  have cache : view.cacheAt final seed.directoryRef seed.activeRef seed.pendingRef = captured.cache := by
    simp only [final, OpenCloseHeapView.cacheAt, directoryCell, activeCell, pending, directoryHandle,
      Option.map_some, Option.map_none, List.map_nil, BootstrapCacheOpen.cache, BootstrapCacheOpen.reached]
  exact ⟨(keeper.reachesFromHeld flat absent marked).trans published, cache, image,
    publication.owners.trans settled.owners, census, released, keeperBytes, markerBytes⟩

end ReusedBootstrapKeeperHeap

end Alvoki.Storage.DiskSession
