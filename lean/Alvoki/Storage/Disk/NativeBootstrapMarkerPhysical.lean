import Alvoki.Storage.Disk.NativeBootstrapKeeperPhysical
import Alvoki.Storage.Disk.BootstrapExecution

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

variable {heap : Type} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {fileCalls : BootstrapOpenCalls (Cache CheckpointOpenHandle) directory before}
  {captured : BootstrapCacheOpen fileCalls.toBootstrapAdmissionCalls}
  {listed : BootstrapCheckedListing captured}
  {view : OpenCloseHeapView heap WalSegmentRotation.State} {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {seed : OpenSyncCacheAllocations captured.opened view init entry} {calls : FreshBootstrapCacheCalls heap}
  {markerEntry : heap} {keeper : BootstrapZeroKeeperRoute listed}

private abbrev stagedMarkerHandle (marker : BootstrapMarkerCustody listed) : CheckpointOpenHandle :=
  marker.toBootstrapMarkerStaging.handle

/-- The same marker publication follows either keeper route. Each exact
callback supplies its physical file and descriptor effect. -/
structure BootstrapMarkerPublicationHeap.Physical
    (chronology : BootstrapMarkerPublicationHeap seed calls markerEntry)
    (inodes : heap → WalInodeImage)
    {marker : BootstrapMarkerCustody listed} (handoff : BootstrapKeeperMarkerHandoff keeper marker)
    (effects : BootstrapKeeperMarkerHandoff.ReturnedCensus marker) where
  staged : BootstrapFileProjection.result view inodes view.handle
      (calls.stage (directory.file .stagedWalBoundary) (WAL.Boundary.encode 0) markerEntry) =
    marker.toBootstrapMarkerStaging.stage (directory.file .stagedWalBoundary) (WAL.Boundary.encode 0)
      (BootstrapFileProjection.atHeap view inodes markerEntry)
  remembered : BootstrapFileProjection.atHeap view inodes chronology.marker.recorded =
    BootstrapFileProjection.atHeap view inodes chronology.marker.produced
  consumed : BootstrapFileProjection.atHeap view inodes chronology.marker.consumed =
    BootstrapFileProjection.atHeap view inodes chronology.marker.recorded
  fileSynced : BootstrapFileProjection.result view inodes (fun _ value => value)
      (calls.fsync chronology.marker.handle chronology.marker.consumed) =
    marker.fsync (view.handle chronology.marker.consumed chronology.marker.handle)
      (BootstrapFileProjection.atHeap view inodes chronology.marker.consumed)
  fileCensus : view.descriptors chronology.marker.consumed = marker.toBootstrapMarkerStaging.inventory.afterDrops marker.beforeFile
  fileDrops : view.descriptors chronology.marker.reached = marker.toBootstrapMarkerStaging.inventory.afterDrops
    (marker.beforeFile ++ marker.afterFile)
  renameProjection : BootstrapFileProjection.result view inodes (fun _ value => value)
      (calls.rename (directory.file .stagedWalBoundary) (directory.file .walBoundary) chronology.marker.reached) =
    marker.rename (directory.file .stagedWalBoundary) (directory.file .walBoundary)
      (BootstrapFileProjection.atHeap view inodes chronology.marker.reached)
  renameCensus : view.descriptors chronology.afterRename = view.descriptors chronology.marker.reached
  directorySynced : BootstrapFileProjection.result view inodes (fun _ value => value)
      (calls.fsync seed.handle chronology.afterRename) =
    marker.fsync (captured.reached, captured.cached, 0) (BootstrapFileProjection.atHeap view inodes chronology.afterRename)
  directoryDrops : view.descriptors chronology.markerDirectory.reached = (view.descriptors chronology.afterRename).afterDrops effects.directoryDrops

namespace BootstrapMarkerPublicationHeap.Physical

variable {chronology : BootstrapMarkerPublicationHeap seed calls markerEntry} {inodes : heap → WalInodeImage}
  {marker : BootstrapMarkerCustody listed} {handoff : BootstrapKeeperMarkerHandoff keeper marker}
  {effects : BootstrapKeeperMarkerHandoff.ReturnedCensus marker}

/-- Keep the exact keeper settled by the preceding directory barrier.
The staged marker crosses file sync and rename before its directory sync.
The reached heap projects to both canonical names and durable payloads. -/
theorem settles (seen : chronology.Physical inodes handoff effects)
    (keeperReady : (view.files markerEntry).image = ⟨before.image.metadata.syncDirectory, .durable⟩)
    (keeperInodes : inodes markerEntry = keeper.settledImage) :
    let raw := chronology.marker
    let final := chronology.markerDirectory.reached
    view.handle raw.consumed raw.handle = stagedMarkerHandle marker ∧
    marker.slot ∈ (view.descriptors raw.consumed).slots ∧
    marker.inodeState.active = (view.descriptors raw.consumed).inode marker.slot.description ∧
    captured.view.modelObject captured.root =
      (view.descriptors chronology.afterRename).inode captured.cached.description ∧
    (view.files final).image = marker.publishedState ∧
    inodes final = (marker.inodeState.completeFileSync marker.inodeState.active).settleBinding ∧
    handoff.afterMarkerNames (renderWalSegmentName 0) = [some keeper.keeperChild] ∧
    handoff.afterMarkerNames "WAL.commit" = [some marker.stageChild.child] ∧
    (inodes final).crashBytes keeper.settledImage.active = [ByteArray.empty] ∧
    (inodes final).crashBytes marker.inodeState.active = [WAL.Boundary.encode 0] ∧
    view.descriptors final = effects.reached ∧
    (view.descriptors final).references marker.slot.description = [] ∧
    fileCalls.slot ∈ (view.descriptors final).slots ∧ captured.cached ∈ (view.descriptors final).slots := by
  intro raw final
  have stageInput : BootstrapFileProjection.atHeap view inodes markerEntry =
      (marker.toBootstrapMarkerStaging.inputState, marker.initial) :=
    Prod.ext keeperReady (keeperInodes.trans handoff.stageInput.symm)
  have staged := seen.staged
  have rawStage : calls.stage (directory.file .stagedWalBoundary) (WAL.Boundary.encode 0) markerEntry =
      .ok raw.handle raw.produced := raw.returnedHandle
  rw [rawStage, stageInput, marker.toBootstrapMarkerStaging.stageReturns] at staged
  obtain ⟨stagedHandle, stagedFiles⟩ := EStateM.Result.ok.inj staged
  have markerHandle : view.handle raw.consumed raw.handle = stagedMarkerHandle marker :=
    raw.sameIssuing.trans (raw.sameProduced.symm.trans stagedHandle)
  have fileSynced := seen.fileSynced
  have rawSync := raw.syncReturned
  rw [show raw.result = .ok () from chronology.markerOK] at rawSync
  rw [rawSync, markerHandle, seen.consumed, seen.remembered, stagedFiles, marker.fileSynced] at fileSynced
  have syncedFiles := (EStateM.Result.ok.inj fileSynced).2
  have renamed := seen.renameProjection
  rw [chronology.renamed, syncedFiles, marker.renameReturned] at renamed
  have renamedFiles := (EStateM.Result.ok.inj renamed).2
  have directorySynced := seen.directorySynced
  rw [chronology.markerDirectory.synced, renamedFiles, marker.directorySynced] at directorySynced
  have finalFiles := (EStateM.Result.ok.inj directorySynced).2
  have finalInodes : inodes final = (marker.inodeState.completeFileSync marker.inodeState.active).settleBinding :=
    congrArg Prod.snd finalFiles
  have census : view.descriptors final = effects.reached := by
    rw [seen.directoryDrops, seen.renameCensus, seen.fileDrops, BootstrapKeeperMarkerHandoff.ReturnedCensus.reached,
      DescriptorInventory.afterDrops_append]
  obtain ⟨fileLive, _, _, _, _, _, liveMarker, _, activeInode, _, markerBytes⟩ := marker.settledInode
  obtain ⟨_, _, _, _, _, _, _, keeperName, _, _, _, _, keeperBytes⟩ := handoff.preservesKeeper
  refine ⟨markerHandle, seen.fileCensus.symm ▸ fileLive, ?_, chronology.markerDirectory.selectsRoot.2.2,
    congrArg Prod.fst finalFiles, finalInodes, keeperName,
    ?_, finalInodes.symm ▸ keeperBytes, finalInodes.symm ▸ markerBytes, census, ?_, ?_, ?_⟩
  · rw [seen.fileCensus]
    exact activeInode
  · simp [handoff.markerSettlement, liveMarker]
  · rw [census]
    exact effects.stageClosed
  · rw [census]
    exact effects.lockRetained
  · rw [census]
    exact effects.cacheRetained

end BootstrapMarkerPublicationHeap.Physical

variable {freshKeeper : BootstrapFreshZeroKeeper listed} {fresh : FreshBootstrapCacheChronology seed calls}

abbrev FreshBootstrapMarkerPhysical
    (chronology : FreshBootstrapCacheChronology seed calls)
    (keeperPhysical : FreshBootstrapKeeperPhysical freshKeeper chronology.keeper chronology.keeperDirectory)
    {marker : BootstrapMarkerCustody listed} (handoff : BootstrapKeeperMarkerHandoff (.fresh freshKeeper) marker)
    (effects : BootstrapKeeperMarkerHandoff.ReturnedCensus marker) :=
  chronology.markerPublication.Physical keeperPhysical.inodes handoff effects

theorem FreshBootstrapMarkerPhysical.settles
    {keeperPhysical : FreshBootstrapKeeperPhysical freshKeeper fresh.keeper fresh.keeperDirectory}
    {marker : BootstrapMarkerCustody listed} {handoff : BootstrapKeeperMarkerHandoff (.fresh freshKeeper) marker}
    {effects : BootstrapKeeperMarkerHandoff.ReturnedCensus marker}
    (seen : FreshBootstrapMarkerPhysical fresh keeperPhysical handoff effects) :
    let raw := fresh.marker
    let final := fresh.markerDirectory.reached
    view.handle raw.consumed raw.handle = stagedMarkerHandle marker ∧
    marker.slot ∈ (view.descriptors raw.consumed).slots ∧
    marker.inodeState.active = (view.descriptors raw.consumed).inode marker.slot.description ∧
    captured.view.modelObject captured.root = (view.descriptors fresh.afterRename).inode captured.cached.description ∧
    (view.files final).image = marker.publishedState ∧
    keeperPhysical.inodes final = (marker.inodeState.completeFileSync marker.inodeState.active).settleBinding ∧
    handoff.afterMarkerNames (renderWalSegmentName 0) = [some (BootstrapZeroKeeperRoute.keeperChild (.fresh freshKeeper))] ∧
    handoff.afterMarkerNames "WAL.commit" = [some marker.stageChild.child] ∧
    (keeperPhysical.inodes final).crashBytes (BootstrapZeroKeeperRoute.settledImage (.fresh freshKeeper)).active = [ByteArray.empty] ∧
    (keeperPhysical.inodes final).crashBytes marker.inodeState.active = [WAL.Boundary.encode 0] ∧
    view.descriptors final = effects.reached ∧
    (view.descriptors final).references marker.slot.description = [] ∧
    fileCalls.slot ∈ (view.descriptors final).slots ∧ captured.cached ∈ (view.descriptors final).slots := by
  obtain ⟨_, _, keeperReady, keeperInodes, _, _, _, _, _, _, _⟩ := keeperPhysical.settles fresh.keeperOK
  exact BootstrapMarkerPublicationHeap.Physical.settles seen keeperReady keeperInodes

end Alvoki.Storage.DiskSession
