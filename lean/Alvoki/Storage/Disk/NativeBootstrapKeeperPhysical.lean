import Alvoki.Storage.Disk.NativeBootstrapCacheChronology
import Alvoki.Storage.Disk.BootstrapKeeperMarkerHandoff

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

variable {heap : Type} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {fileCalls : BootstrapOpenCalls (Cache CheckpointOpenHandle) directory before}
  {captured : BootstrapCacheOpen fileCalls.toBootstrapAdmissionCalls}
  {listed : BootstrapCheckedListing captured}

abbrev BootstrapFileProjection := WalSegmentRotation.State × WalInodeImage

def BootstrapFileProjection.atHeap (view : OpenCloseHeapView heap WalSegmentRotation.State)
    (inodes : heap → WalInodeImage) (state : heap) : BootstrapFileProjection :=
  ((view.files state).image, inodes state)

def BootstrapFileProjection.result (view : OpenCloseHeapView heap WalSegmentRotation.State)
    (inodes : heap → WalInodeImage) (value : heap → α → β) :
    EStateM.Result IO.Error heap α → EStateM.Result IO.Error BootstrapFileProjection β
  | .ok returned reached => .ok (value reached returned) (BootstrapFileProjection.atHeap view inodes reached)
  | .error cause reached => .error cause (BootstrapFileProjection.atHeap view inodes reached)

private abbrev BootstrapFreshZeroKeeper.inventory (observed : BootstrapFreshZeroKeeper listed) :=
  (listed.scan.afterClose.afterDrops observed.beforeCreate).insert observed.slot observed.free

private abbrev BootstrapFreshZeroKeeper.handle (observed : BootstrapFreshZeroKeeper listed) : CheckpointOpenHandle :=
  (observed.inventory, observed.slot, 0)

variable {view : OpenCloseHeapView heap WalSegmentRotation.State} {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {seed : OpenSyncCacheAllocations captured.opened view init entry} {calls : FreshBootstrapCacheCalls heap}
  {prepared : heap} {expected : CheckpointOpenHandle}

/-- Connect the raw keeper creation and its two barriers to their own
physical reports. The pending reference operations preserve only the
stated file projection. The directory census at issue and return is
reported at the actual reached heaps. -/
structure FreshBootstrapKeeperPhysical
    (observed : BootstrapFreshZeroKeeper listed)
    (keeper : BootstrapPendingObservation view calls.toBootstrapPendingCalls directory .keeper
      seed.pendingRef expected prepared)
    (barrier : FreshBootstrapDirectoryBarrier seed calls keeper.reached) where
  inodes : heap → WalInodeImage
  atCreate : BootstrapFileProjection.atHeap view inodes prepared = (before.image, observed.initial)
  created : BootstrapFileProjection.result view inodes view.handle (calls.create (directory.file (.walSegment 0)) prepared) =
    observed.openExclusive (directory.file (.walSegment 0)) (BootstrapFileProjection.atHeap view inodes prepared)
  remembered : BootstrapFileProjection.atHeap view inodes keeper.recorded = BootstrapFileProjection.atHeap view inodes keeper.produced
  consumed : BootstrapFileProjection.atHeap view inodes keeper.consumed = BootstrapFileProjection.atHeap view inodes keeper.recorded
  fileSynced : BootstrapFileProjection.result view inodes (fun _ value => value) (calls.fsync keeper.handle keeper.consumed) =
    observed.fsync (view.handle keeper.consumed keeper.handle) (BootstrapFileProjection.atHeap view inodes keeper.consumed)
  fileCensus : view.descriptors keeper.consumed = observed.inventory.afterDrops observed.beforeFile
  directorySynced : BootstrapFileProjection.result view inodes (fun _ value => value) (calls.fsync seed.handle keeper.reached) =
    observed.fsync (captured.reached, captured.cached, 0) (BootstrapFileProjection.atHeap view inodes keeper.reached)
  directoryCensus : view.descriptors keeper.reached = observed.inventory.afterDrops (observed.beforeFile ++ observed.afterFile)
  finalCensus : view.descriptors barrier.reached = view.descriptors keeper.reached

namespace FreshBootstrapKeeperPhysical

variable {observed : BootstrapFreshZeroKeeper listed}
  {keeper : BootstrapPendingObservation view calls.toBootstrapPendingCalls directory .keeper seed.pendingRef expected prepared}
  {barrier : FreshBootstrapDirectoryBarrier seed calls keeper.reached}

/-- The same raw opened and consumed descriptor reaches the keeper
file barrier. The original cached directory barrier then settles that
inode, with the empty payload and both original slots retained. -/
theorem settles (seen : FreshBootstrapKeeperPhysical observed keeper barrier) (synced : keeper.result = .ok ()) :
    let state := BootstrapZeroKeeperRoute.settledImage (.fresh observed)
    view.handle keeper.consumed keeper.handle = observed.handle ∧
    observed.slot ∈ (view.descriptors keeper.consumed).slots ∧
    (view.files barrier.reached).image = ⟨before.image.metadata.syncDirectory, .durable⟩ ∧
    seen.inodes barrier.reached = state ∧
    observed.namespaceView.child captured.root (renderWalSegmentName 0) = some observed.child.child ∧
    observed.namespaceView.modelObject observed.child.child =
      (view.descriptors keeper.consumed).inode observed.slot.description ∧
    captured.view.modelObject captured.root = (view.descriptors keeper.reached).inode captured.cached.description ∧
    (seen.inodes barrier.reached).crashBindings = [observed.opened.active] ∧
    (seen.inodes barrier.reached).crashBytes observed.opened.active = [ByteArray.empty] ∧
    fileCalls.slot ∈ (view.descriptors barrier.reached).slots ∧
    captured.cached ∈ (view.descriptors barrier.reached).slots := by
  intro state
  have created := seen.created
  have rawCreate : calls.create (directory.file (.walSegment 0)) prepared = .ok keeper.handle keeper.produced :=
    keeper.returnedHandle
  rw [rawCreate, seen.atCreate, observed.created] at created
  obtain ⟨openedHandle, createdFiles⟩ := EStateM.Result.ok.inj created
  have keeperHandle : view.handle keeper.consumed keeper.handle = observed.handle :=
    keeper.sameIssuing.trans (keeper.sameProduced.symm.trans openedHandle)
  have observedSync := seen.fileSynced
  have rawSync := keeper.syncReturned
  rw [synced] at rawSync
  rw [rawSync, keeperHandle, seen.consumed, seen.remembered, createdFiles, observed.fileSynced] at observedSync
  have syncedFiles := (EStateM.Result.ok.inj observedSync).2
  have originalSync := seen.directorySynced
  rw [barrier.synced, syncedFiles, observed.directorySynced] at originalSync
  have durable : BootstrapFileProjection.atHeap view seen.inodes barrier.reached = (⟨before.image.metadata.syncDirectory, .durable⟩, state) :=
    (EStateM.Result.ok.inj originalSync).2
  obtain ⟨fileLive, lockLive, dirLive, _, _, name, _, _, _, binding, bytes⟩ := observed.settledKeeper
  have finalInodes : seen.inodes barrier.reached = state := congrArg Prod.snd durable
  refine ⟨keeperHandle, seen.fileCensus.symm ▸ fileLive, congrArg Prod.fst durable, finalInodes, name,
    ?_, barrier.selectsRoot.2.2, ?_, ?_, ?_, ?_⟩
  · rw [seen.fileCensus]
    exact observed.object
  · exact finalInodes.symm ▸ binding
  · exact finalInodes.symm ▸ bytes
  · rw [seen.finalCensus, seen.directoryCensus]
    exact lockLive
  · rw [seen.finalCensus, seen.directoryCensus]
    exact dirLive

end FreshBootstrapKeeperPhysical

end Alvoki.Storage.DiskSession
