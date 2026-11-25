import Alvoki.Storage.Disk.NativeBootstrapMarkerDirectoryStop
import Alvoki.Storage.Disk.ObservedBootstrapRetry

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

private abbrev keeperName := renderWalSegmentName 0
private abbrev markerName := "WAL.commit"
private abbrev scratchName := "WAL.commit.next"

variable {heap : Type} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {fileCalls : BootstrapOpenCalls (Cache CheckpointOpenHandle) directory before}
  {captured : BootstrapCacheOpen fileCalls.toBootstrapAdmissionCalls} {listed : BootstrapCheckedListing captured}
  {view : OpenCloseHeapView heap WalSegmentRotation.State} {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {seed : OpenSyncCacheAllocations captured.opened view init entry} {calls : FreshBootstrapCacheCalls heap}
  {observed : BootstrapReusedZeroKeeper listed} {guards : ReusedBootstrapKeeperGuards observed seed calls}
  {keeper : ReusedBootstrapKeeperHeap guards} {stop : RawBootstrapMarkerDirectoryStop keeper}
  {marker : BootstrapMarkerRenamed listed}
  {handoff : BootstrapKeeperMarkerRename (.reused observed) marker}

namespace RawBootstrapMarkerDirectoryStop

/-- Before the final directory effect the rename has a crash alternative
with the old markerless metadata pair. The empty keeper is already settled. -/
def markerlessReboot (stop : RawBootstrapMarkerDirectoryStop keeper) : LockedFileState WalSegmentRotation.State :=
  bootstrapPowerLoss directory (view.files stop.afterRename) before.image.metadata.active true

/-- One joint before-effect restart chooses the old markerless pair and
no scratch name. The fsync issues on the original cache and never returns. -/
structure BeforeEffectMarkerlessReboot (physical : stop.Physical handoff) where
  fsync : IO.FS.Handle → EStateM (FilePath × IO.FS.Handle) heap (Except IO.Error Unit)
  stopped : fsync seed.handle stop.afterRename = .error (directory.path, seed.handle) stop.afterRename
  canonicalAbsent : captured.view.child captured.root markerName = none
  markerChoices : handoff.afterRenameNames markerName =
    (physical.names stop.afterRename).child captured.root markerName :: handoff.afterStageNames markerName
  rebooted : heap
  files : view.files rebooted = stop.markerlessReboot
  empty : (view.descriptors rebooted).slots = []
  sameObjects : (physical.names rebooted).modelObject = (physical.names stop.afterRename).modelObject
  chose : ∀ name, (physical.names rebooted).child captured.root name ∈ handoff.afterRenameNames name
  markerMissing : (physical.names rebooted).child captured.root markerName = none
  scratchMissing : (physical.names rebooted).child captured.root scratchName = none
  keeperObject : (keeper.inodes rebooted).active = (physical.names rebooted).modelObject observed.statChild.child
  kept : ∀ child, (physical.names rebooted).child captured.root keeperName = some child →
    (keeper.inodes rebooted).visible ((physical.names rebooted).modelObject child) ∈
      (keeper.inodes stop.afterRename).crashBytes ((physical.names stop.afterRename).modelObject child)

namespace BeforeEffectMarkerlessReboot

variable {physical : stop.Physical handoff} (report : BeforeEffectMarkerlessReboot physical)

structure Selected : Prop where
  issued : report.fsync seed.handle stop.afterRename = .error (directory.path, seed.handle) stop.afterRename
  oldPair : before.image.metadata.active ∈ (view.files stop.afterRename).image.metadata.crashImages
  keeperSurvives : (view.files stop.afterRename).image.successor.MaySurvive true
  valid : BootstrapValid (view.files report.rebooted).image
  markerless : (view.files report.rebooted).image.metadata.active.walBoundary = none
  manifestless : (view.files report.rebooted).image.metadata.active.manifest = none
  vacant : TryLockObserves (view.files report.rebooted).owners directory (.ok true)
  emptyCensus : (view.descriptors report.rebooted).slots = []
  directory : (physical.names report.rebooted).modelObject captured.root =
    (view.descriptors stop.afterRename).inode captured.cached.description
  lock : (physical.names report.rebooted).child captured.root "LOCK" = some listed.lifetime.lock
  lockObject : (physical.names report.rebooted).modelObject listed.lifetime.lock =
    captured.reached.inode fileCalls.slot.description
  manifestMissing : (physical.names report.rebooted).child captured.root "MANIFEST" = none
  noConflict : ∀ name, conflictsWithBootstrap name = true →
    (physical.names report.rebooted).child captured.root name = none
  markerMissing : (physical.names report.rebooted).child captured.root markerName = none
  scratchMissing : (physical.names report.rebooted).child captured.root scratchName = none
  scratchChoice : none ∈ handoff.afterRenameNames scratchName
  allowedMarkerNames : handoff.afterRenameNames markerName = [some marker.stageChild.child, none]
  keeperBinding : (physical.names report.rebooted).child captured.root keeperName = some observed.statChild.child
  sameKeeperObject : (physical.names report.rebooted).modelObject observed.statChild.child =
    (physical.names stop.afterRename).modelObject observed.statChild.child
  keeperBytes : (keeper.inodes report.rebooted).visible (keeper.inodes report.rebooted).active = ByteArray.empty

/-- The reported selection uses the issue heap's old marker alternative.
The checked keeper survives at its original child with its original bytes.
No scratch inode or owner needs to be carried into the next open. -/
theorem selects (valid : BootstrapValid before.image) : report.Selected := by
  have reached := stop.reachesPhysical physical
  have sameObjects : (physical.names report.rebooted).modelObject = captured.view.modelObject :=
    report.sameObjects.trans ((congrArg DirectoryReadNamespace.modelObject physical.renamedNames).trans handoff.renameObjects)
  have sameOldName (name : String) (stage : name ≠ scratchName) (active : name ≠ markerName) :
      (physical.names report.rebooted).child captured.root name = captured.view.child captured.root name := by
    have choice := report.chose name
    rw [handoff.renameChoices name stage active, handoff.stageChoices name stage, handoff.keeperSettlement] at choice
    exact List.mem_singleton.mp choice
  have lock := listed.lifetime.lockEntry
  rw [listed.sameRoot, listed.sameView] at lock
  have lockObject := listed.lifetime.identifiesLock
  rw [listed.sameView] at lockObject
  have noConflict (name : String) (conflicts : conflictsWithBootstrap name = true) :
      (physical.names report.rebooted).child captured.root name = none := by
    by_cases notScratch : name = scratchName
    · exact notScratch.symm ▸ report.scratchMissing
    by_cases notMarker : name = markerName
    · exact notMarker.symm ▸ report.markerMissing
    rw [sameOldName name notScratch notMarker]
    cases found : captured.view.child captured.root name with
    | none => rfl
    | some child =>
      have present := (captured.view.namesExact captured.root name).mpr ⟨child, found⟩
      rw [listed.noConflict name present] at conflicts
      contradiction
  have names : handoff.afterRenameNames markerName = [some marker.stageChild.child, none] := by
    rw [report.markerChoices, reached.markerBinding, handoff.stageChoices markerName (by decide),
      handoff.keeperSettlement]
    change [some marker.stageChild.child, captured.view.child captured.root markerName] = _
    rw [report.canonicalAbsent]
  have keeperBinding : (physical.names report.rebooted).child captured.root keeperName =
      some observed.statChild.child := by
    have bound := observed.statChild.binds
    rw [observed.statChild.atRoot, observed.statChild.atName] at bound
    exact (sameOldName keeperName (by decide) (by decide)).trans bound
  have payload := report.kept _ keeperBinding
  rw [reached.keeperBytes, ← report.keeperObject] at payload
  have oldPair : before.image.metadata.active ∈ (view.files stop.afterRename).image.metadata.crashImages := by
    rw [reached.image]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have keeperSurvives : (view.files stop.afterRename).image.successor.MaySurvive true := by
    rw [reached.image]
    rfl
  have restarted : BootstrapValid stop.markerlessReboot.image := by
    exact ⟨DirectoryPublication.Image.settled_valid valid.metadata.activeValid, fun _ _ _ => rfl⟩
  have vacant : TryLockObserves (view.files report.rebooted).owners directory (.ok true) := by
    rw [report.files]
    intro _
    simp [markerlessReboot, bootstrapPowerLoss, LockOwners.set]
  refine ⟨report.stopped, oldPair, keeperSurvives, report.files.symm ▸ restarted,
    report.files.symm ▸ fileCalls.markerAbsent.1, report.files.symm ▸ valid.nextSelection.1,
    vacant, report.empty, report.sameObjects.symm ▸ reached.directoryInode,
    (sameOldName "LOCK" (by decide) (by decide)).trans lock, sameObjects.symm ▸ lockObject,
    noConflict "MANIFEST" rfl, noConflict, report.markerMissing, report.scratchMissing,
    report.scratchMissing ▸ report.chose scratchName, names, keeperBinding, congrFun report.sameObjects _,
    List.mem_singleton.mp payload⟩

end BeforeEffectMarkerlessReboot
end RawBootstrapMarkerDirectoryStop
end Alvoki.Storage.DiskSession
