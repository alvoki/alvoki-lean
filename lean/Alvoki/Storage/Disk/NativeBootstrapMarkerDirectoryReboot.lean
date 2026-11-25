import Alvoki.Storage.Disk.NativeBootstrapMarkerDirectoryStop
import Alvoki.Storage.Disk.MarkedBootstrapRetryInstallation

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

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

/-- The effective directory fsync settles the bindings already visible
at the issue. The keeper's earlier data and name barrier is complete. -/
def settledImage (stop : RawBootstrapMarkerDirectoryStop keeper) : WalSegmentRotation.State :=
  let issue := (view.files stop.afterRename).image
  { issue with metadata := issue.metadata.syncDirectory }

theorem settlesDirectoryStep (stop : RawBootstrapMarkerDirectoryStop keeper) :
    bootstrapMarkerStep (view.files stop.afterRename).image .syncDirectory = some stop.settledImage := by
  simp [bootstrapMarkerStep, settledImage, DirectoryPublication.Image.step]

/-- The restart selects the settled directory and retains the empty
keeper. The old owner is dropped by the reboot. -/
def settledReboot (stop : RawBootstrapMarkerDirectoryStop keeper) : LockedFileState WalSegmentRotation.State :=
  let issue := view.files stop.afterRename
  bootstrapPowerLoss directory {issue with image := stop.settledImage} stop.settledImage.metadata.active true

/-- One reported reboot after the issued final barrier took effect.
The same namespace projection observes its issued and restarted heaps.
The payloads come from the crash choices of the original reached inodes. -/
structure EffectiveReboot (physical : stop.Physical handoff) where
  afterEffect : heap
  fsync : IO.FS.Handle → EStateM (FilePath × IO.FS.Handle) heap (Except IO.Error Unit)
  stopped : fsync seed.handle stop.afterRename = .error (directory.path, seed.handle) afterEffect
  applied : view.files afterEffect = ⟨stop.settledImage, (view.files stop.afterRename).owners⟩
  effectNames : physical.names afterEffect = physical.names stop.afterRename
  effectInodes : keeper.inodes afterEffect = (keeper.inodes stop.afterRename).settleBinding
  rebooted : heap
  files : view.files rebooted = stop.settledReboot
  emptyCensus : (view.descriptors rebooted).slots = []
  sameObjects : (physical.names rebooted).modelObject = (physical.names afterEffect).modelObject
  chosen : ∀ name, (physical.names rebooted).child captured.root name = (physical.names afterEffect).child captured.root name
  payload : ∀ name ∈ [keeperName, markerName], ∀ child, (physical.names rebooted).child captured.root name = some child →
    (keeper.inodes rebooted).visible ((physical.names rebooted).modelObject child) ∈
      (keeper.inodes afterEffect).crashBytes ((physical.names afterEffect).modelObject child)

theorem readyAtSettledReboot (physical : stop.Physical handoff) (valid : BootstrapValid before.image) :
    BootstrapReady stop.settledReboot.image := by
  have reached := stop.reachesPhysical physical
  have absent := valid.nextSelection.1
  refine ⟨rfl, ?_, ?_, rfl⟩
  · simp only [settledReboot, bootstrapPowerLoss, settledImage, reached.image]
    exact absent
  · simp only [settledReboot, bootstrapPowerLoss, settledImage, reached.image]
    rfl

namespace EffectiveReboot

variable {physical : stop.Physical handoff} (report : EffectiveReboot physical)

/-- The reported effective sync and reboot select the same names and both
exact payloads. The old lock's directory entry survives but no old slot
or owner survives. This is the input needed by the next marked opener. -/
structure Selected : Prop where
  issued : report.fsync seed.handle stop.afterRename = .error (directory.path, seed.handle) report.afterEffect
  effectStep : bootstrapMarkerStep (view.files stop.afterRename).image .syncDirectory =
    some (view.files report.afterEffect).image
  ready : BootstrapReady (view.files report.rebooted).image
  marked : BootstrapMarkedZero (view.files report.rebooted).image
  vacant : TryLockObserves (view.files report.rebooted).owners directory (.ok true)
  emptyCensus : (view.descriptors report.rebooted).slots = []
  directory : (physical.names report.rebooted).modelObject captured.root =
    (view.descriptors stop.afterRename).inode captured.cached.description
  lock : (physical.names report.rebooted).child captured.root "LOCK" = some listed.lifetime.lock
  lockObject : (physical.names report.rebooted).modelObject listed.lifetime.lock =
    captured.reached.inode fileCalls.slot.description
  manifestMissing : (physical.names report.rebooted).child captured.root "MANIFEST" = none
  noConflict : ∀ name, name ≠ scratchName → name ≠ markerName → conflictsWithBootstrap name = true →
    (physical.names report.rebooted).child captured.root name = none
  scratchMissing : (physical.names report.rebooted).child captured.root scratchName = none
  keeperBinding : (physical.names report.rebooted).child captured.root keeperName = some observed.statChild.child
  markerBinding : (physical.names report.rebooted).child captured.root markerName = some marker.stageChild.child
  sameKeeperObject : (physical.names report.rebooted).modelObject observed.statChild.child =
    (physical.names stop.afterRename).modelObject observed.statChild.child
  sameMarkerObject : (physical.names report.rebooted).modelObject marker.stageChild.child =
    (physical.names stop.afterRename).modelObject marker.stageChild.child
  keeperBytes : (keeper.inodes report.rebooted).visible
    ((physical.names report.rebooted).modelObject observed.statChild.child) = ByteArray.empty
  markerBytes : (keeper.inodes report.rebooted).visible
    ((physical.names report.rebooted).modelObject marker.stageChild.child) = WAL.Boundary.encode 0

theorem selects (valid : BootstrapValid before.image) : report.Selected := by
  have reached := stop.reachesPhysical physical
  have ready := stop.readyAtSettledReboot physical valid
  have sameNames (name : String) :
      (physical.names report.rebooted).child captured.root name =
      (physical.names stop.afterRename).child captured.root name := by
    rw [report.chosen, report.effectNames]
  have sameObjects : (physical.names report.rebooted).modelObject = captured.view.modelObject :=
    report.sameObjects.trans ((congrArg DirectoryReadNamespace.modelObject
      (report.effectNames.trans physical.renamedNames)).trans handoff.renameObjects)
  have sameOldName (name : String) (stage : name ≠ scratchName) (active : name ≠ markerName) :
      (physical.names report.rebooted).child captured.root name = captured.view.child captured.root name := by
    rw [sameNames name, physical.renamedNames, handoff.renameNames name stage active]
    exact handoff.stageNames name stage
  have lock : captured.view.child captured.root "LOCK" = some listed.lifetime.lock := by
    have bound := listed.lifetime.lockEntry
    rw [listed.sameRoot, listed.sameView] at bound
    exact bound
  have noConflict (name : String) (notScratch : name ≠ scratchName) (notMarker : name ≠ markerName)
      (conflicts : conflictsWithBootstrap name = true) :
      (physical.names report.rebooted).child captured.root name = none := by
    rw [sameOldName name notScratch notMarker]
    cases found : captured.view.child captured.root name with
    | none => rfl
    | some child =>
      have present := (captured.view.namesExact captured.root name).mpr ⟨child, found⟩
      rw [listed.noConflict name present] at conflicts
      contradiction
  have locked : TryLockObserves (view.files report.rebooted).owners directory (.ok true) := by
    rw [report.files]
    intro _
    simp [settledReboot, bootstrapPowerLoss, LockOwners.set]
  have keeperBinding := (sameNames keeperName).trans reached.keeperBinding
  have markerBinding := (sameNames markerName).trans reached.markerBinding
  have keeperBytes := report.payload keeperName (by simp) _ keeperBinding
  have markerBytes := report.payload markerName (by simp) _ markerBinding
  rw [report.effectNames, report.effectInodes, WalInodeImage.settleBinding, reached.keeperBytes] at keeperBytes
  rw [report.effectNames, report.effectInodes, WalInodeImage.settleBinding, reached.markerBytes] at markerBytes
  have effectStep : bootstrapMarkerStep (view.files stop.afterRename).image .syncDirectory =
      some (view.files report.afterEffect).image := by
    rw [report.applied]
    exact stop.settlesDirectoryStep
  have objectMap : (physical.names report.rebooted).modelObject = (physical.names stop.afterRename).modelObject :=
    report.sameObjects.trans (congrArg DirectoryReadNamespace.modelObject report.effectNames)
  refine ⟨report.stopped, effectStep, report.files.symm ▸ ready,
    report.files.symm ▸ ⟨ready.manifestAbsent, ready.zeroMarker, ready.zeroDurable⟩,
    locked, report.emptyCensus, ?_, (sameOldName "LOCK" (by decide) (by decide)).trans lock, ?_,
    noConflict "MANIFEST" (by decide) (by decide) rfl, noConflict, (sameNames scratchName).trans reached.scratchGone,
    keeperBinding, markerBinding, congrFun objectMap _, congrFun objectMap _, List.mem_singleton.mp keeperBytes,
    List.mem_singleton.mp markerBytes⟩
  · rw [report.sameObjects, report.effectNames]
    exact reached.directoryInode
  · rw [sameObjects]
    have identity := listed.lifetime.identifiesLock
    rw [listed.sameView] at identity
    exact identity

end EffectiveReboot
end RawBootstrapMarkerDirectoryStop

end Alvoki.Storage.DiskSession
