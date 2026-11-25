import Alvoki.Storage.Disk.BootstrapMarkerCustody
import Alvoki.Storage.Disk.BootstrapZeroKeeperCustody

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat
private abbrev Files := WalSegmentRotation.State × WalInodeImage
private abbrev keeperName := renderWalSegmentName 0
private abbrev stageName := "WAL.commit.next"
private abbrev markerName := "WAL.commit"

variable {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {calls : BootstrapOpenCalls (Cache Handle) directory before}
  {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}
  {listed : BootstrapCheckedListing captured}

namespace BootstrapZeroKeeperRoute

def settledImage (route : BootstrapZeroKeeperRoute listed) : WalInodeImage :=
  (route.keeperImage.completeFileSync route.keeperImage.active).settleBinding

def settledInventory (route : BootstrapZeroKeeperRoute listed) : DescriptorInventory :=
  match route with
  | .fresh observed =>
    ((listed.scan.afterClose.afterDrops observed.beforeCreate).insert observed.slot observed.free).afterDrops
      (observed.beforeFile ++ observed.afterFile)
  | .reused observed =>
    ((listed.scan.afterClose.afterDrops observed.beforeOpen).insert observed.slot observed.free).afterDrops
      (observed.beforeFile ++ observed.afterFile)

def keeperView (route : BootstrapZeroKeeperRoute listed) : DirectoryReadNamespace :=
  match route with
  | .fresh observed => observed.namespaceView
  | .reused _ => captured.view

def keeperChild (route : BootstrapZeroKeeperRoute listed) : DeviceInode :=
  match route with
  | .fresh observed => observed.child.child
  | .reused observed => observed.statChild.child

/-- Either route reaches the barrier with the same raw keeper, captured
directory and lock identities used by its corresponding native reports. -/
theorem settledCustody (route : BootstrapZeroKeeperRoute listed) :
    calls.slot ∈ route.settledInventory.slots ∧ captured.cached ∈ route.settledInventory.slots ∧
    route.keeperView.child captured.root keeperName = some route.keeperChild ∧
    captured.view.modelObject route.keeperChild = route.settledImage.active := by
  cases route with
  | fresh observed =>
    obtain ⟨_, lock, dir, _, _, bound, _⟩ := observed.settledKeeper
    rw [← observed.sameObjects]
    exact ⟨lock, dir, bound, observed.active.symm⟩
  | reused observed =>
    obtain ⟨_, lock, dir, _, bound, _⟩ := observed.settledKeeper
    exact ⟨lock, dir, bound, observed.statObject⟩

private theorem settledVisible (route : BootstrapZeroKeeperRoute listed) :
    route.settledImage.visible route.settledImage.active = ByteArray.empty := by
  cases route with
  | fresh observed => exact observed.empty
  | reused observed => exact observed.readEmpty.2.2

end BootstrapZeroKeeperRoute

/-- These effects refer to the same reached successful callbacks as the
keeper and marker reports. The two namespace mutations may affect their
target names. The no-follow guard and stale detach, if reached, belong to
the staged write. The file sync changes the selected inode's bytes, and
the directory barriers settle names in the same captured directory. -/
structure BootstrapKeeperMarkerHandoff (keeper : BootstrapZeroKeeperRoute listed)
    (marker : BootstrapMarkerCustody listed) where
  between : List LockReferenceDrop
  stageInventory : listed.scan.afterClose.afterDrops marker.beforeStage =
    keeper.settledInventory.afterDrops between
  stageInput : marker.initial = keeper.settledImage
  stageObjects : marker.stageView.modelObject = captured.view.modelObject
  renameObjects : marker.renamedView.modelObject = captured.view.modelObject
  separateInodes : captured.view.modelObject marker.stageChild.child ≠
    captured.view.modelObject keeper.keeperChild
  stageNames : ∀ name, name ≠ stageName →
    marker.stageView.child captured.root name = keeper.keeperView.child captured.root name
  renameNames : ∀ name, name ≠ stageName → name ≠ markerName →
    marker.renamedView.child captured.root name = marker.stageView.child captured.root name
  stageBytes : ∀ inode, inode ≠ marker.inodeState.active →
    marker.inodeState.visible inode = marker.initial.visible inode ∧
    marker.inodeState.crashBytes inode = marker.initial.crashBytes inode
  afterKeeperNames : String → List (Option DeviceInode)
  afterStageNames : String → List (Option DeviceInode)
  afterRenameNames : String → List (Option DeviceInode)
  afterMarkerNames : String → List (Option DeviceInode)
  keeperSettlement : ∀ name, afterKeeperNames name = [keeper.keeperView.child captured.root name]
  stageChoices : ∀ name, name ≠ stageName → afterStageNames name = afterKeeperNames name
  renameChoices : ∀ name, name ≠ stageName → name ≠ markerName → afterRenameNames name = afterStageNames name
  markerSettlement : ∀ name, afterMarkerNames name = [marker.renamedView.child captured.root name]

namespace BootstrapKeeperMarkerHandoff

variable {keeper : BootstrapZeroKeeperRoute listed} {marker : BootstrapMarkerCustody listed}

private theorem keeper_ne_stage : keeperName ≠ stageName := by decide
private theorem keeper_ne_marker : keeperName ≠ markerName := by decide

/-- Either keeper route reaches the same marker open boundary.
The listing-derived census at that boundary extends the keeper barrier's
reached census by the reported drops alone. -/
theorem heldAtStage (observed : BootstrapKeeperMarkerHandoff keeper marker) :
    let reached := keeper.settledInventory.afterDrops observed.between
    calls.slot ∈ reached.slots ∧ captured.cached ∈ reached.slots ∧
    marker.initial = keeper.settledImage := by
  intro reached
  dsimp only [reached]
  exact ⟨observed.stageInventory ▸ marker.lockBeforeStage,
    observed.stageInventory ▸ marker.directoryBeforeStage, observed.stageInput⟩

/-- Through staging, the marker file sync, rename, and final directory
barrier, the off-target keeper retains the same name and empty bytes.
The namespace frames protect names outside the actual operation targets.
The marker inode's file sync affects only that inode. -/
theorem preservesKeeper (observed : BootstrapKeeperMarkerHandoff keeper marker) :
    let inode := keeper.settledImage.active
    let fileSynced := marker.inodeState.completeFileSync marker.inodeState.active
    let markerSettled := fileSynced.settleBinding
    let expected := some keeper.keeperChild
    marker.stageChild.child ≠ keeper.keeperChild ∧
    marker.stageView.child captured.root keeperName = expected ∧
    marker.renamedView.child captured.root keeperName = expected ∧
    marker.renamedView.modelObject keeper.keeperChild = inode ∧
    observed.afterKeeperNames keeperName = [expected] ∧
    observed.afterStageNames keeperName = [expected] ∧
    observed.afterRenameNames keeperName = [expected] ∧
    observed.afterMarkerNames keeperName = [expected] ∧
    marker.inodeState.visible inode = ByteArray.empty ∧
    marker.inodeState.crashBytes inode = [ByteArray.empty] ∧
    fileSynced.crashBytes inode = [ByteArray.empty] ∧
    markerSettled.visible inode = ByteArray.empty ∧
    markerSettled.crashBytes inode = [ByteArray.empty] := by
  intro inode fileSynced markerSettled expected
  obtain ⟨_, _, located, identity⟩ := keeper.settledCustody
  have separate : inode ≠ marker.inodeState.active := by
    change keeper.settledImage.active ≠ marker.inodeState.active
    rw [← identity, marker.stageInode, observed.stageObjects]
    exact observed.separateInodes.symm
  have staged := (observed.stageNames keeperName keeper_ne_stage).trans located
  have renamed := (observed.renameNames keeperName keeper_ne_stage keeper_ne_marker).trans staged
  have oldNames : observed.afterKeeperNames keeperName = [expected] := by simp [observed.keeperSettlement, located, expected]
  have stagedNames := (observed.stageChoices keeperName keeper_ne_stage).trans oldNames
  have renamedNames := (observed.renameChoices keeperName keeper_ne_stage keeper_ne_marker).trans stagedNames
  have finalNames : observed.afterMarkerNames keeperName = [expected] := by
    simp [observed.markerSettlement, renamed, expected]
  obtain ⟨visible, crash⟩ := observed.stageBytes inode separate
  rw [observed.stageInput] at visible crash
  have visibleEmpty := visible.trans keeper.settledVisible
  have durableEmpty := crash.trans keeper.settledEmpty.2
  have syncEmpty : fileSynced.crashBytes inode = [ByteArray.empty] := by
    simp [fileSynced, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, separate, durableEmpty]
  exact ⟨fun same => observed.separateInodes (congrArg captured.view.modelObject same),
    staged, renamed, (congrArg (· keeper.keeperChild) observed.renameObjects).trans identity,
    oldNames, stagedNames, renamedNames, finalNames, visibleEmpty, durableEmpty,
    syncEmpty, visibleEmpty, syncEmpty⟩

/-- Both reports have one stateful suffix from the keeper directory
barrier through the actual ordered marker replacement. The output cache
holds the original directory and has consumed the marker's staged entry. -/
theorem publishes (observed : BootstrapKeeperMarkerHandoff keeper marker) :
    let input := keeper.keeperImage.completeFileSync keeper.keeperImage.active
    let stagePath := directory.file .stagedWalBoundary
    let stage := writeFreshStagedWith marker.tryCreate (removeStaleStagingWith marker.statStale marker.unlinkStale)
      marker.create marker.write marker.flush
    let grouped := SyncPathGroup.run (sync directory.path marker.read marker.fsync)
    let rename := fun source dest (state : Cache Handle × Files) =>
      withCache state.1 (marker.rename source dest state.2)
    let replacement := Publication.performReplacement
      (fun path => stageFreshWithCache path (WAL.Boundary.encode 0) stage) grouped rename
      stagePath directory.path (fun _ => directory.file .walBoundary) #[]
    (keeper.groupedSync #[directory.path] *> Publication.run replacement)
      (captured.cache, keeper.fileSyncedState, input) =
      .ok () (captured.cache.consume stagePath, marker.publishedState,
        (marker.inodeState.completeFileSync marker.inodeState.active).settleBinding) := by
  intro input stagePath stage grouped rename replacement
  obtain ⟨wrote, fileSynced, directorySynced⟩ := marker.callbacks
  have reached := keeper.reachesMarker
  change keeper.groupedSync #[directory.path] (captured.cache, keeper.fileSyncedState, input) =
    .ok () (captured.cache, ⟨before.image.metadata.syncDirectory, .durable⟩, keeper.settledImage) at reached
  rw [← observed.stageInput] at reached
  rw [show Publication.run replacement = _ from Publication.run_performReplacement _ _ _ _ _ _ _]
  simp only [SeqRight.seqRight, EStateM.seqRight, Bind.bind, EStateM.bind, reached]
  have singleton : (#[].push stagePath) = #[stagePath] := rfl
  simp only [singleton, stagePath, stage, grouped]
  erw [wrote]
  dsimp only
  rw [fileSynced]
  simp only [rename, withCache, marker.renameReturned]
  rw [directorySynced]
  rfl

/-- The kept inode and published marker coexist at the final effect,
and the reported callbacks install the empty writer returned by the
admitted opener. -/
theorem installs {input : FilePath} (observed : BootstrapKeeperMarkerHandoff keeper marker)
    (admission : OpenAdmissionReports input directory calls.slot) (valid : BootstrapValid before.image)
    (allowCollection : Bool) :
    let markerSettled := (marker.inodeState.completeFileSync marker.inodeState.active).settleBinding
    observed.afterMarkerNames keeperName = [some keeper.keeperChild] ∧
    observed.afterMarkerNames markerName = [some marker.stageChild.child] ∧
    markerSettled.crashBytes keeper.settledImage.active = [ByteArray.empty] ∧
    markerSettled.crashBytes marker.inodeState.active = [WAL.Boundary.encode 0] ∧
    ∃ after, ∃ bootstrap : BootstrapReady after.image,
      let writer := bootstrap.writerState after.owners
      calls.run admission =
        .ok ⟨directory, calls.slot.description, .ready writer.installed, calls.nextRef, calls.nextRef + 1⟩ after ∧
      after.image = marker.publishedState ∧
      writer.RetainedReady directory calls.slot.description ∧
      SegmentedBatchDatabaseTrace directory calls.slot.description writer allowCollection [] calls.slot.description writer := by
  obtain ⟨_, _, _, _, _, _, _, keeperFinal, _, _, _, _, keeperBytes⟩ := observed.preservesKeeper
  obtain ⟨_, _, _, _, _, _, markerLive, _, _, _, markerBytes⟩ := marker.settledInode
  obtain ⟨after, bootstrap, returned, ready, trace⟩ :=
    keeper.installs admission valid marker.markerHealthy allowCollection
  exact ⟨keeperFinal, (observed.markerSettlement _).trans (congrArg (fun child => [child]) markerLive),
    keeperBytes, markerBytes, after, bootstrap, returned,
    marker.publishedImage admission valid keeper.rotationHealthy returned, ready, trace⟩

end BootstrapKeeperMarkerHandoff

end Alvoki.Storage.DiskSession
