import Alvoki.Storage.Disk.NativeLongKeeperSettlementHeap
import Alvoki.Storage.Disk.NativeLongKeeperRepairPrefix

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting
open WAL.Boundary (WalInodeImage)

section

variable {heap : Type} {directory : DiskDirectory} {initial : LockedFileState FileImage}
  {history : List WAL.Write} {layout : CanonicalKeeperLayout initial.image history}
  {operations : MarkedRetryChunkOperations
    (SyncHandleRouting.Cache (DescriptorInventory × DescriptorSlot × Nat)) directory layout}
  {published : CheckpointPublication.Image}
  {held : HeldDirectoryMarkedRetryReports operations published}
  {authorized : ListedDirectoryAuthorization held}
  {pruning : LongKeeperPruning authorized} {staged : ListedLongKeeperStageAt pruning}
  {moved : ListedLongKeeperRename staged}

/-- Effectful settlement makes the measured keeper ready on the same
target, independently of the final call's reported return value. -/
theorem ListedLongKeeperDirectoryIssue.readyAfterEffect
    (issue : ListedLongKeeperDirectoryIssue moved)
    (prepared : Prepared initial.image layout.target layout.plan) :
    (issue.stopped true).image.Ready layout.target := by
  have valid := (issue.stoppedEffects true).valid prepared.pair prepared.keeperPrefix prepared.newer
  exact ⟨valid.selected, valid.settled, rfl, rfl, pruning.stageInputEffects.2⟩

/-- Once the replacement rename returned, the next live reader sees the
trimmed keeper and the suffix already removed by the earlier barrier. -/
theorem ListedLongKeeperDirectoryIssue.visibleAfterRename
    (issue : ListedLongKeeperDirectoryIssue moved) (effective : Bool) :
    (issue.stopped effective).image.keeper.active = some layout.target.trimmed ∧
      (issue.stopped effective).image.later.DurablyEmpty := by
  have pruned := pruning.stageInputEffects.2
  cases effective with
  | false => exact ⟨rfl, pruned⟩
  | true =>
    refine ⟨rfl, ?_⟩
    change pruning.stageInput.image.later.syncDirectory.DurablyEmpty
    exact ⟨pruned.1, congrArg (fun names => [names]) pruned.1⟩

/-- The cached handle at the issued call is live and refers to the
database directory whose child bindings can be settled by this fsync. -/
theorem ListedLongKeeperDirectoryIssue.rawDirectoryTarget
    (issue : ListedLongKeeperDirectoryIssue moved) (view : OpenCloseHeapView heap FileImage)
    (names : heap → FilePath → Option Nat) {issued : heap} {handle : IO.FS.Handle}
    (atIssue : view.handle issued handle = (issue.inventory, held.lifetime.directorySlot, 0))
    (census : view.descriptors issued = issue.inventory)
    (root : names issued directory.path = issue.bindings directory.path) :
    (view.handle issued handle).2.1 ∈ (view.descriptors issued).slots ∧
    names issued directory.path = some ((view.descriptors issued).inode (view.handle issued handle).2.1.description) := by
  obtain ⟨live, _, bound, _⟩ := issue.custody
  rw [atIssue, census]
  exact ⟨live, root.trans bound⟩

variable (callbacks : AlignedKeeperCacheCallbacks heap)
  (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
  (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
  (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
  (stage : LongKeeperStageCallbacks heap)
  (rename : FilePath → FilePath → EStateM IO.Error heap Unit)

local notation "grouped" => callbacks.syncPaths directory.path cached active pending
local notation "write" => stage.stage pending callbacks.modifyPending
local notation "perform" => performPaths directory layout.boundedPlan remove throw write grouped rename

/-- The same prepared long-keeper plan reaches its final directory
barrier after authorization, the suffix pass, stage sync and rename.
A returned error carries the reported filesystem effect of that call. -/
theorem ListedLongKeeperDirectoryIssue.rawFinalSyncError
    (issue : ListedLongKeeperDirectoryIssue moved) (view : OpenCloseHeapView heap FileImage)
    (names : heap → FilePath → Option Nat) {effective : Bool}
    {start afterAuthorization afterPrune recorded afterStage renamed issued reached : heap}
    {physical : Nat} {handle : IO.FS.Handle} {cause : IO.Error}
    (startFiles : (view.files start).image = initial.image)
    (measured : physical = authorized.keeper.metadata.byteSize.toNat)
    (authorizedRoot : grouped #[directory.path] start = .ok () afterAuthorization)
    (pruned : ((layout.boundedPlan.newer.map Step.unlink ++ [Step.syncPruned]).forM perform)
      afterAuthorization = .ok () afterPrune)
    (written : write (directory.file .stagedWal) layout.keeper.bytes afterPrune = .ok () recorded)
    (persisted : grouped #[directory.file .stagedWal] recorded = .ok () afterStage)
    (renamedFile : rename (directory.file .stagedWal) (directory.file (.walSegment layout.keeper.first))
      afterStage = .ok () renamed)
    (loaded : callbacks.getDirectory cached renamed = .ok (some handle) issued)
    (atIssue : view.handle issued handle = (issue.inventory, held.lifetime.directorySlot, 0))
    (census : view.descriptors issued = issue.inventory)
    (issuedFiles : view.files issued = issue.files)
    (root : names issued directory.path = issue.bindings directory.path)
    (keeper : names issued (directory.file (.walSegment layout.keeper.first)) =
      issue.bindings (directory.file (.walSegment layout.keeper.first)))
    (stageName : names issued (directory.file .stagedWal) = issue.bindings (directory.file .stagedWal))
    (failed : callbacks.sync handle issued = .error cause reached)
    (effect : callbacks.sync handle issued = .error cause reached →
      (view.handle issued handle).2.1 ∈ (view.descriptors issued).slots →
      names issued directory.path = some ((view.descriptors issued).inode (view.handle issued handle).2.1.description) →
      view.files issued = issue.files →
      view.files reached = issue.stopped effective)
    (namesKept : ∀ file, names reached (directory.file file) = names issued (directory.file file)) :
    finishBoundedMarkedOpen directory layout.boundedPlan physical remove write grouped rename start =
      .error (IO.userError s!"sync failed for '{directory.path}': {cause}") reached ∧
    view.files reached = issue.stopped effective ∧
    EffectTrace layout.target (view.files start).image (view.files reached).image ∧
    (view.files reached).image.keeper.active = some layout.target.trimmed ∧
    (effective = true → (view.files reached).image.keeper.crashImages = [some layout.target.trimmed]) ∧
    held.lifetime.directorySlot ∈ (view.descriptors issued).slots ∧ operations.slot ∈ (view.descriptors issued).slots ∧
    names reached (directory.file .stagedWal) = none ∧
    names reached (directory.file (.walSegment layout.keeper.first)) =
      some (staged.inventory.inode staged.slot.description) ∧
    (view.files reached).image.withKeeperInodes (issue.stoppedInodes effective) = (view.files reached).image ∧
    (issue.stoppedInodes effective).crashBytes (staged.inventory.inode staged.slot.description) =
      [layout.keeper.bytes] ∧
    (issue.stoppedInodes effective).crashBindings =
      if effective then [staged.inventory.inode staged.slot.description]
      else staged.inventory.inode staged.slot.description :: moved.original.crashBindings := by
  have bytes : layout.boundedPlan.keeperBytes.size = layout.boundedPlan.keeperSize := layout.target.trimmedSize
  have longer : layout.boundedPlan.keeperSize < physical :=
    bytes ▸ measured.symm ▸ pruning.longer
  have valid : layout.boundedPlan.valid = true :=
    (Plan.valid_iff _).mpr ⟨layout.target.firstCovered, Nat.le_of_eq bytes.symm, pruning.later⟩
  obtain ⟨dirLive, ownerLive, _, _, noStage, keeperBound⟩ := issue.custody
  obtain ⟨liveHandle, boundHandle⟩ := issue.rawDirectoryTarget view names atIssue census root
  have files := effect failed liveHandle boundHandle issuedFiles
  have trace : EffectTrace layout.target (view.files start).image (view.files reached).image := by
    rw [startFiles, files]
    exact issue.stoppedEffects effective
  refine ⟨?_, files, trace, ?_, ?_, census.symm ▸ dirLive, census.symm ▸ ownerLive,
    (namesKept .stagedWal).trans (stageName.trans noStage),
    (namesKept (.walSegment layout.keeper.first)).trans (keeper.trans keeperBound),
    files.symm ▸ issue.projectsStoppedInodes effective, ?_, (issue.stoppedBindings effective).2⟩
  · have groupedError : grouped #[directory.path] renamed =
        .error (IO.userError s!"sync failed for '{directory.path}': {cause}") reached := by
      rw [AlignedKeeperCacheCallbacks.syncPaths, SyncPathGroup.run_single]
      simp [syncWithHandles, Bind.bind, EStateM.bind, loaded, failed, Pure.pure, EStateM.pure]
      rfl
    rw [finishBoundedMarkedOpen_afterStage directory layout.boundedPlan physical remove write grouped rename
      valid bytes longer authorizedRoot pruned written]
    have movedKeeper : perform (.replace .renameStaged) afterStage = .ok () renamed := renamedFile
    have fsyncedStage : perform (.replace .syncStaged) recorded = .ok () afterStage := persisted
    have fsyncedDir : perform (.replace .syncDirectory) renamed = _ := groupedError
    simp only [Bind.bind, EStateM.bind, fsyncedStage, movedKeeper, fsyncedDir]
  · rw [files]
    cases effective <;> rfl
  · intro settled
    rw [files, settled]
    rfl
  · cases effective <;> simp [ListedLongKeeperDirectoryIssue.stoppedInodes, WalInodeImage.renameSynced,
      WalInodeImage.settleBinding]

end

end Alvoki.Storage.DiskSession
