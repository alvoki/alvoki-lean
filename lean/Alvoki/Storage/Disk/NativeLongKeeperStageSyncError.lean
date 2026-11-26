import Alvoki.Storage.Disk.NativeLongKeeperRepairPrefix
import Alvoki.Storage.Disk.NativeLongKeeperSuffixStageHeap
import Alvoki.Storage.Disk.NativeRawSync
import Alvoki.Storage.Disk.AppendGroupedReports

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting
open WAL.Boundary (WalInodeImage)

section StageSync

variable {heap : Type} {directory : DiskDirectory} (plan : Plan) (physicalSize : Nat)
  (stage : LongKeeperStageCallbacks heap) (callbacks : AlignedKeeperCacheCallbacks heap)
  (directoryRef : IO.Ref (Option IO.FS.Handle)) (activeRef : IO.Ref (Option (FilePath × IO.FS.Handle)))
  (pendingRef : IO.Ref (List (FilePath × IO.FS.Handle)))
  (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
  (rename : FilePath → FilePath → EStateM IO.Error heap Unit)

local notation "writeStage" => stage.stage pendingRef callbacks.modifyPending
local notation "grouped" => callbacks.syncPaths directory.path directoryRef activeRef pendingRef
local notation "scratch" => directory.file DiskFile.stagedWal

private theorem fsyncErrorEffect {state : Type} {issue persisted reached : state} {effective : Bool}
    {cause : IO.Error} (observed : FsyncResult issue persisted effective (.error cause reached)) :
    reached = if effective then persisted else issue := by
  cases observed <;> rfl

/-- The returned `WAL.next` error consumes the exact freshly written
descriptor from the original pending cache. It stops the repair before
rename or the final directory sync. The physical fsync effect determines
only the durability of those scratch bytes. -/
theorem AlignedKeeperCacheCallbacks.longRepairStageSyncFails
    (valid : plan.valid = true) (size : plan.keeperBytes.size = plan.keeperSize)
    (longer : plan.keeperSize < physicalSize) {entry authorized pruned created written flushed recorded consumed reached : heap}
    {descriptor : IO.FS.Handle} {cause : IO.Error} {effective : Bool}
    (view : OpenCloseHeapView heap FileImage) (inodes : heap → WalInodeImage)
    (names : heap → FilePath → Option Nat)
    (authorizedCall : grouped #[directory.path] entry = .ok () authorized)
    (prune : ((plan.newer.map Step.unlink ++ [Step.syncPruned]).forM
      (performPaths directory plan remove throw writeStage grouped rename)) authorized = .ok () pruned)
    (fresh : stage.tryCreate scratch pruned = .ok (.ok descriptor) created)
    (wrote : stage.write descriptor plan.keeperBytes created = .ok () written)
    (flushedBytes : stage.flush descriptor written = .ok () flushed)
    (remembered : callbacks.modifyPending pendingRef (pushPending scratch descriptor) flushed = .ok () recorded)
    (loaded : callbacks.getPending pendingRef recorded = .ok [(scratch, descriptor)] recorded)
    (cleared : callbacks.setPending pendingRef [] recorded = .ok () consumed)
    (failed : callbacks.sync descriptor consumed = .error cause reached)
    (target : RawFsyncTarget view created consumed descriptor)
    (source : let inode := (view.handle created descriptor).1.inode (view.handle created descriptor).2.1.description
      names consumed scratch = some inode ∧ (inodes consumed).visible inode = plan.keeperBytes)
    (scratchWritten : view.files consumed = { view.files pruned with
      image := (view.files pruned).image.withScratch (some (plan.keeperBytes, false)) })
    (keptNames : names reached = names consumed)
    (observed : let inode := (view.descriptors consumed).inode (view.handle consumed descriptor).2.1.description
      FsyncResult (view.files consumed, inodes consumed)
        ({ view.files consumed with image := (view.files consumed).image.withScratch (some (plan.keeperBytes, true)) },
          (inodes consumed).completeFileSync inode)
        effective (projectResult (fun heap => (view.files heap, inodes heap)) (callbacks.sync descriptor consumed)))
    {initial : FileImage} {selected : Target} (prior : EffectTrace selected initial (view.files pruned).image) :
    let inode := (view.handle created descriptor).1.inode (view.handle created descriptor).2.1.description
    finishBoundedMarkedOpen directory plan physicalSize remove writeStage grouped rename entry =
      .error (IO.userError s!"sync failed for '{scratch}': {cause}") reached ∧
    view.files reached = { view.files pruned with
      image := (view.files pruned).image.withScratch (some (plan.keeperBytes, effective)) } ∧
    EffectTrace selected initial (view.files reached).image ∧
    names reached scratch = some inode ∧ (inodes reached).visible inode = plan.keeperBytes ∧
    (inodes reached).crashBytes inode =
      if effective then [plan.keeperBytes] else (inodes consumed).crashBytes inode := by
  intro inode
  have stagedCall : writeStage scratch plan.keeperBytes pruned = .ok () recorded := by
    simp only [LongKeeperStageCallbacks.stage, writeFreshStagedWith, withFreshStaging, Bind.bind, EStateM.bind,
      fresh, Pure.pure, EStateM.pure, wrote, flushedBytes, remembered]
  have groupError : grouped #[scratch] recorded =
      .error (IO.userError s!"sync failed for '{scratch}': {cause}") reached := by
    rw [AlignedKeeperCacheCallbacks.syncPaths, SyncPathGroup.run_single]
    simp [syncWithHandles, Bind.bind, EStateM.bind, file_ne_directory directory .stagedWal,
      loaded, cleared, failed, Pure.pure, EStateM.pure]
    rfl
  have finish : finishBoundedMarkedOpen directory plan physicalSize remove writeStage grouped rename entry =
      .error (IO.userError s!"sync failed for '{scratch}': {cause}") reached := by
    rw [finishBoundedMarkedOpen_afterStage directory plan physicalSize remove writeStage grouped rename valid size
      longer authorizedCall prune stagedCall]
    simp only [performPaths, Publication.performReplacement, Array.push_empty, Bind.bind, EStateM.bind, groupError]
  rw [failed, projectResult] at observed
  have localEffect : (view.files reached, inodes reached) = if effective then
      ({ view.files consumed with image := (view.files consumed).image.withScratch (some (plan.keeperBytes, true)) },
        (inodes consumed).completeFileSync inode) else (view.files consumed, inodes consumed) := by
    rw [target.inode] at observed
    exact fsyncErrorEffect observed
  have files : view.files reached = { view.files pruned with
      image := (view.files pruned).image.withScratch (some (plan.keeperBytes, effective)) } := by
    cases effective <;> simpa [scratchWritten, FileImage.withScratch] using congrArg Prod.fst localEffect
  have effects : EffectTrace selected initial (view.files reached).image := by
    rw [files]
    exact .scratch prior
  have sourceBytes : (inodes consumed).visible inode = plan.keeperBytes := source.2
  have visible : (inodes reached).visible inode = plan.keeperBytes := by
    cases effective <;> simpa [WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, sourceBytes] using
      congrArg (fun files => files.2.visible inode) localEffect
  have durable : (inodes reached).crashBytes inode =
      if effective then [plan.keeperBytes] else (inodes consumed).crashBytes inode := by
    cases effective <;> simpa [WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, sourceBytes] using
      congrArg (fun files => files.2.crashBytes inode) localEffect
  exact ⟨finish, files, effects, (congrFun keptNames scratch).trans source.1, visible, durable⟩

end StageSync
end Alvoki.Storage.DiskSession
