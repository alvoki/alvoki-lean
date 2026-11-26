import Alvoki.Storage.Disk.NativeCheckpointOpenChronology
import Alvoki.Storage.Disk.NativeLongKeeperFinalSyncError
import Alvoki.Storage.Disk.NativeMutatingOpenRetries
import Alvoki.Storage.Disk.AppendGroupedReports

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting
open WAL.Boundary (WalInodeImage)

section DirectorySync

variable {heap : Type} {directory : DiskDirectory} {initial : LockedFileState FileImage}
  {history : List WAL.Write} {layout : CanonicalKeeperLayout initial.image history}
  {operations : MarkedRetryChunkOperations
    (Cache (DescriptorInventory × DescriptorSlot × Nat)) directory layout}
  {published : CheckpointPublication.Image} {held : HeldDirectoryMarkedRetryReports operations published}
  {authorized : ListedDirectoryAuthorization held} {pruning : LongKeeperPruning authorized}
  {stage : ListedLongKeeperStageAt pruning} {renamed : ListedLongKeeperRename stage}

/-- Project the same returned final fsync onto the logical repair image
and its actual observed keeper inodes. Both error effects keep the
trimmed replacement visible. Only an effective call settles its name. -/
theorem ListedLongKeeperDirectoryIssue.observesFinalSyncError
    (issue : ListedLongKeeperDirectoryIssue renamed) (view : OpenCloseHeapView heap FileImage)
    (inodes : heap → WalInodeImage) (callbacks : AlignedKeeperCacheCallbacks heap)
    {handle : IO.FS.Handle} {issued reached : heap} {cause : IO.Error} {effective : Bool}
    (fileImage : view.files issued = issue.files)
    (keeperInodes : inodes issued = issue.stoppedInodes false)
    (failed : callbacks.sync handle issued = .error cause reached)
    (observed : FsyncResult (view.files issued, inodes issued)
      (issue.stopped true, (inodes issued).settleBinding) effective
      (projectResult (fun heap => (view.files heap, inodes heap)) (callbacks.sync handle issued))) :
    let replacement := stage.inventory.inode stage.slot.description
    view.files reached = issue.stopped effective ∧
    inodes reached = issue.stoppedInodes effective ∧
    (inodes reached).active = replacement ∧
    (inodes reached).visible replacement = layout.target.trimmed ∧
    (inodes reached).crashBytes replacement = [layout.target.trimmed] ∧
    (inodes reached).crashBindings =
      if effective then [replacement] else replacement :: renamed.original.crashBindings := by
  intro replacement
  rw [failed, projectResult, fileImage, keeperInodes] at observed
  have selects {projected : LockedFileState FileImage × WalInodeImage} {applied : Bool}
      (reported : FsyncResult (issue.files, issue.stoppedInodes false)
        (issue.stopped true, (issue.stoppedInodes false).settleBinding) applied (.error cause projected)) :
      projected = (issue.stopped applied, issue.stoppedInodes applied) := by
    cases reported <;> rfl
  have outcome := selects observed
  have seen : inodes reached = issue.stoppedInodes effective := congrArg Prod.snd outcome
  refine ⟨congrArg Prod.fst outcome, seen, (congrArg WalInodeImage.active seen).trans (issue.stoppedBindings effective).1,
    ?_, ?_, ?_⟩
  · rw [seen]
    cases effective <;> simp [replacement, ListedLongKeeperDirectoryIssue.stoppedInodes,
      WalInodeImage.renameSynced, WalInodeImage.settleBinding, CanonicalKeeperLayout.target]
  · rw [seen]
    cases effective <;> simp [replacement, ListedLongKeeperDirectoryIssue.stoppedInodes,
      WalInodeImage.renameSynced, WalInodeImage.settleBinding, CanonicalKeeperLayout.target]
  · rw [seen]
    exact (issue.stoppedBindings effective).2

end DirectorySync

section Finalization

variable {heap : Type} {view : OpenCloseHeapView heap FileImage} {directory : DiskDirectory}
  {calls : RawOpenAdmissionCallbacks heap} {init : OpenSyncCacheCallbacks heap}
  {release : IO.FS.Handle → heap → heap} {input : FilePath} {entry : heap} {workerImage : FileImage}

/-- Cache disposal and lock cleanup retain the worker's live keeper.
This applies to an unchanged keeper and to one already replaced. -/
theorem RawFinalizedOpenAttempt.keepsObservedKeeper
    (failed : RawFinalizedOpenAttempt view directory calls init release input entry workerImage)
    {target : Target} {names : heap → FilePath → Option Nat} {visible : heap → Nat → ByteArray}
    (frames : failed.disposed.ScopeFileFrames failed.finalized
      (fun heap => ⟨names heap, fun inode => [visible heap inode]⟩) (· = directory.file (.walSegment target.first)))
    (worker : workerImage.keeper.active =
      (names failed.beforeCleanup (directory.file (.walSegment target.first))).map (visible failed.beforeCleanup)) :
    RawOpenRetryTrace.KeeperAt view directory target names visible failed.reached := by
  obtain ⟨_, _, _, _, _, _, returnedImage, _⟩ := failed.returns
  unfold RawOpenRetryTrace.KeeperAt
  rw [returnedImage, worker]
  exact (frames.afterWorker.visiblePayload rfl).symm

end Finalization

end Alvoki.Storage.DiskSession
