import Alvoki.Storage.Disk.BatchRecoveryPrefix
import Alvoki.Storage.Disk.ListedStagedKeeperFailure

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix WalInodeImage)

variable {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout before.image history}
  {operations : MarkedRetryChunkOperations (SyncHandleRouting.Cache (DescriptorInventory × DescriptorSlot × Nat))
    directory layout} {published : CheckpointPublication.Image}
  {held : HeldDirectoryMarkedRetryReports operations published} {authorization : ListedDirectoryAuthorization held}
  {pruning : LongKeeperPruning authorization} {stage : ListedLongKeeperStageAt pruning}
  {rename : ListedLongKeeperRename stage}

namespace ListedLongKeeperDirectoryIssue

/-- Opening with the admitted inputs reaches the actual grouped callback
on the renamed image. The continuation describes only what a return from
that callback would do. -/
abbrev AtAdmission {input : FilePath} (issue : ListedLongKeeperDirectoryIssue rename)
    (admission : OpenAdmissionReports input directory operations.slot) : Prop :=
  ∃ opened : Reopened,
    operations.runWithAdmission admission =
      runOpenWithInstallation directory operations.slot.description operations.nextRef (.ok true) operations.unlock
        (fun _ => (do
          operations.sync operations.cache #[directory.path]
          pure opened : EStateM IO.Error FileImage Reopened) issue.files.image) before

/-- The admitted marked opener reaches this final barrier after the exact
checkpoint and keeper reads. If the issued callback returns, this is its
continuation through the parent open schedule. -/
theorem admittedAtIssue {input : FilePath} (issue : ListedLongKeeperDirectoryIssue rename)
    (admission : OpenAdmissionReports input directory operations.slot) (metadata : HeldMarkedMetadata held)
    (localUnlock : operations.unlock.LocalFlock) (prepared : Prepared before.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      before.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    issue.AtAdmission admission := by
  let attempt := operations.cachedAttempt localUnlock
  obtain ⟨opened, read⟩ := metadata.cachedAttemptPrepared localUnlock prepared.newer following accepted ordered
  change attempt.prepare before.image = _ at read
  let finish := (do
    operations.sync operations.cache #[directory.path]
    pure opened : EStateM IO.Error FileImage Reopened) issue.files.image
  have reached : attempt.recover before.image = finish := by
    unfold CachedOpenAttempt.recover reopenMarkedBoundedWithCachedExtents
    change (attempt.prepare >>= _) before.image = finish
    have issueResult : finishBoundedMarkedOpen directory layout.boundedPlan layout.plan.keeperBytes.size
        attempt.removeFile attempt.write attempt.sync attempt.renameFile before.image =
        operations.sync operations.cache #[directory.path] issue.files.image := by
      have extent : authorization.keeper.metadata.byteSize.toNat = layout.plan.keeperBytes.size :=
        authorization.keeper.extent
      have finished := issue.finishesFromIssue
      rw [extent] at finished
      exact finished
    simp only [Bind.bind, EStateM.bind, read, issueResult]
    rfl
  refine ⟨opened, ?_⟩
  rw [operations.runWithAdmission_eq_cached admission localUnlock metadata.callbackMetadata.markerPresent]
  let tail : EStateM IO.Error FileImage Reopened := fun _ => finish
  change runOpenWithInstallation directory operations.slot.description operations.nextRef (.ok true) operations.unlock
      attempt.recover before = runOpenWithInstallation directory operations.slot.description operations.nextRef (.ok true)
        operations.unlock tail before
  rw [runOpenWithInstallation_outcome, runOpenWithInstallation_outcome,
    runOpenWithImage_acquired, runOpenWithImage_acquired, reached]

/-- The same renamed inode remains visible. An effective directory
barrier makes it the sole crash binding. -/
def stoppedInodes (_issue : ListedLongKeeperDirectoryIssue rename) (effective : Bool) : WalInodeImage :=
  let inode := stage.inventory.inode stage.slot.description
  let renamed := rename.original.renameSynced inode layout.keeper.bytes
  if effective then renamed.settleBinding else renamed

theorem stoppedBindings (issue : ListedLongKeeperDirectoryIssue rename) (effective : Bool) :
    let replacement := stage.inventory.inode stage.slot.description
    let inodes := issue.stoppedInodes effective
    inodes.active = replacement ∧
      inodes.crashBindings = if effective then [replacement] else replacement :: rename.original.crashBindings := by
  cases effective <;> exact ⟨rfl, rfl⟩

theorem projectsStoppedInodes (issue : ListedLongKeeperDirectoryIssue rename) (effective : Bool) :
    (issue.stopped effective).image.withKeeperInodes (issue.stoppedInodes effective) =
      (issue.stopped effective).image := by
  cases effective with
  | false =>
    have renamed := (rename.publishesInode (by rw [issue.completed]; rfl)).2.2
    change issue.files.image = _ at renamed
    change issue.files.image.withKeeperInodes (issue.stoppedInodes false) = issue.files.image
    rw [renamed]
    rfl
  | true =>
    simp [stopped, stoppedInodes, files,
      FileImage.withKeeperInodes, WalInodeImage.project, WalInodeImage.settleBinding, WalInodeImage.renameSynced]
    rfl

/-- Both effects of the issued, nonreturning barrier are cuts of the same
authorized repair. The prefix has already durably pruned later names. -/
theorem stoppedEffects (issue : ListedLongKeeperDirectoryIssue rename) (effective : Bool) :
    EffectTrace layout.target before.image (issue.stopped effective).image := by
  obtain ⟨pruned, absent⟩ := pruning.stageInputEffects
  cases effective with
  | false => exact .replace pruned absent (cut := 3) rfl
  | true => exact .replace pruned absent (cut := 4) rfl

/-- An observed effect at the admitted callback extends the existing retry
prefix and keeps its initial files. The opener still owns the lock at this
point. A later exit or power loss starts from this exact stopped image. -/
theorem continuesPrefix {input : FilePath} {keeper : Nat} {initial : LockedFileState FileImage}
    (issue : ListedLongKeeperDirectoryIssue rename)
    (prior : ReportedReopenPrefix directory keeper initial before) (first : layout.target.first = keeper)
    (admission : OpenAdmissionReports input directory operations.slot) (metadata : HeldMarkedMetadata held)
    (localUnlock : operations.unlock.LocalFlock) (prepared : Prepared before.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      before.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) (effective : Bool) :
    issue.AtAdmission admission ∧ ReportedReopenPrefix directory keeper initial (issue.stopped effective) := by
  refine ⟨issue.admittedAtIssue admission metadata localUnlock prepared following accepted ordered, ?_⟩
  have acquired : TryLockObserves before.owners directory (.ok true) :=
    operations.acquired ▸ operations.acquisition
  have owner : (issue.stopped effective).owners =
      before.owners.set (directory.file .lock) (some operations.slot.description) := by
    cases effective <;> rfl
  have interrupted := ReportedReopenPrefix.repairInterrupted prior operations.slot.description
    acquired prepared first (issue.stoppedEffects effective)
  cases stopped : issue.stopped effective with
  | mk image owners =>
    simp only [stopped] at owner interrupted
    rwa [owner]

/-- A later power loss selects only the reported namespace and payload
possibilities after this effect. The same marker and sealed WAL survive
and each selected keeper accepts the same prefix. -/
theorem crashSurvivor (issue : ListedLongKeeperDirectoryIssue rename) (effective : Bool)
    (prepared : Prepared before.image layout.target layout.plan)
    {pair : DirectoryPublication.Bindings} {bytes : Option ByteArray} {later : List Nat}
    (metadata : pair ∈ (issue.stopped effective).image.directory.crashImages)
    (keeper : bytes ∈ (issue.stopped effective).image.keeper.crashImages)
    (names : later ∈ (issue.stopped effective).image.later.crashImages) :
    layout.target.Accepts bytes ∧
      let crashed := (issue.stopped effective).image.crash pair bytes later
      crashed.Valid layout.target ∧ crashed.kept = before.image.kept := by
  have stopped := issue.stoppedEffects effective
  have valid := stopped.valid prepared.pair prepared.keeperPrefix prepared.newer
  have crash := EffectTrace.crash stopped metadata keeper names
  exact ⟨valid.keeper.crashValid _ keeper,
    crash.valid prepared.pair prepared.keeperPrefix prepared.newer, crash.keepsSealed⟩

private theorem lockWasLive (issue : ListedLongKeeperDirectoryIssue rename) :
    operations.slot.reference ∈ issue.inventory.references operations.slot.description :=
  issue.inventory.mem_references.mpr ⟨operations.slot, issue.custody.2.1, rfl, rfl⟩

/-- Use the census carried to the issue, including aliases of the live
lock description, before interpreting the subsequent observed drops. -/
def lockReferences (issue : ListedLongKeeperDirectoryIssue rename) : HeldLockReferences operations.slot.description :=
  issue.inventory.held _ (List.ne_nil_of_mem issue.lockWasLive)

def afterExit (issue : ListedLongKeeperDirectoryIssue rename) (effective : Bool) (drops : List LockReferenceDrop) :
    LockedFileState FileImage :=
  issue.lockReferences.afterFileDrops drops directory (issue.stopped effective)

/-- Extend the known prefix with the issuing process's exit. The observed
exit removes its slots and a surviving alias can retain the lock. -/
theorem exits {keeper : Nat} {initial : LockedFileState FileImage}
    (issue : ListedLongKeeperDirectoryIssue rename) (effective : Bool)
    (prior : ReportedReopenPrefix directory keeper initial (issue.stopped effective)) (drops : List LockReferenceDrop)
    (sameProcess : held.lifetime.directorySlot.reference.process = operations.slot.reference.process)
    (exited : LockReferenceDrop.exited held.lifetime.directorySlot.reference.process ∈ drops)
    (prepared : Prepared before.image layout.target layout.plan) :
    let beforeDrops := issue.stopped effective
    let reached := issue.afterExit effective drops
    beforeDrops.owners.Owns directory operations.slot.description ∧
      operations.slot ∉ (issue.inventory.afterDrops drops).slots ∧
      held.lifetime.directorySlot ∉ (issue.inventory.afterDrops drops).slots ∧
      ReportedReopenPrefix directory keeper initial reached ∧
      (TryLockObserves reached.owners directory (.ok true) ↔
        (issue.inventory.afterDrops drops).references operations.slot.description = []) ∧
      reached.owners (directory.file .lock) =
        (if (issue.inventory.afterDrops drops).references operations.slot.description = [] then none
          else some operations.slot.description) ∧
      reached.image = beforeDrops.image ∧
      reached.image.Valid layout.target ∧ reached.image.kept = before.image.kept := by
  intro beforeDrops reached
  have owned : beforeDrops.owners.Owns directory operations.slot.description := by
    cases effective <;>
      change before.owners.set (directory.file .lock) (some operations.slot.description)
        (directory.file .lock) = some operations.slot.description <;>
      simp [LockOwners.set]
  have gone (slot : DescriptorSlot) (process : slot.reference.process = held.lifetime.directorySlot.reference.process) :
      slot ∉ (issue.inventory.afterDrops drops).slots := by
    intro present
    have stays := List.all_eq_true.mp (List.mem_filter.mp present).2 _ exited
    simp [LockReferenceDrop.removes, process] at stays
  have remaining : issue.lockReferences.remaining drops =
      (issue.inventory.afterDrops drops).references operations.slot.description :=
    issue.inventory.held_remaining _ _ drops
  have admitted := issue.lockReferences.afterFileDrops_admits owned (drops := drops)
  rw [remaining] at admitted
  have owner : reached.owners (directory.file .lock) =
      (if (issue.inventory.afterDrops drops).references operations.slot.description = [] then none
        else some operations.slot.description) := by
    change (issue.lockReferences.afterFileDrops drops directory beforeDrops).owners (directory.file .lock) = _
    rw [← remaining]
    by_cases last : issue.lockReferences.remaining drops = []
    · rw [issue.lockReferences.afterFileDrops_released owned last]
      simp [last, LockOwners.set]
    · rw [issue.lockReferences.afterFileDrops_surviving last]
      simpa only [ite_eq_right last, LockOwners.Owns] using owned
  have effects := issue.stoppedEffects effective
  exact ⟨owned, gone _ sameProcess.symm, gone _ rfl, .referenceDrops prior issue.lockReferences drops, admitted, owner, rfl,
    effects.valid prepared.pair prepared.keeperPrefix prepared.newer, effects.keepsSealed⟩

end ListedLongKeeperDirectoryIssue
end Alvoki.Storage.DiskSession
