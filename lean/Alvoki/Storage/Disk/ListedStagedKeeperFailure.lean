import Alvoki.Storage.Disk.ListedStagedKeeperRepair
import Alvoki.Storage.Disk.ListedDirectoryAuthorizationFailure

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

variable {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout before.image history}
  {operations : MarkedRetryChunkOperations (Cache (DescriptorInventory × DescriptorSlot × Nat)) directory layout}
  {published : CheckpointPublication.Image}
  {held : HeldDirectoryMarkedRetryReports operations published}
  {authorization : ListedDirectoryAuthorization held}
  {prune : ListedLongKeeperPrune authorization}

namespace ListedLongKeeperStage

private abbrev written : LockedFileState FileImage :=
  ⟨before.image.syncDirectory.withScratch (some (layout.keeper.bytes, false)),
    before.owners.set (directory.file .lock) (some operations.slot.description)⟩

/-- A reported stage sync error keeps the authorized live keeper and
returns the same scratch bytes. Only an effective staged sync marks
those bytes durable. The bounded worker stops before publishing them. -/
theorem finishError (stage : ListedLongKeeperStage prune)
    {cause : IO.Error} {nativeReached : LockedFileState FileImage}
    (failed : authorization.fsync (stage.inventory, stage.slot, stage.offset)
      (written (operations := operations)) = .error cause nativeReached) :
    let path := directory.file .stagedWal
    let reached := before.image.syncDirectory.withScratch (some (layout.keeper.bytes, stage.effective))
    finishBoundedMarkedOpen directory layout.boundedPlan layout.plan.keeperBytes.size
      operations.removeFile (operations.write operations.cache) (operations.sync operations.cache)
      operations.renameFile before.image =
      .error (IO.userError s!"sync failed for '{path}': {cause}") reached := by
  intro path reached
  let durable := before.image.syncDirectory.withScratch (some (layout.keeper.bytes, true))
  have sync := stage.stageCallbacks.2
  change operations.sync operations.cache #[path] (written (operations := operations)).image =
    (match authorization.fsync (stage.inventory, stage.slot, stage.offset) (written (operations := operations)) with
    | .ok () _ => EStateM.Result.ok () durable
    | .error reported _ => EStateM.Result.error (IO.userError s!"sync failed for '{path}': {reported}")
        (if stage.effective then durable else (written (operations := operations)).image)) at sync
  rw [failed] at sync
  have second : operations.sync operations.cache #[path] (written (operations := operations)).image =
      .error (IO.userError s!"sync failed for '{path}': {cause}") reached := by
    cases effective : stage.effective <;>
      simpa [effective, reached, durable] using sync
  have physical : authorization.keeper.metadata.byteSize.toNat = layout.plan.keeperBytes.size :=
    authorization.keeper.extent
  have finish := stage.finishFromStage
  dsimp only at finish
  rw [physical, second] at finish
  exact finish

/-- The reported staged sync result of the same admitted attempt supplies
the exact continuation after cleanup. An unlock error takes precedence
and retains the acquired owner. -/
theorem continuesAfterSyncError {input : FilePath} {source : LockedFileState FileImage} {admits : Target → Prop}
    (stage : ListedLongKeeperStage prune) (metadata : HeldMarkedMetadata held)
    {cause : IO.Error} {nativeReached : LockedFileState FileImage}
    (failed : authorization.fsync (stage.inventory, stage.slot, stage.offset)
      (written (operations := operations)) = .error cause nativeReached)
    (admission : OpenAdmissionReports input directory operations.slot)
    (localUnlock : operations.unlock.LocalFlock)
    (keeperValid : before.image.keeper.Valid layout.target.Accepts)
    (laterValid : before.image.later.Beyond layout.range.through)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      before.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (prior : BoundedReopenTrace directory admits source before) (admitted : admits layout.target) :
    let path := directory.file .stagedWal
    let groupedError := IO.userError s!"sync failed for '{path}': {cause}"
    let reached := before.image.syncDirectory.withScratch (some (layout.keeper.bytes, stage.effective))
    let cleanup := (operations.cachedAttempt localUnlock).cleanupError groupedError reached
    operations.runWithAdmission admission = .error cleanup.1 cleanup.2 ∧
    BoundedReopenTrace directory admits source cleanup.2 ∧ cleanup.2.image = reached ∧
    match operations.unlock with
    | .success => cleanup.1 = groupedError ∧ cleanup.2.owners (directory.file .lock) = none
    | .failure unlockError _ =>
      cleanup.1 = unlockError ∧ cleanup.2.owners (directory.file .lock) = some operations.slot.description := by
  exact metadata.continuesAfterRepairError admission localUnlock keeperValid laterValid following accepted ordered
    (stage.finishError failed) (EffectTrace.scratch .authorized) prior admitted

end ListedLongKeeperStage

variable {stage : ListedLongKeeperStage prune}

private def renamedFiles (before : FileImage) (bytes : ByteArray) : FileImage :=
  { before.syncDirectory with keeper := ⟨some bytes, some bytes :: before.keeper.crashImages, none⟩ }

/-- The synced scratch, published replacement, and settled replacement are
the next three exact cuts of the same checked repair plan. -/
private theorem longKeeperCuts (prune : ListedLongKeeperPrune authorization) :
    let synced := before.image.syncDirectory.withScratch (some (layout.keeper.bytes, true))
    let renamed := renamedFiles before.image layout.keeper.bytes
    EffectTrace layout.target before.image synced ∧
    EffectTrace layout.target before.image renamed ∧
    EffectTrace layout.target before.image renamed.syncDirectory.syncKeeper := by
  have absent : before.image.syncDirectory.later.DurablyEmpty := by
    simp [FileImage.syncDirectory, LaterNames.syncDirectory, LaterNames.DurablyEmpty, LaterNames.settled, prune.noLater]
  exact ⟨.replace .authorized absent (cut := 2) rfl,
    .replace .authorized absent (cut := 3) rfl, .replace .authorized absent (cut := 4) rfl⟩

/-- An error from rename retains the exact selected repair prefix. A
reported rename effect leaves old and new crash choices. An error before
the effect keeps the synced scratch and the original keeper binding. The
admitted open returns that state with the reported cleanup precedence. -/
theorem ListedLongKeeperRename.continuesAfterError
    {input : FilePath} {source : LockedFileState FileImage} {admits : Target → Prop}
    (rename : ListedLongKeeperRename stage) (metadata : HeldMarkedMetadata held) {cause : IO.Error}
    (failed : rename.outcome = .errorBeforeEffect cause ∨ rename.outcome = .errorAfterEffect cause)
    (admission : OpenAdmissionReports input directory operations.slot)
    (localUnlock : operations.unlock.LocalFlock)
    (keeperValid : before.image.keeper.Valid layout.target.Accepts)
    (laterValid : before.image.later.Beyond layout.range.through)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      before.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (prior : BoundedReopenTrace directory admits source before) (admitted : admits layout.target) :
    let reached := if rename.outcome.effective then renamedFiles before.image layout.keeper.bytes
      else before.image.syncDirectory.withScratch (some (layout.keeper.bytes, true))
    let cleanup := (operations.cachedAttempt localUnlock).cleanupError cause reached
    operations.runWithAdmission admission = .error cleanup.1 cleanup.2 ∧
    BoundedReopenTrace directory admits source cleanup.2 ∧ cleanup.2.image = reached ∧
    match operations.unlock with
    | .success => cleanup.1 = cause ∧ cleanup.2.owners (directory.file .lock) = none
    | .failure unlockError _ =>
      cleanup.1 = unlockError ∧ cleanup.2.owners (directory.file .lock) = some operations.slot.description := by
  intro reached cleanup
  have aborted : rename.outcome ≠ .completed := by
    rcases failed with returned | returned <;> simp [returned]
  have physical : authorization.keeper.metadata.byteSize.toNat = layout.plan.keeperBytes.size :=
    authorization.keeper.extent
  have finish := rename.finishAfterError aborted
  dsimp only at finish
  rw [physical] at finish
  obtain ⟨synced, renamed, _⟩ := longKeeperCuts prune
  have effects : EffectTrace layout.target before.image reached := by
    rcases failed with returned | returned
    · simpa [reached, returned, KeeperRenameOutcome.effective] using synced
    · simpa [reached, returned, KeeperRenameOutcome.effective] using renamed
  have returned : finishBoundedMarkedOpen directory layout.boundedPlan layout.plan.keeperBytes.size
      operations.removeFile (operations.write operations.cache) (operations.sync operations.cache)
      operations.renameFile before.image = .error cause reached := by
    rcases failed with previous | applied
    · rw [previous] at finish
      simp only [reached, previous, KeeperRenameOutcome.effective, Bool.false_eq_true, ite_false]
      exact finish
    · rw [applied] at finish
      simp only [reached, applied, KeeperRenameOutcome.effective, ite_true]
      exact finish
  exact metadata.continuesAfterRepairError admission localUnlock keeperValid laterValid following accepted ordered
    returned effects prior admitted

/-- After rename, failure of the final directory sync leaves the published
replacement visible. Only a reported effective sync settles its name.
The same admitted cleanup and retry start at that exact returned image. -/
theorem ListedLongKeeperSettlement.continuesAfterError
    {input : FilePath} {source : LockedFileState FileImage} {admits : Target → Prop}
    {rename : ListedLongKeeperRename stage} (settlement : ListedLongKeeperSettlement rename)
    (metadata : HeldMarkedMetadata held) {cause : IO.Error}
    (failed : settlement.outcome = .errorBeforeEffect cause ∨ settlement.outcome = .errorAfterEffect cause)
    (admission : OpenAdmissionReports input directory operations.slot)
    (localUnlock : operations.unlock.LocalFlock)
    (keeperValid : before.image.keeper.Valid layout.target.Accepts)
    (laterValid : before.image.later.Beyond layout.range.through)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      before.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (prior : BoundedReopenTrace directory admits source before) (admitted : admits layout.target) :
    let renamed := renamedFiles before.image layout.keeper.bytes
    let reached := if settlement.outcome.effective then renamed.syncDirectory.syncKeeper else renamed
    let groupedError := IO.userError s!"sync failed for '{directory.path}': {cause}"
    let cleanup := (operations.cachedAttempt localUnlock).cleanupError groupedError reached
    operations.runWithAdmission admission = .error cleanup.1 cleanup.2 ∧
    BoundedReopenTrace directory admits source cleanup.2 ∧ cleanup.2.image = reached ∧
    match operations.unlock with
    | .success => cleanup.1 = groupedError ∧ cleanup.2.owners (directory.file .lock) = none
    | .failure unlockError _ =>
      cleanup.1 = unlockError ∧ cleanup.2.owners (directory.file .lock) = some operations.slot.description := by
  intro renamed reached groupedError cleanup
  have physical : authorization.keeper.metadata.byteSize.toNat = layout.plan.keeperBytes.size :=
    authorization.keeper.extent
  have finish := settlement.finishResult
  dsimp only at finish
  rw [physical] at finish
  have exactSync := settlement.syncResult
  dsimp only at exactSync
  obtain ⟨_, published, durable⟩ := longKeeperCuts prune
  have effects : EffectTrace layout.target before.image reached := by
    rcases failed with returned | returned
    · simpa [reached, renamed, returned, DelayedDirectorySyncOutcome.effective] using published
    · simpa [reached, renamed, returned, DelayedDirectorySyncOutcome.effective] using durable
  have returned : finishBoundedMarkedOpen directory layout.boundedPlan layout.plan.keeperBytes.size
      operations.removeFile (operations.write operations.cache) (operations.sync operations.cache)
      operations.renameFile before.image = .error groupedError reached := by
    refine finish.trans ?_
    rcases failed with previous | applied
    · rw [previous] at exactSync
      simp only [reached, previous, DelayedDirectorySyncOutcome.effective, Bool.false_eq_true, ite_false]
      exact exactSync
    · rw [applied] at exactSync
      simp only [reached, applied, DelayedDirectorySyncOutcome.effective, ite_true]
      exact exactSync
  exact metadata.continuesAfterRepairError admission localUnlock keeperValid laterValid following accepted ordered
    returned effects prior admitted

end Alvoki.Storage.DiskSession
