import Alvoki.Storage.Disk.ListedStagedKeeperRepair
import Alvoki.Storage.Disk.ListedDirectoryAuthorizationFailure

namespace Alvoki.Storage.DiskSession.ListedLongKeeperStage

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

variable {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout before.image history}
  {operations : MarkedRetryChunkOperations (Cache (DescriptorInventory × DescriptorSlot × Nat)) directory layout}
  {published : CheckpointPublication.Image}
  {held : HeldDirectoryMarkedRetryReports operations published}
  {authorization : ListedDirectoryAuthorization held}
  {prune : ListedLongKeeperPrune authorization}

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

end Alvoki.Storage.DiskSession.ListedLongKeeperStage
