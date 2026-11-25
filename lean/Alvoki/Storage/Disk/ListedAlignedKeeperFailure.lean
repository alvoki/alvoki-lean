import Alvoki.Storage.Disk.ListedAlignedKeeperRepair
import Alvoki.Storage.Disk.ListedDirectoryAuthorizationFailure

namespace Alvoki.Storage.DiskSession.ListedAlignedKeeperRepair

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

variable {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout before.image history}
  {operations : MarkedRetryChunkOperations (Cache (DescriptorInventory × DescriptorSlot × Nat)) directory layout}
  {published : CheckpointPublication.Image}
  {report : HeldDirectoryMarkedRetryReports operations published}
  {authorization : ListedDirectoryAuthorization report}

/-- A keeper sync error follows exact preparation and successful directory
authorization. The same cached attempt returns the reached file image and
applies local unlock precedence. That exact endpoint extends the retries. -/
theorem continuesAfterError {input : FilePath} {source : LockedFileState FileImage} {admits : Target → Prop}
    (repair : ListedAlignedKeeperRepair authorization) (metadata : HeldMarkedMetadata report)
    {cause : IO.Error} {nativeReached : LockedFileState FileImage}
    (failed : authorization.fsync (authorization.keeper.inventory, authorization.keeper.slot, 0)
      ⟨before.image.syncDirectory, before.owners.set (directory.file .lock) (some operations.slot.description)⟩ =
        .error cause nativeReached)
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
    let path := directory.file (.walSegment layout.keeper.first)
    let groupedError := IO.userError s!"sync failed for '{path}': {cause}"
    let reached := if repair.effective then before.image.syncDirectory.syncKeeper else before.image.syncDirectory
    let cleanup := (operations.cachedAttempt localUnlock).cleanupError groupedError reached
    operations.runWithAdmission admission = .error cleanup.1 cleanup.2 ∧
    BoundedReopenTrace directory admits source cleanup.2 ∧ cleanup.2.image = reached ∧
    match operations.unlock with
    | .success => cleanup.1 = groupedError ∧ cleanup.2.owners (directory.file .lock) = none
    | .failure unlockError _ =>
      cleanup.1 = unlockError ∧ cleanup.2.owners (directory.file .lock) = some operations.slot.description := by
  exact metadata.continuesAfterRepairError admission localUnlock keeperValid laterValid following accepted ordered
    (repair.finishResult.trans (repair.syncError failed)) repair.effects prior admitted

end Alvoki.Storage.DiskSession.ListedAlignedKeeperRepair
