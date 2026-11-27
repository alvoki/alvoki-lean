import Alvoki.Storage.Disk.Proofs.Recovery.ListedStagedWriteFailure
import Alvoki.Storage.Disk.Proofs.Recovery.ListedDirectoryAuthorizationFailure

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

variable {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout before.image history}
  {operations : MarkedRetryChunkOperations (Cache (DescriptorInventory × DescriptorSlot × Nat)) directory layout}
  {published : CheckpointPublication.Image}
  {held : HeldDirectoryMarkedRetryReports operations published}
  {authorization : ListedDirectoryAuthorization held}
  {pruning : LongKeeperPruning authorization}

/-- A failed stage write feeds the admitted opener's local cleanup and
extends its bounded retry with the exact reached scratch. The unlock
report determines the returned error and whether the lock stays owned. -/
theorem ListedStagedWriteFailure.continuesAfterError
    {input : FilePath} {source : LockedFileState FileImage} {admits : Target → Prop}
    (failure : ListedStagedWriteFailure pruning) (metadata : HeldMarkedMetadata held)
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
    let cleanup := (operations.cachedAttempt localUnlock).cleanupError failure.cause failure.reached.image
    operations.runWithAdmission admission = .error cleanup.1 cleanup.2 ∧
    BoundedReopenTrace directory admits source cleanup.2 ∧ cleanup.2.image = failure.reached.image ∧
    match operations.unlock with
    | .success => cleanup.1 = failure.cause ∧ cleanup.2.owners (directory.file .lock) = none
    | .failure unlockError _ =>
      cleanup.1 = unlockError ∧ cleanup.2.owners (directory.file .lock) = some operations.slot.description := by
  have finished := failure.finishError
  rw [authorization.keeper.extent] at finished
  exact metadata.continuesAfterRepairError admission localUnlock keeperValid laterValid following accepted ordered
    finished failure.preservesRepair prior admitted

end Alvoki.Storage.DiskSession
