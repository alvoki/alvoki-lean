import Alvoki.Storage.Disk.CheckpointHeldOpen
import Alvoki.Storage.Disk.Proofs.Recovery.ListedPrunedAlignedKeeper
import Alvoki.Storage.Disk.Proofs.Recovery.ListedStagedKeeperRepair

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair CheckpointPublication

variable {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout before.image history}
  {operations : MarkedRetryChunkOperations (Cache CheckpointOpenHandle) directory layout}
  {published : Image} {held : HeldDirectoryMarkedRetryReports operations published}

/-- The observed keeper extent and visible suffix exhaust the finish routes
for a valid selected prefix. -/
theorem ListedDirectoryAuthorization.finishAlternatives (authorization : ListedDirectoryAuthorization held) :
    (layout.keeper.bytes.size = authorization.keeper.metadata.byteSize.toNat ∧ before.image.later.visible = []) ∨
    (layout.keeper.bytes.size = authorization.keeper.metadata.byteSize.toNat ∧ before.image.later.visible ≠ []) ∨
    layout.keeper.bytes.size < authorization.keeper.metadata.byteSize.toNat := by
  have extent := authorization.keeper.extent
  rw [ByteArray.size_append] at extent
  have fits : layout.keeper.bytes.size ≤ authorization.keeper.metadata.byteSize.toNat := by omega
  rcases Nat.eq_or_lt_of_le fits with aligned | longer
  · by_cases empty : before.image.later.visible = []
    · exact .inl ⟨aligned, empty⟩
    · exact .inr (.inl ⟨aligned, empty⟩)
  · exact .inr (.inr longer)

/-- The three ways the shared marked finisher can complete after the checked
listing. Every case uses the same authorization and callbacks. In the
replacement case, the pruning report covers both possible suffix routes. -/
inductive ListedMarkedFinish (authorization : ListedDirectoryAuthorization held) : Type where
  | aligned (repair : ListedAlignedKeeperRepair authorization)
      (keeperReturned : ∃ reached, repair.keeperFsyncReturn = .ok () reached)
  | pruned {prune : ListedLaterWalPrune authorization} (repair : ListedPrunedAlignedKeeper prune)
      (keeperReturned : ∃ reached, repair.keeperFsyncReturn = .ok () reached)
  | replaced {pruning : LongKeeperPruning authorization} {stage : ListedLongKeeperStageAt pruning}
      {rename : ListedLongKeeperRename stage} (settlement : ListedLongKeeperSettlement rename)
      (directoryReturned : settlement.outcome = .completed)

namespace ListedMarkedFinish

variable {authorization : ListedDirectoryAuthorization held}

/-- All finish paths obtain authorization from their own first barrier. -/
theorem authorized (observed : ListedMarkedFinish authorization) :
    authorization.outcome = .completed := by
  cases observed with
  | aligned repair _ => exact repair.completed
  | @pruned prune _ _ => exact prune.authorized
  | @replaced pruning _ _ _ _ => exact pruning.completed

/-- The exact branch-specific primitive reports imply the shared finish
contract, including the ordered later-name schedule when present. -/
theorem healthyFinish (observed : ListedMarkedFinish authorization) :
    operations.HealthyFinish := by
  cases observed with
  | aligned repair keeperReturned => exact repair.healthyFinish keeperReturned
  | pruned repair keeperReturned => exact repair.healthyFinishOfKeeperReturn keeperReturned
  | replaced settlement directoryReturned => exact settlement.healthyFinish directoryReturned

end ListedMarkedFinish

/-- The observations of one admitted marked open, through the successful
return of its last primitive. -/
structure PrimitiveCheckpointHeldOpen (input : FilePath) (directory : DiskDirectory)
    {retry : LockedFileState FileImage} {history : List WAL.Write}
    (layout : CanonicalKeeperLayout retry.image history) (physical : Image) where
  calls : MarkedRetryChunkCalls (Cache CheckpointOpenHandle) directory retry
  wal : HeldWalInstallReads layout calls
  held : HeldDirectoryMarkedRetryReports wal.operations physical
  namespaceMatches : held.lifetime.namespaceView = wal.view
  rootMatches : held.lifetime.root = wal.root
  authorization : ListedDirectoryAuthorization held
  metadata : HeldMarkedMetadata held
  finish : ListedMarkedFinish authorization
  admission : OpenAdmissionReports input directory calls.slot

/-- Package the primitive finish reports for the existing exact checkpoint
and clean-reopen theorems. The held listing, payload reads, lock admission,
authorization and finishing effects all use these same callbacks. -/
def PrimitiveCheckpointHeldOpen.toHeldOpen {input directory history physical} {retry : LockedFileState FileImage}
    {layout : CanonicalKeeperLayout retry.image history}
    (observed : PrimitiveCheckpointHeldOpen input directory layout physical) :
    CheckpointHeldOpen input directory layout physical where
  calls := observed.calls
  wal := observed.wal
  held := observed.held
  namespaceMatches := observed.namespaceMatches
  rootMatches := observed.rootMatches
  authorization := observed.authorization
  metadata := observed.metadata
  completed := observed.finish.authorized
  healthy := observed.finish.healthyFinish
  admission := observed.admission

/-- A checkpoint recovery witness may supply primitive completion reports
on the layout derived after its finite failed attempts and crash cuts. -/
theorem CheckpointHeldOpen.reportsFromPrimitives {input directory} {before : SegmentedWriterState}
    {retry : LockedFileState FileImage} {published physical : Image}
    (observed : ∀ layout : CanonicalKeeperLayout retry.image before.history,
      layout.keeper = before.wal.active → layout.tail = ByteArray.empty →
      layout.sealed ++ [layout.keeper] =
        (published.segmentedCheckpointView before.wal).readDescriptors layout.range.watermark →
      Nonempty (PrimitiveCheckpointHeldOpen input directory layout physical)) :
    CheckpointHeldOpen.Reports input directory before retry published physical := by
  intro layout keeper tail descriptors
  obtain ⟨reported⟩ := observed layout keeper tail descriptors
  exact ⟨reported.toHeldOpen⟩

end Alvoki.Storage.DiskSession
