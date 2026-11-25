import Alvoki.Storage.Disk.HeldWalPayloadObservations
import Alvoki.Storage.Disk.ListedAlignedKeeperRepair

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

private abbrev OpenHandle := DescriptorInventory × DescriptorSlot × Nat

/-- The installer accepts the raw locked listing and the bounded reads
resolved under its captured root. The exact seal and keeper payload
equations follow from the typed open and read observations. -/
structure HeldWalInstallReads {directory : DiskDirectory} {before : LockedFileState FileImage}
    {history : List WAL.Write} (layout : CanonicalKeeperLayout before.image history)
    (calls : MarkedRetryChunkCalls (Cache OpenHandle) directory before) where
  inventory : CachedRetryReadInventory directory layout
  inventoryDescription : inventory.inventory.descriptor = calls.slot.description
  inventoryOwners : inventory.inventory.owners = before.owners.set (directory.file .lock) (some calls.slot.description)
  metadata : ∀ path, inventory.inventory.reports.lstat path = (calls.reads.stat path).map Prod.fst
  view : DirectoryReadNamespace
  root : DeviceInode
  wal : HeldWalPayloadReports directory layout calls.reads view root
  keeperProjection : calls.readKeeper calls.cache = readWalKeeperBytes calls.reads

namespace HeldWalInstallReads

variable {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout before.image history}
  {calls : MarkedRetryChunkCalls (Cache OpenHandle) directory before} {published : CheckpointPublication.Image}

def operations (observed : HeldWalInstallReads layout calls) :
    MarkedRetryChunkOperations (Cache OpenHandle) directory layout where
  toMarkedRetryChunkCalls := calls
  reported := observed.wal.toCachedReads observed.inventory observed.metadata
  inventoryDescription := observed.inventoryDescription
  inventoryOwners := observed.inventoryOwners
  metadata := observed.metadata
  keeperReads := observed.keeperProjection

/-- The authorization uses the very same keeper open as the canonical
bounded reader. Both identify the unique stat result and opened slot and
cursor of the same callbacks. -/
theorem keeperObserved (observed : HeldWalInstallReads layout calls)
    {readStart : DescriptorInventory}
    {held : HeldDirectoryMarkedRetryReports observed.operations published readStart}
    (authorization : ListedDirectoryAuthorization held) :
    authorization.keeper = observed.wal.keeper.observesFile := by
  generalize authorization.keeper = authorized
  generalize observed.wal.keeper.observesFile = selected
  cases authorized with
  | mk metadata object inventory slot stat regular extent opened live sameObject contents chunks available =>
    cases selected with
    | mk otherMetadata otherObject otherInventory otherSlot otherStat otherRegular otherExtent otherOpened
        otherLive otherSameObject otherContents otherChunks otherAvailable =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (stat.symm.trans otherStat))
      obtain ⟨rfl, rest⟩ := Prod.mk.inj (Except.ok.inj (opened.symm.trans otherOpened))
      obtain ⟨rfl, _⟩ := Prod.mk.inj rest
      rfl

/-- In aligned repair, the issuing slot of the derived bounded read is
the live keeper at both reached barriers. -/
theorem keeperAtAlignedBarriers (observed : HeldWalInstallReads layout calls)
    {held : HeldDirectoryMarkedRetryReports observed.operations published}
    {authorization : ListedDirectoryAuthorization held}
    (repair : ListedAlignedKeeperRepair authorization) :
    let keeper := observed.wal.keeper.observesFile
    keeper.slot ∈ (keeper.inventory.afterDrops repair.beforeAuthorization).slots ∧
      keeper.slot ∈ (keeper.inventory.afterDrops (repair.beforeAuthorization ++ repair.afterAuthorization)).slots := by
  dsimp only
  rw [← observed.keeperObserved authorization]
  have census := repair.barrierCensus
  exact ⟨census.1, census.2.2.2.1⟩

/-- Run the admitted installer on the same callbacks that yielded the
selected WAL bytes. The keeper issuing slot is shared by the payload read
and authorization, including the descriptor routed to an aligned finish. -/
theorem installs {input : FilePath} (observed : HeldWalInstallReads layout calls)
    {held : HeldDirectoryMarkedRetryReports observed.operations published}
    (namespaceMatches : held.lifetime.namespaceView = observed.view)
    (rootMatches : held.lifetime.root = observed.root)
    (authorization : ListedDirectoryAuthorization held)
    (metadata : HeldMarkedMetadata held) (authorized : authorization.outcome = .completed)
    (healthy : observed.operations.HealthyFinish)
    (admission : OpenAdmissionReports input directory calls.slot)
    (keeperValid : before.image.keeper.Valid layout.target.Accepts)
    (laterValid : before.image.later.Beyond layout.range.through)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      before.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    let ops := observed.operations
    let names := observed.inventory.inventory.names
    (∀ segment ∈ layout.sealed, renderWalSegmentName segment.first ∈ names) ∧
    renderWalSegmentName layout.keeper.first ∈ names ∧
    authorization.keeper = observed.wal.keeper.observesFile ∧
    CachedRetryInstalled (before := before) ops.reported calls.descriptors calls.slot calls.bindings
      published calls.liveRefs (ops.runWithAdmission admission) := by
  have atRoot : HeldWalPayloadReports directory layout calls.reads held.lifetime.namespaceView held.lifetime.root := by
    rw [namespaceMatches, rootMatches]
    exact observed.wal
  obtain ⟨seals, keeper⟩ := held.selectedWalListed atRoot
  exact ⟨seals, keeper, observed.keeperObserved authorization,
    authorization.installs metadata authorized healthy admission keeperValid laterValid following accepted ordered⟩

end HeldWalInstallReads
end Alvoki.Storage.DiskSession
