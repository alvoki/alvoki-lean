import Alvoki.Storage.Disk.Checkpoint.SelectedRuns
import Alvoki.Storage.Disk.HeldWalInstallation
import Alvoki.Storage.Disk.WalSegmentCheckpointRetained

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair SyncHandleRouting

abbrev CheckpointOpenHandle := DescriptorInventory × DescriptorSlot × Nat

/-- The native-shaped reports for the checked open of the physical run
map selected after the crash. The WAL and metadata callbacks, directory
inventory, and authorization all describe this same open. -/
structure CheckpointHeldOpen (input : FilePath) (directory : DiskDirectory)
    {retry : LockedFileState FileImage} {history : List WAL.Write}
    (layout : CanonicalKeeperLayout retry.image history) (physical : Image) where
  calls : MarkedRetryChunkCalls (Cache CheckpointOpenHandle) directory retry
  wal : HeldWalInstallReads layout calls
  held : HeldDirectoryMarkedRetryReports wal.operations physical
  namespaceMatches : held.lifetime.namespaceView = wal.view
  rootMatches : held.lifetime.root = wal.root
  authorization : ListedDirectoryAuthorization held
  metadata : HeldMarkedMetadata held
  completed : authorization.outcome = .completed
  healthy : wal.operations.HealthyFinish
  admission : OpenAdmissionReports input directory calls.slot

def CheckpointHeldOpen.chunkReports {input directory history physical} {retry : LockedFileState FileImage}
    {layout : CanonicalKeeperLayout retry.image history}
    (observed : CheckpointHeldOpen input directory layout physical) :
    MarkedRetryChunkReports (Cache CheckpointOpenHandle) directory layout physical :=
  observed.held.toChunkReports (observed.authorization.settles observed.completed)
    observed.metadata.callbackMetadata observed.healthy

/-- A held open must report the keeper and ordered seals chosen from this
checkpoint survivor and its retained WAL. -/
abbrev CheckpointHeldOpen.Reports (input : FilePath) (directory : DiskDirectory) (before : SegmentedWriterState)
    (retry : LockedFileState FileImage) (published physical : Image) : Prop :=
  ∀ layout : CanonicalKeeperLayout retry.image before.history,
    layout.keeper = before.wal.active → layout.tail = ByteArray.empty →
    layout.sealed ++ [layout.keeper] = (published.segmentedCheckpointView before.wal).readDescriptors layout.range.watermark →
    Nonempty (CheckpointHeldOpen input directory layout physical)

end Alvoki.Storage.DiskSession
