import Alvoki.Storage.Disk.WalSealedSpans
import Alvoki.Storage.Disk.WalSegmentCollectionNames
import Alvoki.Storage.Disk.SegmentedBatchDatabaseTrace

namespace Alvoki.Storage.DiskSession

open WalSegmentRepair WalSegmentRotation

/-- A mixed execution retains only positive sealed spans if its starting
writer had that property. Rotation alone adds a seal, and it seals a
nonempty keeper. Reopen follows the observed old seal list or the surviving
rotation instead of inferring shape from replay validity. -/
theorem SegmentedBatchDatabaseTrace.preservesPositiveSeals
    {directory initialDescriptor initial allowCollection log descriptor last}
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log descriptor last)
    (ready : initial.RetainedReady directory initialDescriptor) (positive : initial.wal.PositiveSeals) :
    last.wal.PositiveSeals := by
  induction trace with
  | start => exact positive
  | ordinary prior step ih => exact step.preservesPositiveSeals (prior.preservesRetained ready).1 ih
  | cleanReopenObserved _ _ endpoint ih =>
    rw [endpoint.writer.wal]
    exact ih
  | checkpointManifestStageError _ endpoint ih =>
    rw [endpoint.wal]
    exact ih
  | checkpointPowerLossObserved _ _ _ _ _ _ installed ih =>
    rw [installed.wal]
    exact ih
  | acknowledgedBatch _ _ _ ih => exact ih
  | batchError _ _ installed ih =>
    rw [installed.wal]
    exact ih
  | batchErrorAdmitted _ _ _ installed ih =>
    exact fun segment member => ih segment (installed.installation.sealedWal ▸ member)
  | batchPowerLoss _ _ _ _ installed ih
  | batchMarkerProcessExit _ _ _ _ installed ih
  | batchMarkerAdmitted _ _ _ installed ih
  | batchAppendPowerLoss _ _ _ installed ih
  | batchAppendProcessExit _ _ _ installed ih
  | batchAppendAdmitted _ _ installed ih =>
    exact fun segment member => ih segment (installed.sealedWal ▸ member)
  | collectRuns _ _ _ ih => exact ih
  | collectRunsPowerLoss _ _ _ installed ih =>
    exact fun segment member => ih segment (installed.sealedWal ▸ member)
  | rotationPowerLossAdmitted prior cut installed ih =>
    have current := (prior.preservesRetained ready).1
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, wal⟩ := installed.reopened
    rw [wal]
    change (WalSegmentRotation.State.visible _ _).PositiveSeals
    exact WalSegmentRotation.State.positiveSeals_visible _ ih (current.rotationInput cut.nonempty).nonempty

/-- Bootstrap has one empty active file and no sealed files. Every
subsequent mixed writer inherits the positive-span invariant. -/
theorem SegmentedBatchDatabaseTrace.positiveSeals_fromBootstrap
    {directory initialDescriptor allowCollection log descriptor last}
    {after : LockedFileState WalSegmentRotation.State} (bootstrap : BootstrapReady after.image)
    (held : after.owners.Owns directory initialDescriptor)
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor (bootstrap.writerState after.owners)
      allowCollection log descriptor last) :
    last.wal.PositiveSeals :=
  trace.preservesPositiveSeals (bootstrap.writerReady held).toRetained (bootstrap.positiveSeals_writer after.owners)

/-- A complete WAL pass after a checkpoint that reaches the keeper start
leaves exactly that keeper in the reached checked listing. Reachability
from bootstrap supplies positivity for every old seal. -/
theorem SegmentedBatchDatabaseTrace.singleWalNameAfterCollection
    {directory initialDescriptor allowCollection log descriptor before after}
    {boot : LockedFileState WalSegmentRotation.State} (bootstrap : BootstrapReady boot.image)
    (held : boot.owners.Owns directory initialDescriptor)
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor (bootstrap.writerState boot.owners)
      allowCollection log descriptor before)
    {report : SegmentedCollectionReport directory before} (installed : report.Installs after)
    (complete : report.offsets = before.wal.collectionOffsets)
    (covered : before.wal.active.first ≤ before.target.range.watermark) {tail : ByteArray}
    (observed : HealthyBoundedWalReports directory after.owners descriptor after.wal after.target.pair
      after.target.range.watermark after.published.durable tail) :
    (observed.entries.toList.map (·.fileName)).filterMap parseWalSegmentName = [before.wal.active.first] :=
  installed.singleObservedWalName (trace.preservesRetained (bootstrap.writerReady held).toRetained).1
    complete covered (trace.positiveSeals_fromBootstrap bootstrap held) observed

end Alvoki.Storage.DiskSession
