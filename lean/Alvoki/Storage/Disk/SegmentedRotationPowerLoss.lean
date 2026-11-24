import Alvoki.Storage.Disk.SegmentedRotationRecovery
import Alvoki.Storage.Disk.WalSegmentRotationPowerLoss

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- The in-flight rotation cut, chosen filesystem survivors, and subsequent
bounded reopen attempts. The power-loss step itself releases the original
writer's lock and fixes which successor name the retries start from. -/
structure SegmentedRotationPowerLossReport (directory : DiskDirectory) (before : SegmentedWriterState)
    (descriptor : Nat) extends SegmentedRotationReopenReport directory before descriptor where
  cut : RotationInFlightCut directory before
  pair : DirectoryPublication.Bindings
  present : Bool
  selected : pair ∈ cut.image.metadata.crashImages
  survives : cut.image.successor.MaySurvive present
  attempts : RotationReopenFailures directory before.wal before.history (cut.released pair present) retry

namespace SegmentedRotationPowerLossReport

variable {directory : DiskDirectory} {before : SegmentedWriterState} {descriptor : Nat}

def run (report : SegmentedRotationPowerLossReport directory before descriptor) :
    EStateM.Result IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession :=
  report.toSegmentedRotationReopenReport.run

structure Installs (report : SegmentedRotationPowerLossReport directory before descriptor)
    (after : SegmentedWriterState) : Prop where
  initialLoss : RotationReopenFailures directory before.wal before.history
    ⟨report.cut.image, before.owners⟩ (report.cut.released report.pair report.present)
  reopened : SegmentedRotationReopenEndpoint directory descriptor before after report.run

/-- The final healthy bounded opener installs the original acknowledged
history and checkpoint with the keeper selected by the reached rotation cut. -/
theorem installs (report : SegmentedRotationPowerLossReport directory before descriptor)
    {oldDescriptor : Nat} (ready : before.Ready directory oldDescriptor) :
    ∃ after, report.Installs after ∧ after.Ready directory descriptor := by
  have origin : WalSegmentRotation.Trace before.wal (report.cut.released report.pair report.present).image :=
    .crash report.cut.trace report.pair report.selected report.survives
  obtain ⟨after, exactOpen, afterReady⟩ := report.toSegmentedRotationReopenReport.installs ready
    (ready.rotationInput report.cut.nonempty) origin report.attempts
  exact ⟨after, ⟨report.cut.startsRetry report.selected report.survives, exactOpen⟩, afterReady⟩

theorem installsRetained (report : SegmentedRotationPowerLossReport directory before descriptor)
    {oldDescriptor : Nat} (ready : before.RetainedReady directory oldDescriptor) :
    ∃ after, report.Installs after ∧ after.RetainedReady directory descriptor := by
  have origin : WalSegmentRotation.Trace before.wal (report.cut.released report.pair report.present).image :=
    .crash report.cut.trace report.pair report.selected report.survives
  obtain ⟨after, exactOpen, afterReady⟩ := report.toSegmentedRotationReopenReport.installsRetained ready
    (ready.rotationInput report.cut.nonempty) origin report.attempts
  exact ⟨after, ⟨report.cut.startsRetry report.selected report.survives, exactOpen⟩, afterReady⟩

/-- A healthy cached open after a rotation crash installs the actual
visible keeper. The directory barrier settles the same segment names and
bytes that the held inventory reported before repair. -/
theorem installsRetainedCached (report : SegmentedRotationPowerLossReport directory before descriptor)
    {oldDescriptor : Nat} (ready : before.RetainedReady directory oldDescriptor)
    (sizes : SizedCheckpointRunReports directory report.read.reports
      (report.retry.image.settledReopenImage before.wal).directory.active.manifest before.published.durable)
    (cached : CachedWalFileReports directory report.read.reports
      (report.retry.image.settleForReopen.visible before.wal) before.target.range.watermark ByteArray.empty) :
    ∃ after,
      report.Installs after ∧
      SegmentedRotationReopenEndpoint directory descriptor before after
        (runOpenWithInstallation directory descriptor report.nextRef (.ok true) report.unlock
          (report.read.reopenCachedWithState sizes cached report.removeFile report.write report.sync report.renameFile)
          report.retry) ∧
      after.RetainedReady directory descriptor ∧
      after.wal.segments = (report.retry.image.visible before.wal).segments ∧
      after.wal.active = (report.retry.image.visible before.wal).active := by
  have origin : WalSegmentRotation.Trace before.wal (report.cut.released report.pair report.present).image :=
    .crash report.cut.trace report.pair report.selected report.survives
  obtain ⟨after, installed, endpoint, next, segments, active⟩ :=
    report.toSegmentedRotationReopenReport.installsRetainedCached ready (ready.rotationInput report.cut.nonempty)
      origin report.attempts sizes cached
  exact ⟨after, ⟨report.cut.startsRetry report.selected report.survives, installed⟩, endpoint, next, segments, active⟩

theorem Installs.preservesReady {report : SegmentedRotationPowerLossReport directory before descriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after)
    {oldDescriptor : Nat} (ready : before.Ready directory oldDescriptor) : after.Ready directory descriptor := by
  obtain ⟨_, next, nextReady⟩ := report.installs ready
  exact endpoint.reopened.unique next.reopened ▸ nextReady

theorem Installs.preservesRetainedReady {report : SegmentedRotationPowerLossReport directory before descriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after)
    {oldDescriptor : Nat} (ready : before.RetainedReady directory oldDescriptor) :
    after.RetainedReady directory descriptor := by
  obtain ⟨_, next, nextReady⟩ := report.installsRetained ready
  exact endpoint.reopened.unique next.reopened ▸ nextReady

theorem Installs.history {report : SegmentedRotationPowerLossReport directory before descriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after) : after.history = before.history :=
  endpoint.reopened.history

end SegmentedRotationPowerLossReport

end Alvoki.Storage.DiskSession
