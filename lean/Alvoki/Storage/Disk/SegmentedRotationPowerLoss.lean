import Alvoki.Storage.Disk.SegmentedRotationRecovery
import Alvoki.Storage.Disk.WalSegmentRotationPowerLoss

namespace Alvoki.Storage.DiskSession

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
