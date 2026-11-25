import Alvoki.Storage.Disk.CheckpointHeldOpenWork
import Alvoki.Storage.Disk.DiskCleanReopenAdmission
import Alvoki.Storage.Disk.NamedMaintenanceBudget

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair
open WAL (frameSize)
open Compaction.Model (retentionRowBound)

/-- The next held open observes the exact released image and the same
canonical lock object. The caller supplies stable files and healthy
primitive reports between the unlock and reacquisition. -/
abbrev CleanUnlockReports.HeldReopenObservations {directory descriptor} {before : SegmentedWriterState}
    (closed : CleanUnlockReports directory descriptor) (input : FilePath) : Prop :=
  ∀ layout : CanonicalKeeperLayout (SegmentedCleanReopenReport.released directory before).image before.history,
    layout.keeper = before.wal.active → layout.tail = ByteArray.empty →
    layout.sealed ++ [layout.keeper] = before.wal.readDescriptors layout.range.watermark →
    ∃ opened : CheckpointHeldOpen input directory layout before.published,
      opened.calls.bindings (directory.file .lock) = closed.bindings (directory.file .lock) ∧
      opened.calls.slot.description ≠ descriptor

/-- Preserve the actual held packet and its admission through the shared
clean-reopen proof. -/
theorem SegmentedWriterState.RetainedReady.closeWithHeldReports {directory descriptor input}
    {before : SegmentedWriterState} (ready : before.RetainedReady directory descriptor)
    (closed : CleanUnlockReports directory descriptor) (observed : closed.HeldReopenObservations (before := before) input) :
    ∃ (layout : CanonicalKeeperLayout (SegmentedCleanReopenReport.released directory before).image before.history)
      (opened : CheckpointHeldOpen input directory layout before.published) (after : SegmentedWriterState),
      AdmittedCleanReopen closed opened.chunkReports opened.admission after := by
  let witness {layout : CanonicalKeeperLayout (SegmentedCleanReopenReport.released directory before).image before.history}
      (report : MarkedRetryChunkReports (SyncHandleRouting.Cache CheckpointOpenHandle) directory layout before.published)
      (admission : OpenAdmissionReports input directory report.slot) : Prop :=
    ∃ opened : CheckpointHeldOpen input directory layout before.published,
      opened.chunkReports = report ∧ HEq opened.admission admission
  obtain ⟨layout, report, admission, after, endpoint, opened, sameReport, sameAdmission⟩ :=
    ready.closeWithAdmissionFromReports closed witness (by
      intro layout keeper tail seals
      obtain ⟨opened, lock, fresh⟩ := observed layout keeper tail seals
      exact ⟨opened.chunkReports, opened.admission, lock, fresh, opened, rfl, HEq.rfl⟩)
  subst report
  cases sameAdmission
  exact ⟨layout, opened, after, endpoint⟩

/-- Following a fully covering checkpoint, the admitted held open still
reads that checkpoint's selected runs and just the retained keeper.
The preparation counter uses exactly the packet that installed the
returned session. -/
theorem SegmentedWriterState.RetainedReady.closeWithHeldRequestBound {directory descriptor input}
    {before : SegmentedWriterState} (ready : before.RetainedReady directory descriptor)
    (full : before.target.range.watermark = before.history.length)
    (closed : CleanUnlockReports directory descriptor) (observed : closed.HeldReopenObservations (before := before) input) :
    ∃ (layout : CanonicalKeeperLayout (SegmentedCleanReopenReport.released directory before).image before.history)
      (opened : CheckpointHeldOpen input directory layout before.published) (after : SegmentedWriterState),
      AdmittedCleanReopen closed opened.chunkReports opened.admission after ∧
      opened.preparationRequests ≤ ((before.checkpoint.getD (.empty, 0)).1.runs.map (·.run.bytes.size)).sum +
        before.wal.active.bytes.size := by
  obtain ⟨layout, opened, after, endpoint⟩ := ready.closeWithHeldReports closed observed
  have range : layout.range = before.target.range :=
    congrArg Target.range (endpoint.writer.target.symm.trans endpoint.target)
  have layouts : layout.sealed ++ [layout.keeper] = [before.wal.active] := by
    have descriptors := endpoint.writer.selectedSeals
    change layout.sealed ++ [layout.keeper] = before.wal.readDescriptors layout.range.watermark at descriptors
    rw [range, full, WalSegmentImage.readDescriptors, ready.layout.activeEnd, ite_eq_right (Nat.lt_irrefl _)] at descriptors
    exact descriptors
  have noSeals : layout.sealed = [] := by
    exact List.length_eq_zero_iff.mp (by simpa using congrArg List.length layouts)
  have firstOfOne {history first keeper} (chain : WalSegment.Chain history first [keeper]) : first = keeper.first := by
    cases chain
    rfl
  have first : layout.first = layout.keeper.first :=
    firstOfOne (by simpa only [noSeals, List.nil_append] using layout.chain)
  have checkpoint : SelectedIntegrityCheckpoint before.published.durable
      (SegmentedCleanReopenReport.released directory before).image.directory.active.manifest before.checkpoint := by
    change SelectedIntegrityCheckpoint before.published.durable before.files.directory.active.manifest before.checkpoint
    rw [ready.resumed.ready.selected]
    exact ready.resumed.selected
  have bounded := opened.preparationRequests_le checkpoint (by simp [layouts]) (by
    change ∀ first ∈ before.files.later.visible, layout.range.through < first
    rw [ready.resumed.ready.pruned.1]
    simp)
  have keeperBytes : layout.keeper.bytes.size = (layout.range.through - layout.keeper.first) * frameSize :=
    layout.target.trimmedSize
  rw [first, ← keeperBytes, endpoint.writer.keeper] at bounded
  exact ⟨layout, opened, after, endpoint, bounded⟩

/-- The selected portion of a completed maintenance pass bounds the
primitive prefix requests of the following held admitted open. Its
session, acquired lock and returned file state belong to the same packet.
The caller supplies an active segment cap and the observed stable handoff. -/
theorem MaintainedRecoveryBounds.closeAndReopen {directory descriptor input}
    {before maintained : SegmentedWriterState} (bounds : MaintainedRecoveryBounds before maintained)
    (ready : maintained.RetainedReady directory descriptor) (closed : CleanUnlockReports directory descriptor)
    (observed : closed.HeldReopenObservations (before := maintained) input)
    {cap : Nat} (width : before.wal.active.last - before.wal.active.first ≤ cap) :
    ∃ (layout : CanonicalKeeperLayout (SegmentedCleanReopenReport.released directory maintained).image maintained.history)
      (opened : CheckpointHeldOpen input directory layout maintained.published)
      (after : SegmentedWriterState) (session : SegmentedSession) (final : LockedFileState FileImage),
      AdmittedCleanReopen closed opened.chunkReports opened.admission after ∧
      opened.wal.operations.runWithAdmission opened.admission = .ok session final ∧
      session.descriptor = opened.calls.slot.description ∧ session.phase = .ready after.installed ∧
      after.files = final.image ∧ after.owners = final.owners ∧
      opened.preparationRequests ≤ 16 * before.installed.table.runs.length +
        32 * (before.installed.table.runs.map (fun run =>
          retentionRowBound run.history.rows before.installed.table.pins.floor)).sum + cap * frameSize := by
  obtain ⟨layout, opened, after, endpoint, requests⟩ :=
    ready.closeWithHeldRequestBound bounds.fullCheckpoint closed observed
  obtain ⟨session, final, returned, _, descriptor, phase, _, files, owners⟩ := endpoint.reopenEffect
  have keeper : maintained.wal.active.bytes.size ≤ cap * frameSize := by
    rw [ready.layout.activeBytes, WAL.encode_size, List.length_drop, ← ready.layout.activeEnd, Nat.mul_comm, bounds.keeper]
    exact Nat.mul_le_mul_right _ width
  exact ⟨layout, opened, after, session, final, endpoint, returned, descriptor, phase, files, owners,
    Nat.le_trans requests (Nat.add_le_add bounds.selectedRuns keeper)⟩

end Alvoki.Storage.DiskSession
