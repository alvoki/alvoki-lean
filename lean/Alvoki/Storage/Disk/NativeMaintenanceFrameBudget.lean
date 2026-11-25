import Alvoki.Storage.Disk.NativeExecutionTrace
import Alvoki.Storage.Disk.NamedMaintenanceBudget
import Alvoki.Storage.Disk.WalReplayWork

namespace Alvoki.Storage.DiskSession

open WAL (frameSize)
open WalSegmentRepair

/-- Count each submission represented in this native execution event.
Its ledger adds explicit acknowledged or uncertain batches. An uncertain
attempt consumes the budget even if recovery retains none of its frames. -/
def NativeExecutionEvent.submittedFrames (event : NativeExecutionEvent) : Nat :=
  (event.submissions.map fun entry => match entry with
    | .acknowledgedBatch batch | .uncertainBatch batch => batch.length
    | .ordinary _ => 0).sum

theorem NativeExecutionEvent.retainedFrames_le_submitted (event : NativeExecutionEvent)
    (whole : event.uncertainBatchWhole) :
    event.writes.length ≤ event.submittedFrames := by
  cases event <;> simp [writes, submittedFrames, submissions, uncertainBatchWhole] at whole ⊢
  all_goals rcases whole with retained | retained <;> simp [retained]

/-- Over a reached ready trace, the exact history grows by at most the
submitted frame count. The count does not use only acknowledged writes. -/
theorem NativeExecutionTrace.historyLength_le_submittedFrames
    (trace : NativeExecutionTrace start events last) :
    last.history.length ≤ start.history.length + (events.map NativeExecutionEvent.submittedFrames).sum := by
  induction trace with
  | empty => simp
  | @step events before event after prior next earlier =>
    have frames := event.retainedFrames_le_submitted next.uncertainBatchWhole
    rw [next.ledgers.1]
    simp only [List.length_append, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    omega

/-- The latest selected checkpoint must still cover the completed cut.
A caller can spend the frame budget on batches and schedule the next
maintenance pass before issuing another batch. -/
theorem NativeExecutionTrace.pendingFramesAfterMaintenance_le
    (trace : NativeExecutionTrace start events last)
    {before : SegmentedWriterState} (maintenance : MaintainedRecoveryBounds before start.ready.state.writer)
    (checkpointRetained : start.ready.state.writer.target.range.watermark ≤
      last.ready.state.writer.target.range.watermark)
    {budget : Nat} (scheduled : (events.map NativeExecutionEvent.submittedFrames).sum ≤ budget) :
    last.ready.state.writer.target.range.through - last.ready.state.writer.target.range.watermark ≤ budget := by
  have startClock : start.ready.state.writer.target.range.watermark = start.history.length :=
    maintenance.fullCheckpoint.trans (congrArg List.length start.ready.readPrefix.refines.2.1)
  have endClock : last.ready.state.writer.target.range.through = last.history.length :=
    last.ready.readPrefix.refines.1.retained.resumed.through.trans (congrArg List.length last.ready.readPrefix.refines.2.1)
  have length := trace.historyLength_le_submittedFrames
  omega

/-- The counted marked replay can attempt at most the scheduled number
of frames above that completed maintenance cut. The marker and checkpoint
clock come from the actual reached ready state. This is a replay bound
even when the selected file list fails a format check. -/
theorem NativeExecutionTrace.replayAttemptsAfterMaintenance_le
    (trace : NativeExecutionTrace start events last)
    {before : SegmentedWriterState} (maintenance : MaintainedRecoveryBounds before start.ready.state.writer)
    (checkpointRetained : start.ready.state.writer.target.range.watermark ≤
      last.ready.state.writer.target.range.watermark)
    {budget : Nat} (scheduled : (events.map NativeExecutionEvent.submittedFrames).sum ≤ budget) :
    ∃ bytes count, last.ready.state.files.image.directory.active.walBoundary = some bytes ∧
      WAL.Boundary.decode bytes = .ok count ∧
      ∀ files, (recoverMarkedWalSegmentsWithReplayWork
        (last.ready.state.writer.checkpoint.getD (.empty, 0)).1 count files).2 ≤ budget := by
  have pending := trace.pendingFramesAfterMaintenance_le maintenance checkpointRetained scheduled
  let state := last.ready.state
  let ready := last.ready.readPrefix.refines.1.retained
  obtain ⟨watermark, _, bytes, count, marker, decoded, absolute⟩ :=
    DirectoryPublication.Bindings.walRange_accounting state.writer.target.decoded
  have through : count.toNat / frameSize = state.writer.target.range.through := by
    rw [absolute, Nat.mul_div_cancel _ (by decide : 0 < frameSize)]
  have clock : (state.writer.checkpoint.getD (.empty, 0)).1.committed.toNat =
      state.writer.target.range.watermark :=
    Option.some.inj (ready.resumed.selected.watermark.symm.trans watermark)
  refine ⟨bytes, count, (congrArg DirectoryPublication.Bindings.walBoundary ready.resumed.ready.selected).trans marker,
    decoded, ?_⟩
  intro files
  have counted := (recoverMarkedWalSegmentsWithReplayWork_spec
    (state.writer.checkpoint.getD (.empty, 0)).1 count files).2.1
  exact Nat.le_trans (by simpa only [through, clock] using counted) pending

end Alvoki.Storage.DiskSession
