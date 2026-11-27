import Alvoki.Storage.Table.RunRetentionPass
import Alvoki.Storage.Disk.Proofs.Write.SegmentedWriterTrace

namespace Alvoki.Storage.DiskSession

open Compaction.Model (retentionRowBound)

/-- The full rewrite schedule is a sequence of existing table operations of
the same writer, with no new submissions or checkpoint publications. -/
theorem SegmentedWriterTrace.retainRuns {directory descriptor initial writes checkpoints before}
    (prior : SegmentedWriterTrace directory descriptor initial writes checkpoints before)
    {table : PackedTable} {index count}
    (pass : PackedTable.RunRetentionSteps index count before.installed.table table) :
    SegmentedWriterTrace directory descriptor initial writes checkpoints (before.withTable table) := by
  have extend {source result : PackedTable} {start count : Nat}
      (steps : PackedTable.RunRetentionSteps start count source result)
      (trace : SegmentedWriterTrace directory descriptor initial writes checkpoints (before.withTable source)) :
      SegmentedWriterTrace directory descriptor initial writes checkpoints (before.withTable result) := by
    induction steps with
    | done => exact trace
    | @next _ _ current reached _ retained _ ih =>
      exact ih (SegmentedWriterTrace.table (before := before.withTable current) (table := reached)
        trace (.retainRunVersions retained))
  exact extend pass prior

/-- With no pending rows to flush, a successful checkpoint after a full
run-retention pass publishes exactly the rewritten payload in order.
This counts the selected generation's run bytes. Earlier generations are
still subject to the separate collection policy. -/
theorem SegmentedCheckpointReport.Installs.retainedRunPayload {directory}
    {before after : SegmentedWriterState} {table : PackedTable}
    (pass : PackedTable.RunRetentionSteps 0 before.installed.table.runs.length before.installed.table table)
    (empty : table.memoryIsEmpty = true)
    {attempt : SegmentedCheckpointReport directory (before.withTable table)}
    (observed : attempt.Valid) (installed : attempt.Installs after) :
    let files := table.runs.map (·.run.bytes)
    after.published.manifest = .settled (some attempt.manifest) ∧
    (∀ index, after.published.durable (SegmentedCheckpointReport.generation before) index = files[index]?) ∧
    (files.map ByteArray.size).sum ≤
      16 * before.installed.table.runs.length +
        32 * (before.installed.table.runs.map (fun run =>
          retentionRowBound run.history.rows before.installed.table.pins.floor)).sum := by
  have checkpointTable : attempt.table = table := by
    have flushed := observed.flushed
    change (flushForCheckpoint table id : Except String PackedTable) = .ok attempt.table at flushed
    simpa [flushForCheckpoint, empty, Pure.pure, Except.pure] using flushed.symm
  refine ⟨installed.settled, fun index => ?_, ?_⟩
  · rw [show after.published.durable (SegmentedCheckpointReport.generation before) index =
      attempt.plan.files[index]? from installed.runs index]
    change (attempt.table.runs.map (·.run.bytes))[index]? = (table.runs.map (·.run.bytes))[index]?
    rw [checkpointTable]
  · simpa only [List.map_map, Function.comp_def] using pass.fullByteSize_le

end Alvoki.Storage.DiskSession
