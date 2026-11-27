import Alvoki.Storage.Proofs.Table.PackedTableCompaction
import Alvoki.Storage.Disk.Proofs.Append.SegmentedAppendTrace
import Alvoki.Storage.Disk.Proofs.Append.RetainedAppendReports
import Alvoki.Storage.Disk.Proofs.Recovery.SegmentedCheckpointStep
import Alvoki.Storage.Disk.Proofs.Write.SegmentedWriterEntry
import Alvoki.Storage.Disk.Proofs.Write.SegmentedWriterMaintenance

namespace Alvoki.Storage.DiskSession

open WalSegmentRepair

/-- A stretch in one owned writer session. The endpoint of each reported
operation supplies the exact installed table and files for the next one. -/
inductive SegmentedWriterTrace (directory : DiskDirectory) (descriptor : Nat) (initial : SegmentedWriterState) :
    List WAL.Write → Nat → SegmentedWriterState → Prop where
  | empty : SegmentedWriterTrace directory descriptor initial [] 0 initial
  | appends {writes checkpoints before after events}
      (prior : SegmentedWriterTrace directory descriptor initial writes checkpoints before)
      (acknowledged : SegmentedAppendTrace directory descriptor before events after) :
      SegmentedWriterTrace directory descriptor initial (writes ++ events) checkpoints after
  | checkpoint {writes checkpoints before after}
      (prior : SegmentedWriterTrace directory descriptor initial writes checkpoints before)
      (report : SegmentedCheckpointReport directory before) (observed : report.Valid)
      (installed : report.Installs after) : SegmentedWriterTrace directory descriptor initial writes (checkpoints + 1) after
  | table {writes checkpoints before table}
      (prior : SegmentedWriterTrace directory descriptor initial writes checkpoints before)
      (step : SegmentedTableStep before.installed.table table) :
      SegmentedWriterTrace directory descriptor initial writes checkpoints (before.withTable table)

private theorem flushForCheckpoint_runAt {before checkpoint : PackedTable} {index : Nat}
    {run : Compaction.CheckedRun}
    (flushed : (flushForCheckpoint before id : Except String PackedTable) = .ok checkpoint)
    (atIndex : before.runs[index]? = some run) :
    checkpoint.runs[index]? = some run := by
  unfold flushForCheckpoint at flushed
  split at flushed
  · exact Except.ok.inj flushed ▸ atIndex
  · change before.flush = .ok checkpoint at flushed
    obtain ⟨_, _, _, appended, runs, _⟩ := PackedTable.flush_spec flushed
    rw [runs]
    exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp atIndex).1).trans atIndex

/-- The normal checkpoint publishes the exact single-run retention result
at its original index, even if flushing appends a newer run. -/
theorem SegmentedCheckpointReport.Installs.afterRunRetention {directory descriptor}
    {before after : SegmentedWriterState} {table : PackedTable} {index : Nat}
    (retained : before.installed.table.retainRunVersions index = some table)
    (ready : before.RetainedReady directory descriptor)
    {attempt : SegmentedCheckpointReport directory (before.withTable table)}
    (observed : attempt.Valid) (endpoint : attempt.Installs after) :
    after.RetainedReady directory descriptor ∧ after.history = before.history ∧
    ∃ source output : Compaction.CheckedRun, before.installed.table.runs[index]? = some source ∧
      output.history = source.history.retain before.installed.table.pins.floor ∧
      after.published.durable (SegmentedCheckpointReport.generation before) index = some output.run.bytes := by
  obtain ⟨_, _, _, older, source, output, newer, length, original, updated, _, history⟩ :=
    PackedTable.retainRunVersions_spec retained
  have sourceAt : before.installed.table.runs[index]? = some source := by
    rw [original, List.getElem?_append_right (by omega), ← length, Nat.sub_self, List.getElem?_cons_zero]
  have outputAt : table.runs[index]? = some output := by
    rw [updated, List.getElem?_append_right (by omega), ← length, Nat.sub_self, List.getElem?_cons_zero]
  have readyAfterRetention := (SegmentedTableStep.retainRunVersions retained).preservesRetained ready
  refine ⟨(endpoint.preservesRetained observed readyAfterRetention).1, endpoint.history, source, output,
    sourceAt, history, ?_⟩
  have written := endpoint.runs index
  change after.published.durable (SegmentedCheckpointReport.generation before) index =
    (attempt.table.runs.map (·.run.bytes))[index]? at written
  rw [written, List.getElem?_map, flushForCheckpoint_runAt observed.flushed outputAt]
  rfl
theorem SegmentedWriterTrace.preservesRetainedWithChain {directory descriptor initial writes checkpoints last}
    (trace : SegmentedWriterTrace directory descriptor initial writes checkpoints last)
    (ready : initial.RetainedReady directory descriptor) :
    last.RetainedReady directory descriptor ∧ last.history = initial.history ++ writes ∧ last.owners = initial.owners ∧
      last.installed.generation.toNat = initial.installed.generation.toNat + checkpoints ∧
      (WalSegment.Chain initial.history 0 initial.wal.segments →
        WalSegment.Chain last.history 0 last.wal.segments) := by
  induction trace with
  | empty => exact ⟨ready, by simp, rfl, by simp, id⟩
  | appends _ acknowledged ih =>
    obtain ⟨valid, history, owners, generation, chain⟩ := ih
    obtain ⟨next, exactHistory, held, gen, appendedChain⟩ := acknowledged.preservesRetainedWithChain valid
    exact ⟨next, by rw [exactHistory, history, List.append_assoc], held.trans owners,
      (congrArg UInt64.toNat gen).trans generation, appendedChain ∘ chain⟩
  | checkpoint _ report observed installed ih =>
    obtain ⟨valid, history, owners, generation, chain⟩ := ih
    refine ⟨(installed.preservesRetained observed valid).1, installed.history.trans history,
      installed.owners.trans owners, ?_, ?_⟩
    · rw [installed.installed]
      change (SegmentedCheckpointReport.generation _).toNat = _
      rw [SegmentedCheckpointReport.generation, UInt64.toNat_ofNat_of_lt' observed.generationFits, generation, Nat.add_assoc]
    · intro initialChain
      rw [installed.history, installed.wal]
      exact chain initialChain
  | table _ step ih =>
    obtain ⟨valid, history, owners, generation, chain⟩ := ih
    exact ⟨step.preservesRetained valid, history, owners, generation, chain⟩

theorem SegmentedWriterTrace.preservesReady {directory descriptor initial writes checkpoints last}
    (trace : SegmentedWriterTrace directory descriptor initial writes checkpoints last)
    (ready : initial.Ready directory descriptor) :
    last.Ready directory descriptor ∧ last.history = initial.history ++ writes ∧ last.owners = initial.owners ∧
      last.installed.generation.toNat = initial.installed.generation.toNat + checkpoints := by
  obtain ⟨next, history, owners, generation, chain⟩ := trace.preservesRetainedWithChain ready.toRetained
  exact ⟨next.withChain (chain ready.chain), history, owners, generation⟩

/-- A retained writer can keep serving one owned session after collection,
using the same actual reports and acknowledgment order. -/
theorem SegmentedWriterTrace.preservesRetained {directory descriptor initial writes checkpoints last}
    (trace : SegmentedWriterTrace directory descriptor initial writes checkpoints last)
    (ready : initial.RetainedReady directory descriptor) :
    last.RetainedReady directory descriptor ∧ last.history = initial.history ++ writes := by
  obtain ⟨next, history, _, _, _⟩ := trace.preservesRetainedWithChain ready
  exact ⟨next, history⟩

/-- Starting from the observed first open, the final live table represents
the exact submitted writes, with one generation advance per publication. -/
theorem SegmentedWriterTrace.fromBootstrap {directory descriptor writes checkpoints last}
    {after : LockedFileState WalSegmentRotation.State} (bootstrap : BootstrapReady after.image)
    (held : after.owners.Owns directory descriptor)
    (trace : SegmentedWriterTrace directory descriptor (bootstrap.writerState after.owners) writes checkpoints last) :
    last.Ready directory descriptor ∧ last.history = writes ∧ last.owners = after.owners ∧
      last.installed.generation.toNat = checkpoints := by
  obtain ⟨ready, history, owners, generation⟩ := trace.preservesReady (bootstrap.writerReady held)
  change last.history = [] ++ writes at history
  change last.installed.generation.toNat = 0 + checkpoints at generation
  exact ⟨ready, by simpa only [List.nil_append] using history, owners,
    by simpa only [Nat.zero_add] using generation⟩

end Alvoki.Storage.DiskSession
