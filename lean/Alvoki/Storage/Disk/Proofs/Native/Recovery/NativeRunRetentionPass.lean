import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointRunCollection
import Alvoki.Storage.Proofs.Table.RunRetentionPass

namespace Alvoki.Storage.DiskSession

open Compaction.Model (retentionRowBound)

/-- Interpret a caller's finite sequence of existing native retention
calls, in increasing index order. Each call receives the preceding
returned session and the result records every acceptance response. -/
def runNativeRetention (start count : Nat) : EStateM IO.Error SegmentedSession (List Bool) :=
  (List.range' start count).mapM (fun index => (RunMaintenance.retainRunVersions index).run)

private theorem withCurrentTable (state : NativeReadyState) (ready : state.Valid) :
    state.withTable state.writer.installed.table = state := by
  cases state with
  | mk session writer cache census owner directorySlot =>
    cases session
    cases writer
    simp [NativeReadyState.withTable, SegmentedWriterState.withTable] at ready ⊢
    exact ready.phase.symm

private theorem withTableAgain (state : NativeReadyState) (first second : PackedTable) :
    (state.withTable first).withTable second = state.withTable second := rfl

variable {history : List WAL.Write} {log : List DatabaseSubmissions}

/-- A native retention transcript keeps the initial recovered session
anchor and read ledger. Its endpoint changes only the installed table. -/
structure NativeRunRetentionPass (current next : NativeReadPosition history log) (start count : Nat)
    (table : PackedTable) : Prop where
  returned : runNativeRetention start count current.state.session = .ok (List.replicate count true) next.state.session
  reached : next.state = current.state.withTable table
  opened : next.opened = current.opened
  initial : next.initial = current.initial
  reads : next.reads = current.reads

/-- Every step of the pure checked schedule is executed by the native
ready maintenance transition. No effectful file callback is involved. -/
theorem NativeReadPosition.runsRetentionSteps (current : NativeReadPosition history log)
    {before after : PackedTable} {start count : Nat}
    (steps : PackedTable.RunRetentionSteps start count before after)
    (atTable : current.state.writer.installed.table = before) :
    ∃ next, NativeRunRetentionPass current next start count after := by
  induction steps generalizing current with
  | done index table =>
    refine ⟨current, rfl, ?_, rfl, rfl, rfl⟩
    rw [← atTable]
    exact (withCurrentTable current.state current.readPrefix.refines.1).symm
  | @next index count before reached after retained rest ih =>
    obtain ⟨result, following, step⟩ := current.rewritesRun (.retainRunVersions index)
    have returned := step.reached
    change (match current.state.writer.installed.table.retainRunVersions index with
      | none => result = false ∧ following = current
      | some table => result = true ∧ following.state = current.state.withTable table) at returned
    rw [atTable, retained] at returned
    obtain ⟨rfl, followingState⟩ := returned
    obtain ⟨next, pass⟩ := ih following (by rw [followingState]; rfl)
    refine ⟨next, ?_, ?_, pass.opened.trans step.opened, pass.initial.trans step.initial, pass.reads.trans step.reads⟩
    · have tail := pass.returned
      unfold runNativeRetention at tail
      simp only [runNativeRetention, List.range'_succ, List.mapM_cons, Bind.bind, EStateM.bind,
        step.returned, tail, List.replicate_succ, Pure.pure, EStateM.pure]
    · rw [pass.reached, followingState, withTableAgain]

/-- Run all current indices once. The exact native response list accepts
every index, and every callback uses the original retention floor.
The bound concerns only the resulting packed payload. -/
theorem NativeReadPosition.completesRetentionPass (current : NativeReadPosition history log) :
    let before := current.state.writer.installed.table
    ∃ next : NativeReadPosition history log, ∃ table : PackedTable,
      NativeRunRetentionPass current next 0 before.runs.length table ∧
      PackedTable.RunRetentionSteps 0 before.runs.length before table ∧
      before.runs.mapM (·.retainVersions before.pins.floor) = .ok table.runs ∧
      table.runs.length = before.runs.length ∧
      (table.runs.map (·.run.bytes.size)).sum ≤
        16 * before.runs.length + 32 * (before.runs.map (fun run => retentionRowBound run.history.rows before.pins.floor)).sum ∧
      table.memory = before.memory ∧ table.committed = before.committed ∧ table.pins = before.pins ∧
      (∀ snapshot, before.pins.floor ≤ snapshot → ∀ key start stop,
        table.lookupAt key snapshot = before.lookupAt key snapshot ∧
        table.rangeAt start stop snapshot = before.rangeAt start stop snapshot) ∧
      InstalledClientReplay log current.reads history next.state.writer.installed next.state.session := by
  intro before
  obtain ⟨table, steps, written, length, bytes⟩ := before.completeRunRetention
  obtain ⟨next, pass⟩ := current.runsRetentionSteps steps rfl
  obtain ⟨memory, clock, pins, reads⟩ := steps.preservesReads
  exact ⟨next, table, pass, steps, written, length, bytes, memory, clock, pins, reads,
    pass.reads ▸ next.readPrefix.guardedReplay⟩

variable {current reached : NativeReadPosition history log} {table : PackedTable} {image : Type}
  {attempt : SegmentedCheckpointReport reached.state.session.directory reached.state.writer}
  {reports : CheckpointCompletionReports (CensusDirectoryCache × image) attempt}

/-- A complete retention pass publishes the exact ordered bounded
payload, assuming no pending rows need to be flushed into a new run.
The native checkpoint binds the payload at its completed run image. -/
structure NativeRetainedRunPublication (current : NativeReadPosition history log) (table : PackedTable)
    (checkpoint : NativeReadyCheckpoint reached.state reports) (writer : SegmentedWriterState) : Prop where
  completed : checkpoint.Completed writer
  sameHistory : writer.history = history
  prepared : attempt.table = table
  manifest : writer.published.manifest = .settled (some attempt.manifest)
  durable : ∀ index, writer.published.durable attempt.prepared.generation index =
    (table.runs.map (·.run.bytes))[index]?
  observedBytes : ∀ index < table.runs.length,
    (reports.runs reports.observed.completed).guaranteed attempt.prepared.generation index =
      (table.runs.map (·.run.bytes))[index]?
  bound : (table.runs.map (·.run.bytes.size)).sum ≤
    16 * current.state.writer.installed.table.runs.length +
      32 * (current.state.writer.installed.table.runs.map (fun run =>
        retentionRowBound run.history.rows current.state.writer.installed.table.pins.floor)).sum

/-- The same native checkpoint run publishes the table reached by the
whole native retention sequence and supplies its next ready position. -/
theorem NativeRunRetentionPass.checkpoints
    (pass : NativeRunRetentionPass current reached 0 current.state.writer.installed.table.runs.length table)
    (steps : PackedTable.RunRetentionSteps 0 current.state.writer.installed.table.runs.length
      current.state.writer.installed.table table)
    (empty : table.memoryIsEmpty = true) (checkpoint : NativeReadyCheckpoint reached.state reports) :
    ∃ writer, NativeRetainedRunPublication current table checkpoint writer := by
  obtain ⟨valid, historyEq, _⟩ := reached.readPrefix.refines
  obtain ⟨writer, completed, installed⟩ := checkpoint.completesWithPublication valid
  have retainedTable : reached.state.writer.installed.table = table := by rw [pass.reached]; rfl
  have flushed := reports.preflight.preparedFacts.1
  change (flushForCheckpoint reached.state.writer.installed.table id : Except String PackedTable) = .ok attempt.table at flushed
  have prepared : attempt.table = table := by
    rw [retainedTable] at flushed
    simpa [flushForCheckpoint, empty, Pure.pure, Except.pure] using flushed.symm
  refine ⟨writer, completed, completed.sameHistory.trans historyEq, prepared, installed.settled, ?_, ?_, steps.fullByteSize_le⟩
  · intro index
    have written := installed.runs index
    change writer.published.durable attempt.prepared.generation index = (attempt.table.runs.map (·.run.bytes))[index]? at written
    simpa only [prepared] using written
  · intro index within
    have selected := completed.runs index (prepared.symm ▸ within)
    rw [completed.installed] at selected
    change _ = (attempt.table.runs.map (·.run.bytes))[index]? at selected
    simpa only [prepared] using selected

/-- With the optional checked run collector, the entire selected bounded
payload survives in the returned writer. The same read ledger continues
at that writer, while the prescribed older unheld names are durably gone. -/
theorem NativeRetainedRunPublication.collects
    {checkpoint : NativeReadyCheckpoint reached.state reports} {writer : SegmentedWriterState} {held : List UInt64}
    (published : NativeRetainedRunPublication current table checkpoint writer)
    (seen : CheckpointRunCollectionReports checkpoint writer held) :
    ∃ next, NativeObsoleteRunCollectionStep
      (current.afterCheckpoint checkpoint published.completed published.sameHistory) seen.collector next ∧
      (∀ index < table.runs.length, next.state.writer.published.durable attempt.prepared.generation index =
        (table.runs.map (·.run.bytes))[index]?) ∧
      (∀ generation index, generation < writer.installed.generation → generation ∉ held →
        seen.collector.atBarrier.syncDirectory.DurablyAbsent (generation, index)) ∧
      next.reads = current.reads ∧ InstalledClientReplay log current.reads history next.state.writer.installed next.state.session := by
  let checkpointed := current.afterCheckpoint checkpoint published.completed published.sameHistory
  obtain ⟨next, collected⟩ := checkpointed.collectsObsoleteRuns seen.collector
  obtain ⟨_, absent, kept, _, _⟩ := seen.completes published.completed
  refine ⟨next, collected, ?_, absent, collected.reads, collected.reads ▸ collected.replay⟩
  intro index within
  have length : index < (table.runs.map (·.run.bytes)).length := by simpa only [List.length_map] using within
  have atIndex := List.getElem?_eq_getElem length
  have selected := (published.observedBytes index within).trans atIndex
  have generation : writer.installed.generation ≤ attempt.prepared.generation := by
    rw [published.completed.installed]
    exact UInt64.le_refl _
  exact (congrFun (congrFun collected.durable attempt.prepared.generation) index).trans
    ((kept _ index _ (.inl generation) selected).trans atIndex.symm)

end Alvoki.Storage.DiskSession
