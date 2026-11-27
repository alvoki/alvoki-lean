import Alvoki.Storage.Disk.Proofs.Native.Open.NativeOpenedPosition
import Alvoki.Storage.Disk.Proofs.Read.NativeOpenCheckpointReadTrace

namespace Alvoki.Storage.DiskSession

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- A successful public checkpoint continues at its actual returned
heap. The same callback interpretation supplies the durable checkpoint
and the unchanged client ledgers of the next ready position. -/
theorem NativeOpenedPosition.checkpointsFromReturn {image : Type}
    (start : NativeOpenedPosition opened)
    (calls : CheckpointPrimitiveCalls CheckpointOpenHandle image) (atEntry : image)
    {attempt : SegmentedCheckpointReport start.current.ready.state.session.directory start.current.ready.state.writer}
    {reports : CheckpointCompletionReports (CensusDirectoryCache × image) attempt}
    (observed : NativeReadyCheckpoint start.current.ready.state reports)
    (sameCalls : observed.primitives = calls)
    (sameEntry : (reports.observed.atRun 0).2 = atEntry)
    {reached : heap} {after : CensusDirectoryCache × image}
    (returned : runCheckpointOnOpenPhase (calls.cached.perform start.current.ready.state.session.directory)
      opened.phase opened.get opened.set (start.reached, start.current.ready.state.cache, atEntry) =
        .ok () (reached, after)) :
    opened.table.UsesOpenCheckpointSchedule start.current.ready.state.session.directory opened.files opened.phase ∧
    ∃ (writer : SegmentedWriterState) (next : NativeOpenedPosition opened),
      observed.Completed writer ∧ next.reached = reached ∧ after = reports.observed.completed ∧
      next.current.ready.state = observed.next writer ∧ NativeExecutionStep start.current .checkpoint next.current ∧
      next.current.history = start.current.history ∧ next.current.submissions = start.current.submissions ∧
      next.current.ready.reads = start.current.ready.reads ∧ next.pins = start.pins := by
  let state := start.current.ready.state
  let perform := observed.primitives.cached.perform state.session.directory
  let files : LockedFileState (CensusDirectoryCache × image) :=
    ⟨(state.cache, (reports.observed.atRun 0).2), state.files.owners⟩
  obtain ⟨source, classified⟩ :=
    opened.phaseEffects.classifiesCheckpointReturn start.uses start.stored observed.primitives files
  have raw : runCheckpointOnOpenPhase perform opened.phase opened.get opened.set (start.reached, files.image) =
      .ok () (reached, after) := by
    simpa only [perform, files, state, sameCalls, sameEntry] using returned
  obtain ⟨writer, completed, history, _⟩ := start.current.ready.readPrefix.checkpoints observed
  have normalized := completed.returned
  rw [completed.owners] at normalized
  change runCheckpointWithEffects perform (state.session.phase, files) =
    .ok () (.ready writer.installed, ⟨reports.observed.completed, state.files.owners⟩) at normalized
  change OpenCheckpointReturn perform state.session.phase files opened.phase opened.contents opened.set start.reached
    (runCheckpointOnOpenPhase perform opened.phase opened.get opened.set (start.reached, files.image))
    (runCheckpointWithEffects perform (state.session.phase, files)) at classified
  rw [raw, normalized] at classified
  cases classified with
  | published _ _ _ _ _ stored =>
    obtain ⟨next, step, sameState, reads⟩ := start.current.checkpointAtWriter observed writer completed history
    have directory : next.state.session.directory = opened.directory := by
      rw [sameState]
      exact start.directory
    let position : NativeOpenedPosition opened :=
      ⟨⟨start.current.history, start.current.submissions, next⟩, reached, directory, sameState.symm ▸ stored, start.pins⟩
    exact ⟨source, writer, position, completed, rfl, rfl, sameState, step, rfl, rfl, reads, rfl⟩

end Alvoki.Storage.DiskSession
