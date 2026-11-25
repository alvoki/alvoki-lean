import Alvoki.Storage.Disk.NativeOpenReadyTrace

namespace Alvoki.Storage.DiskSession

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- A checkpoint error that leaves the opened cell ready can only be
a preflight rejection. Its fixed callback result supplies the exact
diagnostic and unchanged position for the common execution edge. -/
theorem NativeOpenedPosition.rejectsCheckpointFromReturn {image : Type}
    (start : NativeOpenedPosition opened)
    (calls : CheckpointPrimitiveCalls CheckpointOpenHandle image) (atEntry : image)
    {cause : IO.Error} {reached : heap} {after : CensusDirectoryCache × image}
    (returned : runCheckpointOnOpenPhase (calls.cached.perform start.current.ready.state.session.directory)
      opened.phase opened.get opened.set (start.reached, start.current.ready.state.cache, atEntry) =
        .error cause (reached, after))
    (stillReady : opened.contents reached opened.phase = some start.current.ready.state.session.phase) :
    let state := start.current.ready.state
    let files : LockedFileState (CensusDirectoryCache × image) := ⟨(state.cache, atEntry), state.writer.owners⟩
    opened.table.UsesOpenCheckpointSchedule state.session.directory opened.files opened.phase ∧
    reached = start.reached ∧ after = files.image ∧
    CheckpointPreflight (.ready state.writer.installed) (.error cause) ∧
    runCheckpointWithEffects (calls.cached.perform state.session.directory) (state.session.phase, files) =
      .error cause (state.session.phase, files) ∧
    NativeExecutionStep start.current (.checkpointRejected cause) start.current := by
  intro state files
  have ready := start.current.ready.readPrefix.refines.1.phase
  obtain ⟨source, classified⟩ :=
    opened.phaseEffects.classifiesCheckpointReturn start.uses start.stored calls files
  rw [returned] at classified
  generalize runCheckpointWithEffects (calls.cached.perform state.session.directory) (state.session.phase, files) =
    normalized at classified ⊢
  cases classified with
  | rejected preflight =>
    have guard : CheckpointPreflight (.ready state.writer.installed) (.error cause) := ready ▸ preflight
    exact ⟨source, rfl, rfl, guard, rfl, .checkpointRejected _ _ (start.current.ready.rejectsCheckpoint guard)⟩
  | fileError _ _ poison _ =>
    rw [stillReady, ready] at poison
    cases poison

end Alvoki.Storage.DiskSession
