import Alvoki.Storage.Disk.NativeOpenReadyTrace
import Alvoki.Storage.Disk.NativeExecutionPrefix

namespace Alvoki.Storage.DiskSession

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- Connect the actual returned checkpoint error to the same run file
sync observation. The terminal proof keeps the exact issued step,
temporary slot release, earlier checkpoint and read replay. -/
theorem NativeOpenedPosition.checkpointRunFsyncErrorFromReturn {image : Type}
    (start : NativeOpenedPosition opened)
    (calls : CheckpointPrimitiveCalls CheckpointOpenHandle image) (atEntry : image)
    {cut : CheckpointPowerCut start.current.ready.state.session.directory start.current.ready.state.writer}
    (reported : NativeCheckpointRunFileError (image := image) start.current.ready.state cut)
    (sameCalls : reported.prior.primitives = calls)
    (sameEntry : reported.prior.atRun 0 = atEntry)
    {cause : IO.Error} {reached : heap} {after : CensusDirectoryCache × image}
    (returned : runCheckpointOnOpenPhase (calls.cached.perform start.current.ready.state.session.directory)
      opened.phase opened.get opened.set (start.reached, start.current.ready.state.cache, atEntry) =
        .error cause (reached, after)) :
    let state := start.current.ready.state
    opened.table.UsesOpenCheckpointSchedule state.session.directory opened.files opened.phase ∧
    cause = reported.error ∧ after = (state.cache, reported.after) ∧
    opened.contents reached opened.phase = some .poisoned ∧
    (NativeExecutionEnd.checkpointRunFileError (current := start.current) reported).Reached := by
  intro state
  obtain ⟨source, classified⟩ := opened.phaseEffects.classifiesCheckpointReturn
    start.uses start.stored reported.prior.primitives reported.prior.entry
  have raw : runCheckpointOnOpenPhase (reported.prior.primitives.cached.perform start.current.ready.state.session.directory)
      opened.phase opened.get opened.set (start.reached, reported.prior.entry.image) =
      .error cause (reached, after) := by
    simpa only [NativeCheckpointRunObservations.entry, sameCalls, sameEntry] using returned
  have physical := start.current.ready.checkpointRunFileError reported
  have normalized := physical.returned
  change runCheckpointWithEffects (reported.prior.primitives.cached.perform start.current.ready.state.session.directory)
    (start.current.ready.state.session.phase, reported.prior.entry) = _ at normalized
  have ready := start.current.ready.readPrefix.refines.1.phase
  rw [raw, normalized, ready] at classified
  cases classified with
  | fileError _ _ poison _ =>
    exact ⟨source, rfl, rfl, poison, physical⟩

end Alvoki.Storage.DiskSession
