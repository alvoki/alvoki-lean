import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointRunDirectoryCut
import Alvoki.Storage.Disk.Proofs.Native.Checkpoint.NativePendingCheckpointOpenPhase

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair

namespace NativeCheckpointRunDirectoryStop

variable {image heap : Type} {state : NativeReadyState} {cut : CheckpointPowerCut state.session.directory state.writer}
  (stop : NativeCheckpointRunDirectoryStop (image := image) state cut)

noncomputable def onOpenPhase (opened : NativeOpenedHandle heap) :
    EStateM FilePath (heap × (CensusDirectoryCache × image)) (Except IO.Error Unit) := fun entry =>
  match runCheckpointPrefixOnOpenPhase opened (fun next => runSteps next.table.runs.length) stop.runs.perform entry with
  | .error cause reached => .ok (.error cause) reached
  | .ok () (phase, files) =>
    match stop.syncGroup files with
    | .ok result reached => .ok result (phase, reached)
    | .error path reached => .error path (phase, reached)

/-- The original opened phase is read and poisoned before the actual
run callbacks and the cached directory issue. The unfinished checkpoint
keeps the earlier replay for the still-selected history. -/
theorem stopsOnOpenPhase {opened : NativeOpenedHandle heap} (current : NativeOpenedPosition opened)
    {cut : CheckpointPowerCut current.current.ready.state.session.directory current.current.ready.state.writer}
    (stop : NativeCheckpointRunDirectoryStop (image := image) current.current.ready.state cut) :
    let state := current.current.ready.state
    opened.table.UsesOpenCheckpointSchedule state.session.directory opened.files opened.phase ∧
    CheckpointIssue stop.runs.perform state.session.phase stop.runs.entry cut.checkpoint.prepared cut.checkpoint.manifest
      cut.completed .syncRunsDirectory (state.cache, stop.atIssue) ∧
    state.files.owners.Owns state.session.directory state.session.descriptor ∧
    PendingClientReplay current.current.submissions current.current.ready.reads current.current.history ∧
    (∀ read ∈ current.current.ready.reads, read.BoundedBy current.current.history.length) ∧
    ∃ poisoned, opened.contents poisoned opened.phase = some .poisoned ∧
      opened.get opened.phase current.reached = .ok state.session.phase current.reached ∧
      opened.set opened.phase .poisoned current.reached = .ok () poisoned ∧
      stop.onOpenPhase opened (current.reached, stop.runs.entry.image) =
        .error state.session.directory.path (poisoned, state.cache, stop.reached) := by
  intro state
  obtain ⟨valid, _, replay⟩ := current.current.ready.readPrefix.refines
  have loaded := opened.phaseEffects.reads current.reached opened.phase state.session.phase current.stored
  obtain ⟨poisoned, written, stored⟩ := opened.phaseEffects.writes current.reached opened.phase state.session.phase
    .poisoned current.stored
  have available : CheckpointPreflight state.session.phase (.ok (cut.checkpoint.prepared, cut.checkpoint.manifest)) := by
    rw [valid.phase]
    exact cut.preflight
  have arrived : runCheckpointPrefixOnOpenPhase opened (fun next => runSteps next.table.runs.length)
      stop.runs.perform (current.reached, stop.runs.entry.image) =
      .ok () (poisoned, state.cache, stop.atIssue) :=
    available.reachesOpenPrefix opened loaded written stop.runs.runPrefix
  refine ⟨current.uses.checkpoint, stop.issues valid, valid.retained.held, replay,
    current.current.ready.readPrefix.readsBounded, poisoned, stored, loaded, written, ?_⟩
  have stopped : stop.syncGroup (state.cache, stop.atIssue) =
      .error state.session.directory.path (state.cache, stop.reached) := stop.stopsGroup
  simp only [onOpenPhase, arrived, stopped]

end NativeCheckpointRunDirectoryStop
end Alvoki.Storage.DiskSession
