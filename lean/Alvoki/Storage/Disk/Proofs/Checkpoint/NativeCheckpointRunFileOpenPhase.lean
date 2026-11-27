import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointRunFileStop
import Alvoki.Storage.Disk.Proofs.Native.Checkpoint.NativePendingCheckpointOpenPhase

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair

namespace NativeCheckpointRunFileStop

variable {image heap : Type} {state : NativeReadyState} {cut : CheckpointPowerCut state.session.directory state.writer}
  (stop : NativeCheckpointRunFileStop (image := image) state cut)

noncomputable def onOpenPhase (opened : NativeOpenedHandle heap) :
    EStateM FilePath (heap × (CensusDirectoryCache × image)) (Except IO.Error Unit) := fun entry =>
  match runCheckpointPrefixOnOpenPhase opened (fun _ => runSteps stop.effect.index ++ [.writeRun stop.effect.index])
      stop.effect.prior.perform entry with
  | .error cause reached => .ok (.error cause) reached
  | .ok () (phase, files) =>
    match stop.syncGroup files with
    | .ok result reached => .ok result (phase, reached)
    | .error path reached => .error path (phase, reached)

end NativeCheckpointRunFileStop

/-- The actual opened phase is poisoned before the original run prefix
and the issued fsync on the selected run. This cut never reaches the
later runs, the directory barrier or the ready phase setter. -/
theorem NativeOpenedPosition.stopsAtCheckpointRunFile {heap : Type} {opened : NativeOpenedHandle heap}
    (current : NativeOpenedPosition opened)
    {cut : CheckpointPowerCut current.current.ready.state.session.directory current.current.ready.state.writer}
    (stop : NativeCheckpointRunFileStop (image := image) current.current.ready.state cut) :
    let state := current.current.ready.state
    opened.table.UsesOpenCheckpointSchedule state.session.directory opened.files opened.phase ∧
    NativePendingCheckpointRunFile current.current.ready stop ∧
    ∃ poisoned, opened.contents poisoned opened.phase = some .poisoned ∧
      opened.get opened.phase current.reached = .ok state.session.phase current.reached ∧
      opened.set opened.phase .poisoned current.reached = .ok () poisoned ∧
      stop.onOpenPhase opened (current.reached, stop.effect.prior.entry.image) =
        .error stop.effect.path (poisoned, state.cache, stop.effect.after) := by
  intro state
  have valid := current.current.ready.readPrefix.refines.1
  have loaded := opened.phaseEffects.reads current.reached opened.phase state.session.phase current.stored
  obtain ⟨poisoned, written, stored⟩ := opened.phaseEffects.writes current.reached opened.phase state.session.phase
    .poisoned current.stored
  have available : CheckpointPreflight state.session.phase (.ok (cut.checkpoint.prepared, cut.checkpoint.manifest)) := by
    rw [valid.phase]
    exact cut.preflight
  have returned := stop.issue.runPrefix
  rw [stop.effect.completed] at returned
  have arrived : runCheckpointPrefixOnOpenPhase opened (fun _ => runSteps stop.effect.index ++ [.writeRun stop.effect.index])
      stop.effect.prior.perform (current.reached, stop.effect.prior.entry.image) = .ok () (poisoned, stop.issue.atIssue) :=
    available.reachesOpenPrefix opened loaded written returned
  refine ⟨current.uses.checkpoint, current.current.ready.stopsAtCheckpointRunFile stop, poisoned, stored, loaded, written, ?_⟩
  have stopped : stop.syncGroup stop.issue.atIssue = .error stop.effect.path (state.cache, stop.effect.after) := stop.stopsGroup
  simp only [NativeCheckpointRunFileStop.onOpenPhase, arrived, stopped]

end Alvoki.Storage.DiskSession
