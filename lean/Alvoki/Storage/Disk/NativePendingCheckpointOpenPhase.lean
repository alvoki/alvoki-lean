import Alvoki.Storage.Disk.NativeOpenCheckpoint
import Alvoki.Storage.Disk.NativeOpenedPosition
import Alvoki.Storage.Disk.NativePendingCheckpoint

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting

variable {heap image : Type} {opened : NativeOpenedHandle heap} {state : NativeReadyState}
  {cut : CheckpointPowerCut state.session.directory state.writer}

private def phaseCall {files α : Type} (call : EStateM IO.Error heap α) : EStateM IO.Error (heap × files) α :=
  fun (phase, files) => match call phase with
    | .ok result reached => .ok result (reached, files)
    | .error cause reached => .error cause (reached, files)

private def fileCalls {files : Type} (call : EStateM IO.Error files Unit) : EStateM IO.Error (heap × files) Unit :=
  fun (phase, files) => match call files with
    | .ok result reached => .ok result (phase, reached)
    | .error cause reached => .error cause (phase, reached)

/-- Source preparation and poison setter followed by a returned prefix
of the checkpoint file callbacks. -/
def runCheckpointPrefixOnOpenPhase {files : Type} (opened : NativeOpenedHandle heap)
    (completed : Installed → List Step) (perform : Installed → ByteArray → Step → EStateM IO.Error files Unit) :
    EStateM IO.Error (heap × files) Unit :=
  withPreparedCheckpoint (do (← phaseCall (opened.get opened.phase)).installed) liftCheckpointExcept
    (fun next manifest => do
      phaseCall (opened.set opened.phase .poisoned)
      fileCalls ((completed next).forM (perform next manifest)))

theorem CheckpointPreflight.reachesOpenPrefix {files : Type}
    {phase : Phase Installed} {next : Installed} {manifest : ByteArray}
    (preflight : CheckpointPreflight phase (.ok (next, manifest))) (opened : NativeOpenedHandle heap)
    {completed : Installed → List Step} {perform : Installed → ByteArray → Step → EStateM IO.Error files Unit}
    {entry poisoned : heap} {before reached : files}
    (loaded : opened.get opened.phase entry = .ok phase entry)
    (written : opened.set opened.phase .poisoned entry = .ok () poisoned)
    (ran : ((completed next).forM (perform next manifest)) before = .ok () reached) :
    runCheckpointPrefixOnOpenPhase opened completed perform (entry, before) = .ok () (poisoned, reached) := by
  unfold runCheckpointPrefixOnOpenPhase
  rw [preflight.preparesFrom _ (by simp only [Bind.bind, EStateM.bind, phaseCall, loaded])]
  simp only [Bind.bind, EStateM.bind, phaseCall, fileCalls, written, ran]

/-- The public checkpoint's returned source prefix through manifest
rename, before the last directory barrier or ready setter. -/
noncomputable def NativeCheckpointFinalBarrier.beforeDirectoryOnOpenPhase
    (barrier : NativeCheckpointFinalBarrier (image := image) state cut) (opened : NativeOpenedHandle heap) :
    EStateM IO.Error (heap × (CensusDirectoryCache × image)) Unit :=
  runCheckpointPrefixOnOpenPhase opened (fun next => manifestDirectoryPrefix next.table.runs.length) barrier.perform

/-- Interpret the same source prefix and the issued grouped sync with
an outer interruption. Inner errors still denote ordinary returns. -/
noncomputable def NativeCheckpointDirectoryStop.onOpenPhase
    (stop : NativeCheckpointDirectoryStop (image := image) state cut) (opened : NativeOpenedHandle heap) :
    EStateM FilePath (heap × (CensusDirectoryCache × image)) (Except IO.Error Unit) := fun entry =>
  match stop.barrier.beforeDirectoryOnOpenPhase opened entry with
  | .error cause reached => .ok (.error cause) reached
  | .ok () (phase, files) =>
    match (SyncPathGroup.run stop.syncPath #[state.session.directory.path]).run files with
    | .ok result reached => .ok result (phase, reached)
    | .error path reached => .error path (phase, reached)

/-- The public checkpoint follows the original phase cell and the
reported returned file prefix. After that prefix the sole remaining
file step issues the same cached directory fsync and does not return. -/
theorem NativeOpenedPosition.stopsCheckpointOnOpenPhase (current : NativeOpenedPosition opened)
    {cut : CheckpointPowerCut current.current.ready.state.session.directory current.current.ready.state.writer}
    (stop : NativeCheckpointDirectoryStop (image := image) current.current.ready.state cut) :
    let state := current.current.ready.state
    let before := (current.reached, stop.barrier.entry.image)
    opened.table.UsesOpenCheckpointSchedule state.session.directory opened.files opened.phase ∧
    NativePendingCheckpoint current.current.ready stop ∧
    steps cut.checkpoint.prepared.table.runs.length = cut.completed ++ [.manifest .syncDirectory] ∧
    ∃ poisoned : heap,
      opened.get opened.phase current.reached = .ok state.session.phase current.reached ∧
      opened.set opened.phase .poisoned current.reached = .ok () poisoned ∧
      opened.contents poisoned opened.phase = some .poisoned ∧
      stop.barrier.beforeDirectoryOnOpenPhase opened before = .ok () (poisoned, stop.barrier.observed.renamed) ∧
      stop.onOpenPhase opened before = .error state.session.directory.path (poisoned, state.cache, stop.reached) := by
  intro state before
  have pending := current.current.ready.stopsDuringCheckpoint stop
  have valid := current.current.ready.readPrefix.refines.1
  have preflight : CheckpointPreflight state.session.phase (.ok (cut.checkpoint.prepared, cut.checkpoint.manifest)) := by
    rw [valid.phase]
    exact cut.preflight
  have loaded := opened.phaseEffects.reads current.reached opened.phase state.session.phase current.stored
  obtain ⟨poisoned, excluded, poison⟩ := opened.phaseEffects.writes current.reached opened.phase state.session.phase
    .poisoned current.stored
  have returnedPrefix : (cut.completed.forM (stop.barrier.perform cut.checkpoint.prepared cut.checkpoint.manifest))
      stop.barrier.entry.image = .ok () stop.barrier.observed.renamed := by
    have issued := pending.issued.atIssue
    simp only [runCheckpointActions, Bind.bind, EStateM.bind, modify, modifyGet, MonadStateOf.modifyGet,
      EStateM.modifyGet] at issued
    split at issued
    · next result reached ran =>
      have same := congrArg (fun file => file.2.image) (EStateM.Result.ok.inj issued).2
      cases result
      exact ran.trans (congrArg (EStateM.Result.ok ()) same)
    · contradiction
  have arrived : stop.barrier.beforeDirectoryOnOpenPhase opened before = .ok () (poisoned, stop.barrier.observed.renamed) := by
    have completed : manifestDirectoryPrefix cut.checkpoint.prepared.table.runs.length = cut.completed :=
      stop.barrier.completed.symm
    exact preflight.reachesOpenPrefix opened loaded excluded (by simpa only [completed] using returnedPrefix)
  refine ⟨current.uses.checkpoint, pending, ?_, poisoned, loaded, excluded, poison, arrived, ?_⟩
  · rw [stop.barrier.completed]
    exact manifestDirectoryPrefix_steps _
  · simp only [NativeCheckpointDirectoryStop.onOpenPhase, arrived, pending.stopped]
    rfl

end Alvoki.Storage.DiskSession
