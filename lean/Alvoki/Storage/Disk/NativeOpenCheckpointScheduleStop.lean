import Alvoki.Storage.Disk.Checkpoint.Run.ScheduleStop
import Alvoki.Storage.Disk.NativeOpenedPosition

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting

abbrev CheckpointWorld (heap : Type) := CensusDirectoryCache × heap

/-- Interpreted syncs either return an ordinary diagnostic or stop at
the issued operation and its reached state. Both phase and file actions
run on the same heap. -/
abbrev CheckpointFsync (heap : Type) := CheckpointOpenHandle → EStateM FilePath heap (Except IO.Error Unit)

abbrev CheckpointStopM (heap : Type) :=
  ExceptT IO.Error (EStateM (Step × FilePath) (CheckpointWorld heap))

private def phaseAction {heap α : Type} (action : EStateM IO.Error heap α) :
    CheckpointStopM heap α :=
  fun (cache, before) => match action before with
    | .ok result reached => .ok (.ok result) (cache, reached)
    | .error cause reached => .ok (.error cause) (cache, reached)

private theorem phaseAction_run {heap α : Type} (action : EStateM IO.Error heap α)
    (cache : CensusDirectoryCache) (heap : heap) : (phaseAction action).run (cache, heap) =
    match action heap with
    | .ok result reached => .ok (.ok result) (cache, reached)
    | .error cause reached => .ok (.error cause) (cache, reached) := rfl

private def validate {heap α : Type} (result : Except String α) : CheckpointStopM heap α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private theorem pure_run {heap α : Type} (value : α) (entry : CheckpointWorld heap) :
    (pure value : CheckpointStopM heap α).run entry = .ok (.ok value) entry := rfl

private theorem throw_run {heap α : Type} (cause : IO.Error) (entry : CheckpointWorld heap) :
    (throw cause : CheckpointStopM heap α).run entry = .ok (.error cause) entry := rfl

private theorem flushValidation {heap : Type} (table : PackedTable) :
    flushForCheckpoint (m := CheckpointStopM heap) table validate =
      validate (flushForCheckpoint (m := Except String) table id) := by
  by_cases empty : table.memoryIsEmpty = true <;> simp [flushForCheckpoint, empty, validate, pure, Except.pure]

private theorem preflightFromRead {heap : Type} {phase : Phase Installed}
    {result : Except IO.Error (Installed × ByteArray)} (preflight : CheckpointPreflight phase result)
    (load : CheckpointStopM heap Installed) {entry : CheckpointWorld heap}
    (loaded : load.run entry = (phase.installed : CheckpointStopM heap Installed).run entry)
    (publish : Installed → ByteArray → CheckpointStopM heap Unit) :
    (withPreparedCheckpoint load validate publish).run entry =
      match result with
      | .error cause => .ok (.error cause) entry
      | .ok (next, manifest) => (publish next manifest).run entry := by
  cases preflight <;>
    simp [withPreparedCheckpoint, Bind.bind, run_bind, Phase.installed, flushValidation, validate,
      pure_run, throw_run, -UInt64.ofNat_add, *]

abbrev CheckpointPrimitiveCalls.syncUntilStop {heap : Type}
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap) (directory : FilePath)
    (fsync : CheckpointFsync heap) :
    Array FilePath → ExceptT IO.Error (EStateM FilePath (CheckpointWorld heap)) Unit :=
  SyncPathGroup.run (checkpointSyncUntilStop directory primitives.openRead fsync)

noncomputable abbrev CheckpointPrimitiveCalls.checkpointStepUntilStop {heap : Type}
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap) (directory : DiskDirectory)
    (fsync : CheckpointFsync heap) (next : Installed) (manifest : ByteArray) :
    Step → ExceptT IO.Error (EStateM FilePath (CheckpointWorld heap)) Unit :=
  (primitives.cached.callbacks directory).performUntilSyncStop (primitives.syncUntilStop directory.path fsync)
    directory next manifest

/-- Interpret the published schedule with the opened table's phase
callbacks and the observed file primitives. An outer stop passes over
ordinary error handling and the final ready setter. -/
noncomputable def runCheckpointOnOpenPhaseUntilSyncStop {heap : Type}
    (opened : NativeOpenedHandle heap) (directory : DiskDirectory)
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap) (fsync : CheckpointFsync heap) :
    CheckpointStopM heap Unit :=
  withPreparedCheckpoint (do (← phaseAction (opened.get opened.phase)).installed) validate
    (fun next manifest => publishPrepared (fun phase => phaseAction (opened.set opened.phase phase))
      (CheckpointPublication.run next.table.runs.length
        (tagStop (primitives.checkpointStepUntilStop directory fsync next manifest)))
      (phaseAction (opened.set opened.phase (.ready next))))

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- The prefix and stopped callback are derived from one execution.
The issue records its heap and consumed cache before any reboot is chosen. -/
structure NativeCheckpointSourceStop (current : NativeOpenedPosition opened)
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap) (fsync : CheckpointFsync heap)
    (stage : Step) (reason : FilePath) (reached : CheckpointWorld heap) where
  next : Installed
  manifest : ByteArray
  poisoned : heap
  completed : List Step
  remaining : List Step
  atIssue : CheckpointWorld heap
  source : opened.table.UsesOpenCheckpointSchedule current.current.ready.state.session.directory opened.files opened.phase
  prepared : CheckpointPreflight current.current.ready.state.session.phase (.ok (next, manifest))
  setsPoisoned : opened.set opened.phase .poisoned current.reached = .ok () poisoned
  poisonStored : opened.contents poisoned opened.phase = some .poisoned
  ordered : steps next.table.runs.length = completed ++ stage :: remaining
  returnedPrefix : (completed.forM (primitives.checkpointStepUntilStop current.current.ready.state.session.directory
    fsync next manifest)).run (current.current.ready.state.cache, poisoned) = .ok (.ok ()) atIssue
  stoppedStep : (primitives.checkpointStepUntilStop current.current.ready.state.session.directory
    fsync next manifest stage).run atIssue = .error reason reached

/-- Derive the stop directly from the interpreted whole call starting at
the original opened position, using each successful prefix once. -/
theorem NativeOpenedPosition.checkpointStopsFromWhole (current : NativeOpenedPosition opened)
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap) (fsync : CheckpointFsync heap)
    {step : Step} {reason : FilePath} {reached : CheckpointWorld heap}
    (stopped : (runCheckpointOnOpenPhaseUntilSyncStop opened current.current.ready.state.session.directory
      primitives fsync).run (current.current.ready.state.cache, current.reached) = .error (step, reason) reached) :
    Nonempty (NativeCheckpointSourceStop current primitives fsync step reason reached) := by
  let state := current.current.ready.state
  let directory := state.session.directory
  have loaded := opened.phaseEffects.reads current.reached opened.phase state.session.phase current.stored
  obtain ⟨result, preflight⟩ := CheckpointPreflight.total state.session.phase
  let load : CheckpointStopM heap Installed := do
    (← phaseAction (opened.get opened.phase)).installed
  let perform next manifest := tagStop (primitives.checkpointStepUntilStop directory fsync next manifest)
  let publish next manifest := publishPrepared (fun value => phaseAction (opened.set opened.phase value))
    (CheckpointPublication.run next.table.runs.length (perform next manifest))
    (phaseAction (opened.set opened.phase (.ready next)))
  have readPhase : load.run (state.cache, current.reached) =
      (state.session.phase.installed : CheckpointStopM heap Installed).run (state.cache, current.reached) := by
    change (ExceptT.bind (phaseAction (opened.get opened.phase))
      (fun phase => phase.installed)).run (state.cache, current.reached) = _
    rw [run_bind, phaseAction_run, loaded]
  change (withPreparedCheckpoint load validate publish).run (state.cache, current.reached) = _ at stopped
  rw [preflightFromRead preflight load readPhase publish] at stopped
  cases result with
  | error cause => cases stopped
  | ok prepared =>
    obtain ⟨next, manifest⟩ := prepared
    obtain ⟨phase, wrote, stored⟩ := opened.phaseEffects.writes current.reached opened.phase state.session.phase
      .poisoned current.stored
    change (ExceptT.bind (phaseAction (opened.set opened.phase .poisoned)) (fun _ =>
      ExceptT.bind (CheckpointPublication.run next.table.runs.length (perform next manifest))
        (fun _ => phaseAction (opened.set opened.phase (.ready next))))).run (state.cache, current.reached) = _ at stopped
    rw [run_bind, phaseAction_run, wrote] at stopped
    simp only at stopped
    rw [run_bind] at stopped
    cases ran : (CheckpointPublication.run next.table.runs.length (perform next manifest)).run (state.cache, phase) with
    | error halt after =>
      simp only [ran] at stopped
      obtain ⟨rfl, rfl⟩ := EStateM.Result.error.inj stopped
      obtain ⟨done, remaining, atIssue, ordered, completedRun, issued⟩ := run_firstStop ran
      exact ⟨⟨next, manifest, phase, done, remaining, atIssue, current.uses.checkpoint, preflight, wrote,
        stored, ordered, completedRun, issued⟩⟩
    | ok returned after =>
      simp only [ran] at stopped
      cases returned with
      | error cause => cases stopped
      | ok value =>
        cases value
        obtain ⟨cache, files⟩ := after
        rw [phaseAction_run] at stopped
        cases installed : opened.set opened.phase (.ready next) files <;> rw [installed] at stopped <;> cases stopped

private theorem successfulCheckpointStepsFrame {value : Type}
    (perform : Step → ExceptT IO.Error (EStateM FilePath (CheckpointWorld heap)) Unit)
    (observe : heap → value) (completed : List Step)
    (frame : ∀ step ∈ completed, ∀ before after,
      (perform step).run before = .ok (.ok ()) after → observe after.2 = observe before.2)
    {before after : CheckpointWorld heap}
    (returned : (completed.forM perform).run before = .ok (.ok ()) after) :
    observe after.2 = observe before.2 := by
  induction completed generalizing before with
  | nil =>
    have same := (EStateM.Result.ok.inj returned).2
    exact congrArg (fun world : CheckpointWorld heap => observe world.2) same.symm
  | cons step remaining ih =>
    change (ExceptT.bind (perform step) (fun _ => remaining.forM perform)).run before = _ at returned
    rw [run_bind] at returned
    cases result : (perform step).run before with
    | error reason reached => rw [result] at returned; cases returned
    | ok value reached =>
      rw [result] at returned
      cases value with
      | error cause => cases returned
      | ok resultValue =>
        cases resultValue
        have kept := frame step List.mem_cons_self before reached result
        exact (ih (fun earlier member => frame earlier (List.mem_cons_of_mem step member)) returned).trans kept

/-- File effects frame the original phase cell. Propagate this local
contract across the derived prefix and the issued step. -/
theorem NativeCheckpointSourceStop.phaseAtStop {current : NativeOpenedPosition opened}
    {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap} {fsync : CheckpointFsync heap}
    {stage : Step} {reason : FilePath} {reached : CheckpointWorld heap}
    (stop : NativeCheckpointSourceStop current primitives fsync stage reason reached)
    (returnedKeeps : ∀ step ∈ stop.completed, ∀ before after,
      (primitives.checkpointStepUntilStop current.current.ready.state.session.directory
        fsync stop.next stop.manifest step).run before = .ok (.ok ()) after →
      opened.contents after.2 opened.phase = opened.contents before.2 opened.phase)
    (stoppedKeeps : opened.contents reached.2 opened.phase = opened.contents stop.atIssue.2 opened.phase) :
    opened.contents reached.2 opened.phase = some .poisoned := by
  have completed := successfulCheckpointStepsFrame _ (fun heap => opened.contents heap opened.phase)
    stop.completed returnedKeeps stop.returnedPrefix
  exact stoppedKeeps.trans (completed.trans stop.poisonStored)

/-- A singleton barrier can stop only after the cache resolves the
requested path to the descriptor that actually issues fsync. -/
theorem CheckpointPrimitiveCalls.issuedFsync {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap}
    {directory path reason : FilePath} {fsync : CheckpointFsync heap}
    {before reached : CheckpointWorld heap}
    (stopped : (primitives.syncUntilStop directory fsync #[path]).run before = .error reason reached) :
    ∃ handle atEffect,
      before.1.resolve directory path primitives.openRead before.2 = .ok handle (reached.1, atEffect) ∧
      fsync handle atEffect = .error reason reached.2 := by
  obtain ⟨cache, before⟩ := before
  cases resolved : cache.resolve directory path primitives.openRead before with
  | error cause atError =>
    have returned : checkpointSyncUntilStop directory primitives.openRead fsync path (cache, before) =
        .ok (.error cause) atError := by simp only [checkpointSyncUntilStop, resolved]
    simp [CheckpointPrimitiveCalls.syncUntilStop, SyncPathGroup.run, ← Array.forIn_toList, List.forIn_cons,
      List.forIn_nil, MonadExcept.tryCatch, MonadExceptOf.tryCatch, tryCatchThe, ExceptT.tryCatch, Bind.bind,
      ExceptT.bind, ExceptT.run, ExceptT.mk, EStateM.bind, StateT.pure, Pure.pure, ExceptT.pure,
      ExceptT.bindCont, MonadExceptOf.throw, throw, throwThe, EStateM.pure, returned] at stopped
  | ok handle selected =>
    obtain ⟨selectedCache, atEffect⟩ := selected
    cases synced : fsync handle atEffect with
    | error stoppedReason after =>
      have issued : checkpointSyncUntilStop directory primitives.openRead fsync path (cache, before) =
          .error stoppedReason (selectedCache, after) := by simp only [checkpointSyncUntilStop, resolved, synced]
      have group : (primitives.syncUntilStop directory fsync #[path]).run (cache, before) =
          .error stoppedReason (selectedCache, after) := by
        simp [CheckpointPrimitiveCalls.syncUntilStop, SyncPathGroup.run, ← Array.forIn_toList, List.forIn_cons,
          List.forIn_nil, MonadExcept.tryCatch, MonadExceptOf.tryCatch, tryCatchThe, ExceptT.tryCatch, Bind.bind,
          ExceptT.bind, ExceptT.run, ExceptT.mk, EStateM.bind, StateT.pure, Pure.pure, ExceptT.pure, issued]
      have same := EStateM.Result.error.inj (stopped.symm.trans group)
      obtain ⟨rfl, rfl⟩ := same
      exact ⟨handle, atEffect, rfl, synced⟩
    | ok result after =>
      have returned : checkpointSyncUntilStop directory primitives.openRead fsync path (cache, before) =
          .ok result (selectedCache, after) := by simp only [checkpointSyncUntilStop, resolved, synced]
      cases result <;> simp [CheckpointPrimitiveCalls.syncUntilStop, SyncPathGroup.run, ← Array.forIn_toList,
        List.forIn_cons, List.forIn_nil, MonadExcept.tryCatch, MonadExceptOf.tryCatch, tryCatchThe, ExceptT.tryCatch,
        Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, EStateM.bind, StateT.pure, Pure.pure, ExceptT.pure,
        ExceptT.bindCont, MonadExceptOf.throw, throw, throwThe, EStateM.pure, returned] at stopped

variable {current : NativeOpenedPosition opened}
  {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap} {fsync : CheckpointFsync heap}
  {reason : FilePath} {reached : CheckpointWorld heap}

theorem NativeCheckpointSourceStop.runFileIssue {index : Nat}
    (stop : NativeCheckpointSourceStop current primitives fsync (.syncRun index) reason reached) :
    let directory := current.current.ready.state.session.directory
    let path := directory.file (.run stop.next.generation index)
    index < stop.next.table.runs.length ∧ stop.completed = runSteps index ++ [.writeRun index] ∧
    ∃ handle atEffect,
      stop.atIssue.1.resolve directory.path path primitives.openRead stop.atIssue.2 =
        .ok handle (reached.1, atEffect) ∧ fsync handle atEffect = .error reason reached.2 := by
  have stage := prefixBeforeRunSync stop.ordered
  exact ⟨stage.1, stage.2, primitives.issuedFsync stop.stoppedStep⟩

theorem NativeCheckpointSourceStop.runsDirectoryIssue
    (stop : NativeCheckpointSourceStop current primitives fsync .syncRunsDirectory reason reached) :
    let dir := current.current.ready.state.session.directory.path
    stop.completed = runSteps stop.next.table.runs.length ∧
    ∃ handle atEffect,
      stop.atIssue.1.resolve dir dir primitives.openRead stop.atIssue.2 =
        .ok handle (reached.1, atEffect) ∧ fsync handle atEffect = .error reason reached.2 := by
  exact ⟨prefixBeforeRunsDirectory stop.ordered, primitives.issuedFsync stop.stoppedStep⟩

end Alvoki.Storage.DiskSession
