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
    (directory : DiskDirectory) (phase : IO.Ref (Phase Installed))
    (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit)
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap) (fsync : CheckpointFsync heap) :
    CheckpointStopM heap Unit :=
  withPreparedCheckpoint (do (← phaseAction (get phase)).installed) validate
    (fun next manifest => publishPrepared (fun nextPhase => phaseAction (set phase nextPhase))
      (CheckpointPublication.run next.table.runs.length
        (tagStop (primitives.checkpointStepUntilStop directory fsync next manifest)))
      (phaseAction (set phase (.ready next))))

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- The completed actions and issued step come from the same
checkpoint preparation, phase update and ordered publication prefix. -/
structure NativeCheckpointSourcePrefix (current : NativeOpenedPosition opened)
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap) (fsync : CheckpointFsync heap)
    (stage : Step) where
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

/-- A native stop records the actual callback interruption before any
reboot or continuation is chosen. -/
structure NativeCheckpointSourceStop (current : NativeOpenedPosition opened)
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap) (fsync : CheckpointFsync heap)
    (stage : Step) (reason : FilePath) (reached : CheckpointWorld heap)
    extends NativeCheckpointSourcePrefix current primitives fsync stage where
  stoppedStep : (primitives.checkpointStepUntilStop current.current.ready.state.session.directory
    fsync next manifest stage).run atIssue = .error reason reached
  stoppedCall : (runCheckpointOnOpenPhaseUntilSyncStop current.current.ready.state.session.directory
    opened.phase opened.get opened.set primitives fsync).run
      (current.current.ready.state.cache, current.reached) = .error (stage, reason) reached

/-- An ordinary return keeps the failing callback's diagnostic and the
exact heap it reached. As with an interruption, no later action is run. -/
structure NativeCheckpointSourceError (current : NativeOpenedPosition opened)
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap) (fsync : CheckpointFsync heap)
    (stage : Step) (cause : IO.Error) (reached : CheckpointWorld heap)
    extends NativeCheckpointSourcePrefix current primitives fsync stage where
  failedStep : (primitives.checkpointStepUntilStop current.current.ready.state.session.directory
    fsync next manifest stage).run atIssue = .ok (.error cause) reached
  failedCall : (runCheckpointOnOpenPhaseUntilSyncStop current.current.ready.state.session.directory
    opened.phase opened.get opened.set primitives fsync).run
      (current.current.ready.state.cache, current.reached) = .ok (.error cause) reached

/-- Expose the single publication run and final setter used by the
literal opened checkpoint after a successful preparation. -/
private theorem checkpointRunsFromPrepared (current : NativeOpenedPosition opened)
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap) (fsync : CheckpointFsync heap)
    {next : Installed} {manifest : ByteArray}
    (prepared : CheckpointPreflight current.current.ready.state.session.phase (.ok (next, manifest))) :
    let state := current.current.ready.state
    let perform := tagStop (primitives.checkpointStepUntilStop state.session.directory fsync next manifest)
    ∃ poisoned,
      opened.set opened.phase .poisoned current.reached = .ok () poisoned ∧
      opened.contents poisoned opened.phase = some .poisoned ∧
      (runCheckpointOnOpenPhaseUntilSyncStop state.session.directory opened.phase opened.get opened.set
        primitives fsync).run (state.cache, current.reached) =
      (ExceptT.bind (CheckpointPublication.run next.table.runs.length perform)
        (fun _ => phaseAction (opened.set opened.phase (.ready next)))).run (state.cache, poisoned) := by
  intro state perform
  have loaded := opened.phaseEffects.reads current.reached opened.phase state.session.phase current.stored
  obtain ⟨poisoned, wrote, stored⟩ := opened.phaseEffects.writes current.reached opened.phase state.session.phase
    .poisoned current.stored
  let load : CheckpointStopM heap Installed := do
    (← phaseAction (opened.get opened.phase)).installed
  let publish next manifest := publishPrepared (fun value => phaseAction (opened.set opened.phase value))
    (CheckpointPublication.run next.table.runs.length
      (tagStop (primitives.checkpointStepUntilStop state.session.directory fsync next manifest)))
    (phaseAction (opened.set opened.phase (.ready next)))
  have readPhase : load.run (state.cache, current.reached) =
      (state.session.phase.installed : CheckpointStopM heap Installed).run (state.cache, current.reached) := by
    change (ExceptT.bind (phaseAction (opened.get opened.phase))
      (fun phase => phase.installed)).run (state.cache, current.reached) = _
    rw [run_bind, phaseAction_run, loaded]
  refine ⟨poisoned, wrote, stored, ?_⟩
  change (withPreparedCheckpoint load validate publish).run (state.cache, current.reached) = _
  rw [preflightFromRead prepared load readPhase publish]
  change (ExceptT.bind (phaseAction (opened.set opened.phase .poisoned)) (fun _ =>
    ExceptT.bind (CheckpointPublication.run next.table.runs.length perform)
      (fun _ => phaseAction (opened.set opened.phase (.ready next))))).run (state.cache, current.reached) = _
  rw [run_bind, phaseAction_run, wrote]

/-- A rejected preflight never runs a publication or phase setter. -/
private theorem checkpointRejectsBeforePublication (current : NativeOpenedPosition opened)
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap) (fsync : CheckpointFsync heap)
    {cause : IO.Error} (rejected : CheckpointPreflight current.current.ready.state.session.phase (.error cause)) :
    let state := current.current.ready.state
    (runCheckpointOnOpenPhaseUntilSyncStop state.session.directory opened.phase opened.get opened.set
      primitives fsync).run (state.cache, current.reached) = .ok (.error cause) (state.cache, current.reached) := by
  intro state
  let load : CheckpointStopM heap Installed := do (← phaseAction (opened.get opened.phase)).installed
  have readPhase : load.run (state.cache, current.reached) =
      (state.session.phase.installed : CheckpointStopM heap Installed).run (state.cache, current.reached) := by
    change (ExceptT.bind (phaseAction (opened.get opened.phase))
      (fun phase => phase.installed)).run (state.cache, current.reached) = _
    rw [run_bind, phaseAction_run, opened.phaseEffects.reads current.reached opened.phase state.session.phase current.stored]
  apply preflightFromRead rejected load readPhase

/-- Derive the stop directly from the interpreted whole call starting at
the original opened position, using each successful prefix once. -/
theorem NativeOpenedPosition.checkpointStopsFromWhole (current : NativeOpenedPosition opened)
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap) (fsync : CheckpointFsync heap)
    {step : Step} {reason : FilePath} {reached : CheckpointWorld heap}
    (stopped : (runCheckpointOnOpenPhaseUntilSyncStop current.current.ready.state.session.directory
      opened.phase opened.get opened.set primitives fsync).run
        (current.current.ready.state.cache, current.reached) = .error (step, reason) reached) :
    Nonempty (NativeCheckpointSourceStop current primitives fsync step reason reached) := by
  have wholeCall := stopped
  obtain ⟨result, preflight⟩ := CheckpointPreflight.total current.current.ready.state.session.phase
  cases result with
  | error cause =>
    rw [checkpointRejectsBeforePublication current primitives fsync preflight] at stopped
    cases stopped
  | ok prepared =>
    obtain ⟨next, manifest⟩ := prepared
    obtain ⟨poisoned, wrote, stored, runs⟩ := checkpointRunsFromPrepared current primitives fsync preflight
    rw [runs, run_bind] at stopped
    cases ran : (CheckpointPublication.run next.table.runs.length
      (tagStop (primitives.checkpointStepUntilStop current.current.ready.state.session.directory
        fsync next manifest))).run (current.current.ready.state.cache, poisoned) with
    | error halt after =>
      rw [ran] at stopped
      obtain ⟨rfl, rfl⟩ := EStateM.Result.error.inj stopped
      obtain ⟨done, remaining, atIssue, ordered, completedRun, issued⟩ := run_firstStop ran
      exact ⟨⟨⟨next, manifest, poisoned, done, remaining, atIssue, current.uses.checkpoint, preflight, wrote,
        stored, ordered, completedRun⟩, issued, wholeCall⟩⟩
    | ok returned after =>
      rw [ran] at stopped
      cases returned with
      | error cause => cases stopped
      | ok value =>
        cases value
        obtain ⟨cache, files⟩ := after
        simp only at stopped
        rw [phaseAction_run] at stopped
        cases installed : opened.set opened.phase (.ready next) files <;> rw [installed] at stopped <;> cases stopped

/-- Invert an ordinary checkpoint error on the actual opened phase and
heap. A preflight rejection or a failed ready setter is distinct from
a reported error of the first unsuccessful publication callback. -/
theorem NativeOpenedPosition.checkpointErrorsFromWhole (current : NativeOpenedPosition opened)
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap) (fsync : CheckpointFsync heap)
    {cause : IO.Error} {reached : CheckpointWorld heap}
    (failed : (runCheckpointOnOpenPhaseUntilSyncStop current.current.ready.state.session.directory
      opened.phase opened.get opened.set primitives fsync).run
      (current.current.ready.state.cache, current.reached) = .ok (.error cause) reached) :
    let state := current.current.ready.state
    (CheckpointPreflight state.session.phase (.error cause) ∧ reached = (state.cache, current.reached)) ∨
    (∃ step, Nonempty (NativeCheckpointSourceError current primitives fsync step cause reached)) ∨
    (∃ (next : Installed) (manifest : ByteArray) (poisoned : heap) (beforeReady : CheckpointWorld heap),
      CheckpointPreflight state.session.phase (.ok (next, manifest)) ∧
      opened.set opened.phase .poisoned current.reached = .ok () poisoned ∧
      ((steps next.table.runs.length).forM (tagStop
        (primitives.checkpointStepUntilStop state.session.directory fsync next manifest))).run
        (state.cache, poisoned) = .ok (.ok ()) beforeReady ∧
      opened.set opened.phase (.ready next) beforeReady.2 = .error cause reached.2 ∧
      reached.1 = beforeReady.1) := by
  intro state
  have wholeCall := failed
  obtain ⟨result, preflight⟩ := CheckpointPreflight.total state.session.phase
  cases result with
  | error rejected =>
    rw [checkpointRejectsBeforePublication current primitives fsync preflight] at failed
    obtain ⟨same, reached⟩ := EStateM.Result.ok.inj failed
    cases same
    exact .inl ⟨preflight, reached.symm⟩
  | ok prepared =>
    obtain ⟨next, manifest⟩ := prepared
    obtain ⟨poisoned, wrote, stored, runs⟩ := checkpointRunsFromPrepared current primitives fsync preflight
    rw [runs, run_bind] at failed
    cases ran : (CheckpointPublication.run next.table.runs.length
      (tagStop (primitives.checkpointStepUntilStop state.session.directory fsync next manifest))).run
      (state.cache, poisoned) with
    | error halt after =>
      rw [ran] at failed
      cases failed
    | ok result after =>
      rw [ran] at failed
      cases result with
      | error diagnostic =>
        obtain ⟨same, heap⟩ := EStateM.Result.ok.inj failed
        cases same
        subst after
        obtain ⟨done, step, remaining, atIssue, ordered, completedRun, issued⟩ := run_firstReturnedError ran
        exact .inr (.inl ⟨step, ⟨⟨⟨next, manifest, poisoned, done, remaining, atIssue, current.uses.checkpoint,
          preflight, wrote, stored, ordered, completedRun⟩, issued, wholeCall⟩⟩⟩)
      | ok value =>
        cases value
        obtain ⟨cache, files⟩ := after
        simp only at failed
        rw [phaseAction_run] at failed
        cases installed : opened.set opened.phase (.ready next) files with
        | ok result after =>
          rw [installed] at failed
          cases failed
        | error diagnostic after =>
          rw [installed] at failed
          obtain ⟨same, world⟩ := EStateM.Result.ok.inj failed
          cases same
          have afterHeap := congrArg Prod.snd world
          exact .inr (.inr ⟨next, manifest, poisoned, (cache, files), preflight, wrote, ran,
            afterHeap ▸ installed, (congrArg Prod.fst world).symm⟩)

/-- Use the same source-stop witness when the call starts on the
literal opened table's directory and cache. The three equalities
identify its actual entry with the current ready position. -/
theorem NativeOpenedPosition.checkpointStopsAtReachedCache (current : NativeOpenedPosition opened)
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap) (fsync : CheckpointFsync heap)
    {directory : DiskDirectory} {cache : CensusDirectoryCache} {entry : heap}
    {step : Step} {reason : FilePath} {reached : CheckpointWorld heap}
    (sameDirectory : current.current.ready.state.session.directory = directory)
    (sameCache : cache = current.current.ready.state.cache)
    (sameHeap : current.reached = entry)
    (stopped : (runCheckpointOnOpenPhaseUntilSyncStop directory
      opened.phase opened.get opened.set primitives fsync).run (cache, entry) = .error (step, reason) reached) :
    Nonempty (NativeCheckpointSourceStop current primitives fsync step reason reached) :=
  current.checkpointStopsFromWhole primitives fsync (by
    rwa [sameDirectory, sameHeap, ← sameCache])

theorem successfulCheckpointStepsPreserve {value : Type}
    (perform : Step → ExceptT IO.Error (EStateM FilePath (CheckpointWorld heap)) Unit)
    (observe : CheckpointWorld heap → value) (related : value → value → Prop)
    (refl : ∀ item, related item item)
    (trans : ∀ {first middle last}, related first middle → related middle last → related first last)
    (completed : List Step)
    (frame : ∀ step ∈ completed, ∀ before after,
      (perform step).run before = .ok (.ok ()) after → related (observe before) (observe after))
    {before after : CheckpointWorld heap}
    (returned : (completed.forM perform).run before = .ok (.ok ()) after) :
    related (observe before) (observe after) := by
  induction completed generalizing before with
  | nil =>
    have same := (EStateM.Result.ok.inj returned).2
    rw [same]
    exact refl _
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
        exact trans kept (ih (fun earlier member => frame earlier (List.mem_cons_of_mem step member)) returned)

private theorem successfulCheckpointStepsFrame {value : Type}
    (perform : Step → ExceptT IO.Error (EStateM FilePath (CheckpointWorld heap)) Unit)
    (observe : CheckpointWorld heap → value) (completed : List Step)
    (frame : ∀ step ∈ completed, ∀ before after,
      (perform step).run before = .ok (.ok ()) after → observe after = observe before)
    {before after : CheckpointWorld heap}
    (returned : (completed.forM perform).run before = .ok (.ok ()) after) :
    observe after = observe before :=
  successfulCheckpointStepsPreserve perform observe (fun first last => last = first)
    (fun _ => rfl) (fun earlier later => later.trans earlier) completed frame returned

/-- Each actually returned file callback preserves the original phase cell. -/
abbrev NativeCheckpointSourcePrefix.KeepsPhase {current : NativeOpenedPosition opened}
    {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap} {fsync : CheckpointFsync heap}
    {stage : Step} (prior : NativeCheckpointSourcePrefix current primitives fsync stage) : Prop :=
  ∀ step ∈ prior.completed, ∀ before after,
    (primitives.checkpointStepUntilStop current.current.ready.state.session.directory
      fsync prior.next prior.manifest step).run before = .ok (.ok ()) after →
    opened.contents after.2 opened.phase = opened.contents before.2 opened.phase

theorem NativeCheckpointSourcePrefix.phaseAtIssue {current : NativeOpenedPosition opened}
    {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap} {fsync : CheckpointFsync heap}
    {stage : Step} (prior : NativeCheckpointSourcePrefix current primitives fsync stage)
    (returnedKeeps : prior.KeepsPhase) : opened.contents prior.atIssue.2 opened.phase = some .poisoned := by
  have completed := successfulCheckpointStepsFrame _ (fun world => opened.contents world.2 opened.phase)
    prior.completed returnedKeeps prior.returnedPrefix
  exact completed.trans prior.poisonStored

/-- Carry the poisoned cell through the successful prefix and the issued stop. -/
theorem NativeCheckpointSourceStop.phaseAtStop {current : NativeOpenedPosition opened}
    {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap} {fsync : CheckpointFsync heap}
    {stage : Step} {reason : FilePath} {reached : CheckpointWorld heap}
    (stop : NativeCheckpointSourceStop current primitives fsync stage reason reached)
    (returnedKeeps : stop.toNativeCheckpointSourcePrefix.KeepsPhase)
    (stoppedKeeps : opened.contents reached.2 opened.phase = opened.contents stop.atIssue.2 opened.phase) :
    opened.contents reached.2 opened.phase = some .poisoned :=
  stoppedKeeps.trans (stop.toNativeCheckpointSourcePrefix.phaseAtIssue returnedKeeps)

/-- A returned publication error also leaves that same phase poisoned. -/
theorem NativeCheckpointSourceError.phaseAtError {current : NativeOpenedPosition opened}
    {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap} {fsync : CheckpointFsync heap}
    {stage : Step} {cause : IO.Error} {reached : CheckpointWorld heap}
    (failed : NativeCheckpointSourceError current primitives fsync stage cause reached)
    (returnedKeeps : failed.toNativeCheckpointSourcePrefix.KeepsPhase)
    (failedKeeps : opened.contents reached.2 opened.phase = opened.contents failed.atIssue.2 opened.phase) :
    opened.contents reached.2 opened.phase = some .poisoned :=
  failedKeeps.trans (failed.toNativeCheckpointSourcePrefix.phaseAtIssue returnedKeeps)

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

/-- The returned run write supplies the actual payload, handle and pending cache. -/
theorem CheckpointPrimitiveCalls.runWriteReturned
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap) (directory : DiskDirectory)
    (fsync : CheckpointFsync heap) (next : Installed) (manifest : ByteArray) (index : Nat)
    {before after : CheckpointWorld heap}
    (returned : (primitives.checkpointStepUntilStop directory fsync next manifest (.writeRun index)).run before =
      .ok (.ok ()) after) :
    let path := directory.file (.run next.generation index)
    ∃ run handle, next.table.runs.toArray[index]? = some run ∧
      primitives.cached.writeRun path run.run.bytes before.2 = .ok handle after.2 ∧
      after.1 = before.1.remember path handle := by
  intro path
  obtain ⟨cache, raw⟩ := before
  cases found : next.table.runs.toArray[index]? with
  | none =>
    simp [CheckpointFileCallbacks.performUntilSyncStop, performCheckpointFileStep, found,
      Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.run, ExceptT.mk, EStateM.bind,
      Pure.pure, EStateM.pure, MonadExceptOf.throw, throw, throwThe] at returned
  | some run =>
    have write := (primitives.cached.callbacks directory).performRunWriteUntilSyncStop
      (primitives.syncUntilStop directory.path fsync) directory next manifest found (cache, raw)
    rw [write] at returned
    simp only [CheckpointCacheCalls.callbacks] at returned
    cases wrote : primitives.cached.writeRun (directory.file (.run next.generation index)) run.run.bytes raw with
    | error cause reached =>
      simp [stageFreshWithCache, wrote] at returned
    | ok handle flushed =>
      simp only [stageFreshWithCache, wrote] at returned
      have reachedWrite := (EStateM.Result.ok.inj returned).2
      exact ⟨run, handle, rfl, (congrArg Prod.snd reachedWrite) ▸ wrote, (congrArg Prod.fst reachedWrite).symm⟩

private theorem checkpointStoppedRememberedFile
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap) (fsync : CheckpointFsync heap)
    {directory path reason : FilePath} {atIssue reached : CheckpointWorld heap}
    {cache : CensusDirectoryCache} {handle : CheckpointOpenHandle} (separate : path ≠ directory)
    (remembered : atIssue.1 = cache.remember path handle)
    (stopped : (primitives.syncUntilStop directory fsync #[path]).run atIssue = .error reason reached) :
    reached.1 = atIssue.1.consume path ∧ fsync handle atIssue.2 = .error reason reached.2 := by
  obtain ⟨selected, atEffect, resolved, issued⟩ := primitives.issuedFsync stopped
  rw [remembered, Cache.resolveRemembered separate handle primitives.openRead atIssue.2] at resolved
  obtain ⟨rfl, cacheAndHeap⟩ := EStateM.Result.ok.inj resolved
  have sameCache := congrArg Prod.fst cacheAndHeap
  have sameHeap := congrArg Prod.snd cacheAndHeap
  refine ⟨?_, sameHeap.symm ▸ issued⟩
  rw [remembered]
  simpa [Cache.consume, Cache.remember, pushPending] using sameCache.symm

/-- The last returned step before a run fsync installs the exact
descriptor selected by that fsync. Extract both effects from the same
prefix. The ordinary write callback includes guard, open and flush. -/
theorem NativeCheckpointSourceStop.runFileUsesWrittenHandle {index : Nat}
    (stop : NativeCheckpointSourceStop current primitives fsync (.syncRun index) reason reached) :
    let directory := current.current.ready.state.session.directory
    let path := directory.file (.run stop.next.generation index)
    let perform := primitives.checkpointStepUntilStop directory fsync stop.next stop.manifest
    ∃ beforeWrite run handle,
      ((runSteps index).forM perform).run (current.current.ready.state.cache, stop.poisoned) = .ok (.ok ()) beforeWrite ∧
      stop.next.table.runs.toArray[index]? = some run ∧
      primitives.cached.writeRun path run.run.bytes beforeWrite.2 = .ok handle stop.atIssue.2 ∧
      stop.atIssue.1 = beforeWrite.1.remember path handle ∧
      reached.1 = stop.atIssue.1.consume path ∧
      fsync handle stop.atIssue.2 = .error reason reached.2 := by
  intro directory path perform
  have stage := stop.runFileIssue
  have completed := stop.returnedPrefix
  rw [stage.2.1] at completed
  obtain ⟨beforeWrite, earlier, lastWrite⟩ := returnedLastStep perform (runSteps index) (.writeRun index) completed
  obtain ⟨run, handle, selectedRun, wrote, staged⟩ :=
    primitives.runWriteReturned directory fsync stop.next stop.manifest index lastWrite
  obtain ⟨consumed, stopped⟩ := checkpointStoppedRememberedFile primitives fsync
    (file_ne_directory _ _) staged stop.stoppedStep
  exact ⟨beforeWrite, run, handle, earlier, selectedRun, wrote, staged, consumed, stopped⟩

private theorem checkpointManifestWriteReturned
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap) (directory : DiskDirectory)
    (fsync : CheckpointFsync heap) (next : Installed) (manifest : ByteArray)
    {before after : CheckpointWorld heap}
    (returned : (primitives.checkpointStepUntilStop directory fsync next manifest (.manifest .writeStaged)).run before =
      .ok (.ok ()) after) :
    let path := directory.file .stagedManifest
    ∃ handle, primitives.cached.writeStaged path manifest before.2 = .ok handle after.2 ∧
      after.1 = before.1.remember path handle := by
  intro path
  obtain ⟨cache, raw⟩ := before
  have stage := (primitives.cached.callbacks directory).performManifestWriteUntilSyncStop
    (primitives.syncUntilStop directory.path fsync) directory next manifest (cache, raw)
  rw [stage] at returned
  simp only [CheckpointCacheCalls.callbacks] at returned
  cases wrote : primitives.cached.writeStaged (directory.file .stagedManifest) manifest raw with
  | error cause reached => simp [stageFreshWithCache, wrote] at returned
  | ok handle flushed =>
    simp only [stageFreshWithCache, wrote] at returned
    have reachedWrite := (EStateM.Result.ok.inj returned).2
    exact ⟨handle, congrArg (EStateM.Result.ok handle) (congrArg Prod.snd reachedWrite),
      (congrArg Prod.fst reachedWrite).symm⟩

/-- A stopped manifest file barrier follows the actual completed run and
directory prefix. Its staged write supplied the same handle that issued fsync. -/
theorem NativeCheckpointSourceStop.manifestSyncUsesWrittenHandle
    (stop : NativeCheckpointSourceStop current primitives fsync (.manifest .syncStaged) reason reached) :
    let directory := current.current.ready.state.session.directory
    let path := directory.file .stagedManifest
    let perform := primitives.checkpointStepUntilStop directory fsync stop.next stop.manifest
    ∃ beforeWrite handle,
      ((runSteps stop.next.table.runs.length ++ [Step.syncRunsDirectory]).forM perform).run
        (current.current.ready.state.cache, stop.poisoned) = .ok (.ok ()) beforeWrite ∧
      primitives.cached.writeStaged path stop.manifest beforeWrite.2 = .ok handle stop.atIssue.2 ∧
      stop.atIssue.1 = beforeWrite.1.remember path handle ∧
      reached.1 = stop.atIssue.1.consume path ∧
      fsync handle stop.atIssue.2 = .error reason reached.2 := by
  intro directory path perform
  have completed := stop.returnedPrefix
  rw [prefixBeforeManifestSync stop.ordered] at completed
  obtain ⟨beforeWrite, earlier, lastWrite⟩ := returnedLastStep perform
    (runSteps stop.next.table.runs.length ++ [.syncRunsDirectory]) (.manifest .writeStaged) completed
  obtain ⟨handle, wrote, staged⟩ :=
    checkpointManifestWriteReturned primitives directory fsync stop.next stop.manifest lastWrite
  obtain ⟨consumed, stopped⟩ := checkpointStoppedRememberedFile primitives fsync
    (file_ne_directory _ _) staged stop.stoppedStep
  exact ⟨beforeWrite, handle, earlier, wrote, staged, consumed, stopped⟩

theorem NativeCheckpointSourceStop.runsDirectoryIssue
    (stop : NativeCheckpointSourceStop current primitives fsync .syncRunsDirectory reason reached) :
    let dir := current.current.ready.state.session.directory.path
    stop.completed = runSteps stop.next.table.runs.length ∧
    ∃ handle atEffect,
      stop.atIssue.1.resolve dir dir primitives.openRead stop.atIssue.2 =
        .ok handle (reached.1, atEffect) ∧ fsync handle atEffect = .error reason reached.2 := by
  exact ⟨prefixBeforeRunsDirectory stop.ordered, primitives.issuedFsync stop.stoppedStep⟩

/-- The successful manifest rename advances the raw heap and retains
the checkpoint cache. -/
theorem CheckpointPrimitiveCalls.manifestRenameReturned
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap) (directory : DiskDirectory)
    (fsync : CheckpointFsync heap) (next : Installed) (manifest : ByteArray)
    {before after : CheckpointWorld heap}
    (returned : (primitives.checkpointStepUntilStop directory fsync next manifest (.manifest .renameStaged)).run
      before = .ok (.ok ()) after) :
    primitives.rename (directory.file .stagedManifest) (directory.file .manifest) before.2 = .ok () after.2 ∧
      after.1 = before.1 := by
  obtain ⟨cache, raw⟩ := before
  rw [CheckpointFileCallbacks.performManifestRenameUntilSyncStop] at returned
  simp only [CheckpointCacheCalls.callbacks, CheckpointPrimitiveCalls.cached] at returned
  cases renamed : primitives.rename (directory.file .stagedManifest) (directory.file .manifest) raw with
  | error cause after => simp [withCache, renamed] at returned
  | ok value after =>
    cases value
    simp only [withCache, renamed] at returned
    have same := (EStateM.Result.ok.inj returned).2
    exact ⟨congrArg (EStateM.Result.ok ()) (congrArg Prod.snd same), (congrArg Prod.fst same).symm⟩

/-- The final directory barrier follows the actual returned replacement
of MANIFEST. Extract the rename's entry and return from the same prefix
that supplies the issued directory descriptor and fsync heap. -/
theorem NativeCheckpointSourceStop.manifestDirectoryFollowsRename
    (stop : NativeCheckpointSourceStop current primitives fsync (.manifest .syncDirectory) reason reached) :
    let directory := current.current.ready.state.session.directory
    let perform := primitives.checkpointStepUntilStop directory fsync stop.next stop.manifest
    let beforeRenameSteps : List Step := runSteps stop.next.table.runs.length ++
      [.syncRunsDirectory, .manifest .writeStaged, .manifest .syncStaged]
    ∃ beforeRename handle atSync,
      (beforeRenameSteps.forM perform).run (current.current.ready.state.cache, stop.poisoned) =
        .ok (.ok ()) beforeRename ∧
      primitives.rename (directory.file .stagedManifest) (directory.file .manifest) beforeRename.2 =
        .ok () stop.atIssue.2 ∧ stop.atIssue.1 = beforeRename.1 ∧
      stop.atIssue.1.resolve directory.path directory.path primitives.openRead stop.atIssue.2 =
        .ok handle (reached.1, atSync) ∧ fsync handle atSync = .error reason reached.2 := by
  intro directory perform beforeRenameSteps
  have completed := stop.returnedPrefix
  rw [prefixBeforeManifestDirectory stop.ordered] at completed
  obtain ⟨beforeRename, earlier, renameReturned⟩ :=
    returnedLastStep perform beforeRenameSteps (.manifest .renameStaged) completed
  obtain ⟨handle, atSync, resolved, issued⟩ := primitives.issuedFsync stop.stoppedStep
  obtain ⟨renamed, keepsCache⟩ :=
    primitives.manifestRenameReturned directory fsync stop.next stop.manifest renameReturned
  exact ⟨beforeRename, handle, atSync, earlier, renamed, keepsCache, resolved, issued⟩

private theorem resolveKeepsDirectory (cache : CensusDirectoryCache) (dir path : FilePath)
    (openRead : FilePath → EStateM IO.Error heap CheckpointOpenHandle) (before : heap) :
    (reachedState (cache.resolve dir path openRead before)).1.directory = cache.directory := by
  by_cases isDirectory : path = dir
  · cases found : cache.directory <;> simp [Cache.resolve, isDirectory, found, reachedState]
  · cases pending : cache.pending.find? (fun entry => entry.1 == path) with
    | some found => simp [Cache.resolve, isDirectory, pending, Cache.consume, reachedState]
    | none =>
      have reopened : (reachedState (withCache cache (openRead path before))).1.directory = cache.directory := by
        cases openRead path before <;> rfl
      cases active : cache.active with
      | none => simpa only [Cache.resolve, isDirectory, beq_iff_eq, ↓reduceIte, pending, active] using reopened
      | some found =>
        by_cases same : found.1 = path
        · simp [Cache.resolve, isDirectory, pending, active, same, reachedState]
        · simpa only [Cache.resolve, isDirectory, beq_iff_eq, ↓reduceIte, pending, active, same] using reopened

/-- Invert a returned singleton group to recover the actual handle selection
and successful fsync, with their own issue and return heaps. -/
theorem CheckpointPrimitiveCalls.returnedFsync
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap) (fsync : CheckpointFsync heap)
    (dir path : FilePath) {before after : CheckpointWorld heap}
    (returned : (primitives.syncUntilStop dir fsync #[path]).run before = .ok (.ok ()) after) :
    ∃ handle issued, before.1.resolve dir path primitives.openRead before.2 = .ok handle (after.1, issued) ∧
      fsync handle issued = .ok (.ok ()) after.2 := by
  obtain ⟨cache, raw⟩ := before
  have success : ∃ atSync, checkpointSyncUntilStop dir primitives.openRead fsync path (cache, raw) = .ok (.ok ()) atSync ∧
      after = atSync := by
    let sync := checkpointSyncUntilStop dir primitives.openRead fsync
    change (SyncPathGroup.run sync #[path]).run (cache, raw) = _ at returned
    cases issued : (sync path).run (cache, raw) with
    | error reason reached =>
      change sync path (cache, raw) = _ at issued
      simp [SyncPathGroup.run, ← Array.forIn_toList, List.forIn_cons, List.forIn_nil,
        MonadExcept.tryCatch, MonadExceptOf.tryCatch, tryCatchThe, ExceptT.tryCatch, Bind.bind, ExceptT.bind,
        ExceptT.run, ExceptT.mk, EStateM.bind, StateT.pure, Pure.pure, ExceptT.pure, issued] at returned
    | ok result reached =>
      change sync path (cache, raw) = _ at issued
      cases result with
      | error cause =>
        simp [SyncPathGroup.run, ← Array.forIn_toList, List.forIn_cons, List.forIn_nil,
          MonadExcept.tryCatch, MonadExceptOf.tryCatch, tryCatchThe, ExceptT.tryCatch, Bind.bind, ExceptT.bind,
          ExceptT.run, ExceptT.mk, EStateM.bind, StateT.pure, Pure.pure, ExceptT.pure, ExceptT.bindCont,
          MonadExceptOf.throw, throw, throwThe, EStateM.pure, issued] at returned
      | ok resultValue =>
        cases resultValue
        simp [SyncPathGroup.run, ← Array.forIn_toList, List.forIn_cons, List.forIn_nil,
          MonadExcept.tryCatch, MonadExceptOf.tryCatch, tryCatchThe, ExceptT.tryCatch, Bind.bind, ExceptT.bind,
          ExceptT.run, ExceptT.mk, EStateM.bind, StateT.pure, Pure.pure, ExceptT.pure, ExceptT.bindCont,
          MonadExceptOf.throw, throw, throwThe, EStateM.pure, issued] at returned
        exact ⟨reached, issued, returned.symm⟩
  obtain ⟨atSync, sync, rfl⟩ := success
  cases resolved : cache.resolve dir path primitives.openRead raw with
  | error cause reached => simp [checkpointSyncUntilStop, resolved] at sync
  | ok handle atEffect =>
    obtain ⟨selectedCache, heapAtEffect⟩ := atEffect
    cases ran : fsync handle heapAtEffect with
    | error reason reached => simp [checkpointSyncUntilStop, resolved, ran] at sync
    | ok result reached =>
      simp only [checkpointSyncUntilStop, resolved, ran] at sync
      cases result <;> cases sync
      exact ⟨handle, heapAtEffect, rfl, ran⟩

/-- A returned file fsync consumes the handle remembered by its write.
The cached selection keeps the raw heap at the actual syscall entry. -/
theorem CheckpointPrimitiveCalls.returnedRememberedFile
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap) (fsync : CheckpointFsync heap)
    {directory path : FilePath} {atIssue after : CheckpointWorld heap}
    {cache : CensusDirectoryCache} {handle : CheckpointOpenHandle}
    (separate : path ≠ directory) (remembered : atIssue.1 = cache.remember path handle)
    (returned : (primitives.syncUntilStop directory fsync #[path]).run atIssue = .ok (.ok ()) after) :
    after.1 = cache.consume path ∧ fsync handle atIssue.2 = .ok (.ok ()) after.2 := by
  obtain ⟨literal, atSync, resolved, effect⟩ := primitives.returnedFsync fsync directory path returned
  rw [remembered, Cache.resolveRemembered separate handle primitives.openRead atIssue.2] at resolved
  obtain ⟨rfl, same⟩ := EStateM.Result.ok.inj resolved
  exact ⟨(congrArg Prod.fst same).symm, (congrArg Prod.snd same).symm ▸ effect⟩

/-- The manifest staged on the way to the final directory barrier was
synced using the descriptor returned by the actual write. Consuming that
descriptor does not change the raw heap where the fsync issues. -/
theorem NativeCheckpointSourcePrefix.manifestRenameFollowsStagedSync
    (stop : NativeCheckpointSourcePrefix current primitives fsync stage)
    {beforeRename : CheckpointWorld heap}
    (returned : let directory := current.current.ready.state.session.directory
      let perform := primitives.checkpointStepUntilStop directory fsync stop.next stop.manifest
      ((runSteps stop.next.table.runs.length ++
        [Step.syncRunsDirectory, Step.manifest .writeStaged, Step.manifest .syncStaged]).forM perform).run
        (current.current.ready.state.cache, stop.poisoned) = .ok (.ok ()) beforeRename) :
    let directory := current.current.ready.state.session.directory
    let path := directory.file .stagedManifest
    let perform := primitives.checkpointStepUntilStop directory fsync stop.next stop.manifest
    ∃ (beforeWrite afterWrite : CheckpointWorld heap) (handle : CheckpointOpenHandle),
      ((runSteps stop.next.table.runs.length ++ [Step.syncRunsDirectory]).forM perform).run
        (current.current.ready.state.cache, stop.poisoned) = .ok (.ok ()) beforeWrite ∧
      primitives.cached.writeStaged path stop.manifest beforeWrite.2 = .ok handle afterWrite.2 ∧
      afterWrite.1 = beforeWrite.1.remember path handle ∧
      fsync handle afterWrite.2 = .ok (.ok ()) beforeRename.2 ∧
      beforeRename.1 = beforeWrite.1.consume path := by
  intro directory path perform
  let prior := runSteps stop.next.table.runs.length ++ [Step.syncRunsDirectory]
  change ((runSteps stop.next.table.runs.length ++
    [Step.syncRunsDirectory, Step.manifest .writeStaged, Step.manifest .syncStaged]).forM perform).run _ = _ at returned
  have order : runSteps stop.next.table.runs.length ++
      [Step.syncRunsDirectory, Step.manifest .writeStaged, Step.manifest .syncStaged] =
      (prior ++ [.manifest .writeStaged]) ++ [.manifest .syncStaged] := by
    simp only [prior, List.append_assoc, List.cons_append, List.nil_append]
  rw [order] at returned
  obtain ⟨afterWrite, written, sync⟩ := returnedLastStep perform
    (prior ++ [.manifest .writeStaged]) (.manifest .syncStaged) returned
  obtain ⟨beforeWrite, earlier, write⟩ := returnedLastStep perform prior (.manifest .writeStaged) written
  obtain ⟨handle, wrote, remembered⟩ :=
    checkpointManifestWriteReturned primitives directory fsync stop.next stop.manifest write
  have synced : (primitives.syncUntilStop directory.path fsync #[path]).run afterWrite = .ok (.ok ()) beforeRename := sync
  obtain ⟨consumed, effect⟩ := primitives.returnedRememberedFile fsync (file_ne_directory _ _) remembered synced
  exact ⟨beforeWrite, afterWrite, handle, earlier, wrote, remembered, effect, consumed⟩

abbrev NativeCheckpointSourceStop.manifestRenameFollowsStagedSync
    (stop : NativeCheckpointSourceStop current primitives fsync (.manifest .syncDirectory) reason reached)
    {beforeRename : CheckpointWorld heap} :=
  stop.toNativeCheckpointSourcePrefix.manifestRenameFollowsStagedSync (beforeRename := beforeRename)

/-- The first returned error at the manifest rename names the actual
callback between the staged file sync and the unexecuted final barrier. -/
theorem NativeCheckpointSourceError.manifestRenameFailed
    (failed : NativeCheckpointSourceError current primitives fsync (.manifest .renameStaged) cause reached) :
    let directory := current.current.ready.state.session.directory
    let path := directory.file .stagedManifest
    let perform := primitives.checkpointStepUntilStop directory fsync failed.next failed.manifest
    primitives.rename path (directory.file .manifest) failed.atIssue.2 = .error cause reached.2 ∧
    reached.1 = failed.atIssue.1 ∧
    ∃ (beforeWrite afterWrite : CheckpointWorld heap) (handle : CheckpointOpenHandle),
      ((runSteps failed.next.table.runs.length ++ [Step.syncRunsDirectory]).forM perform).run
        (current.current.ready.state.cache, failed.poisoned) = .ok (.ok ()) beforeWrite ∧
      primitives.cached.writeStaged path failed.manifest beforeWrite.2 = .ok handle afterWrite.2 ∧
      afterWrite.1 = beforeWrite.1.remember path handle ∧
      fsync handle afterWrite.2 = .ok (.ok ()) failed.atIssue.2 ∧
      failed.atIssue.1 = beforeWrite.1.consume path := by
  intro directory path perform
  have earlier := failed.returnedPrefix
  rw [prefixBeforeManifestRename failed.ordered] at earlier
  have renameEffect : primitives.rename path (directory.file .manifest) failed.atIssue.2 = .error cause reached.2 ∧
      reached.1 = failed.atIssue.1 := by
    have failure := failed.failedStep
    rw [CheckpointFileCallbacks.performManifestRenameUntilSyncStop] at failure
    simp only [CheckpointCacheCalls.callbacks, CheckpointPrimitiveCalls.cached] at failure
    cases renamed : primitives.rename
      (current.current.ready.state.session.directory.file .stagedManifest)
      (current.current.ready.state.session.directory.file .manifest) failed.atIssue.2 with
    | ok value after => simp [withCache, renamed] at failure
    | error diagnostic after =>
      simp only [withCache, renamed] at failure
      obtain ⟨different, world⟩ := EStateM.Result.ok.inj failure
      cases different
      exact ⟨congrArg (EStateM.Result.error cause) (congrArg Prod.snd world), (congrArg Prod.fst world).symm⟩
  exact ⟨renameEffect.1, renameEffect.2,
    failed.toNativeCheckpointSourcePrefix.manifestRenameFollowsStagedSync earlier⟩

private theorem checkpointSyncKeepsDirectory
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap) (fsync : CheckpointFsync heap)
    (dir path : FilePath) {before after : CheckpointWorld heap}
    (returned : (primitives.syncUntilStop dir fsync #[path]).run before = .ok (.ok ()) after) :
    after.1.directory = before.1.directory := by
  obtain ⟨_, _, resolved, _⟩ := primitives.returnedFsync fsync dir path returned
  simpa only [resolved, reachedState] using
    resolveKeepsDirectory before.1 dir path primitives.openRead before.2

private theorem checkpointStepKeepsDirectory
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap) (directory : DiskDirectory)
    (fsync : CheckpointFsync heap) (next : Installed) (manifest : ByteArray)
    (step : Step) {before after : CheckpointWorld heap}
    (returned : (primitives.checkpointStepUntilStop directory fsync next manifest step).run before =
      .ok (.ok ()) after) :
    after.1.directory = before.1.directory := by
  cases step with
  | writeRun index =>
    obtain ⟨_, _, _, _, remembered⟩ := primitives.runWriteReturned directory fsync next manifest index returned
    rw [remembered]
    rfl
  | syncRun index =>
    exact checkpointSyncKeepsDirectory primitives fsync directory.path
      (directory.file (.run next.generation index)) returned
  | syncRunsDirectory =>
    exact checkpointSyncKeepsDirectory primitives fsync directory.path directory.path returned
  | manifest step =>
    cases step with
    | writeStaged =>
      obtain ⟨_, _, remembered⟩ := checkpointManifestWriteReturned primitives directory fsync next manifest returned
      rw [remembered]
      rfl
    | syncStaged =>
      exact checkpointSyncKeepsDirectory primitives fsync directory.path (directory.file .stagedManifest) returned
    | renameStaged =>
      exact congrArg Cache.directory (primitives.manifestRenameReturned directory fsync next manifest returned).2
    | syncDirectory =>
      exact checkpointSyncKeepsDirectory primitives fsync directory.path directory.path returned

/-- A returned checkpoint step can add or consume pending handles.
The original directory slot survives the whole prefix, including rename. -/
theorem NativeCheckpointSourcePrefix.directoryCacheAtIssue
    (prior : NativeCheckpointSourcePrefix current primitives fsync stage) :
    prior.atIssue.1.directory = current.current.ready.state.cache.directory :=
  successfulCheckpointStepsFrame _ (fun world => world.1.directory) prior.completed
    (fun step _ _ _ => checkpointStepKeepsDirectory primitives current.current.ready.state.session.directory
      fsync prior.next prior.manifest step) prior.returnedPrefix

private theorem checkpointDirectoryUsesCachedHandle
    (stop : NativeCheckpointSourceStop current primitives fsync stage reason reached)
    (issued : let dir := current.current.ready.state.session.directory.path
      (primitives.syncUntilStop dir fsync #[dir]).run stop.atIssue = .error reason reached) :
    ∃ handle, current.current.ready.state.cache.directory = some handle ∧
      stop.atIssue.1.directory = some handle ∧
      reached.1 = stop.atIssue.1 ∧ fsync handle stop.atIssue.2 = .error reason reached.2 := by
  obtain ⟨handle, heapAtEffect, resolved, effect⟩ := primitives.issuedFsync issued
  simp only [Cache.resolve, beq_self_eq_true, ↓reduceIte] at resolved
  cases cached : stop.atIssue.1.directory with
  | none => rw [cached] at resolved; cases resolved
  | some original =>
    rw [cached] at resolved
    obtain ⟨rfl, same⟩ := EStateM.Result.ok.inj resolved
    exact ⟨original, stop.toNativeCheckpointSourcePrefix.directoryCacheAtIssue.symm.trans cached, rfl, (congrArg Prod.fst same).symm,
      (congrArg Prod.snd same).symm ▸ effect⟩

/-- The first directory barrier issues on the original cached descriptor. -/
theorem NativeCheckpointSourceStop.runsDirectoryUsesCachedHandle
    (stop : NativeCheckpointSourceStop current primitives fsync .syncRunsDirectory reason reached) :
    ∃ handle, current.current.ready.state.cache.directory = some handle ∧
      stop.atIssue.1.directory = some handle ∧
      reached.1 = stop.atIssue.1 ∧ fsync handle stop.atIssue.2 = .error reason reached.2 :=
  checkpointDirectoryUsesCachedHandle stop stop.stoppedStep

/-- After the manifest rename, the final directory barrier issues on
the same original cached descriptor. -/
theorem NativeCheckpointSourceStop.manifestDirectoryUsesCachedHandle
    (stop : NativeCheckpointSourceStop current primitives fsync (.manifest .syncDirectory) reason reached) :
    ∃ handle, current.current.ready.state.cache.directory = some handle ∧
      stop.atIssue.1.directory = some handle ∧
      reached.1 = stop.atIssue.1 ∧ fsync handle stop.atIssue.2 = .error reason reached.2 :=
  checkpointDirectoryUsesCachedHandle stop stop.stoppedStep

end Alvoki.Storage.DiskSession
