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
    (stopped : (runCheckpointOnOpenPhaseUntilSyncStop current.current.ready.state.session.directory
      opened.phase opened.get opened.set primitives fsync).run
        (current.current.ready.state.cache, current.reached) = .error (step, reason) reached) :
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
    (observe : CheckpointWorld heap → value) (completed : List Step)
    (frame : ∀ step ∈ completed, ∀ before after,
      (perform step).run before = .ok (.ok ()) after → observe after = observe before)
    {before after : CheckpointWorld heap}
    (returned : (completed.forM perform).run before = .ok (.ok ()) after) :
    observe after = observe before := by
  induction completed generalizing before with
  | nil =>
    have same := (EStateM.Result.ok.inj returned).2
    exact congrArg observe same.symm
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
  have completed := successfulCheckpointStepsFrame _ (fun world => opened.contents world.2 opened.phase)
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

private theorem checkpointRunWriteReturned
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
  rw [stage.2.1, List.forM_eq_forM, List.forM_append] at completed
  change (ExceptT.bind ((runSteps index).forM perform)
    (fun _ => ExceptT.bind (perform (.writeRun index)) (fun _ => pure ()))).run
      (current.current.ready.state.cache, stop.poisoned) = _ at completed
  rw [run_bind] at completed
  cases ran : ((runSteps index).forM perform).run (current.current.ready.state.cache, stop.poisoned) with
  | error rejected after => rw [ran] at completed; cases completed
  | ok returned beforeWrite =>
    rw [ran] at completed
    cases returned with
    | error cause => cases completed
    | ok value =>
      cases value
      change (ExceptT.bind (perform (.writeRun index)) (fun _ => pure ())).run beforeWrite = _ at completed
      rw [run_bind] at completed
      have lastWrite : (perform (.writeRun index)).run beforeWrite = .ok (.ok ()) stop.atIssue := by
        cases wrote : (perform (.writeRun index)).run beforeWrite with
        | error rejected after => rw [wrote] at completed; cases completed
        | ok returned after =>
          rw [wrote] at completed
          cases returned with
          | error cause => cases completed
          | ok value =>
            cases value
            exact congrArg (EStateM.Result.ok (Except.ok () : Except IO.Error Unit))
              (EStateM.Result.ok.inj completed).2
      obtain ⟨run, handle, selectedRun, wrote, staged⟩ :=
        checkpointRunWriteReturned primitives directory fsync stop.next stop.manifest index lastWrite
      obtain ⟨selected, atEffect, resolved, issued⟩ := stage.2.2
      change stop.atIssue.1.resolve directory.path path primitives.openRead stop.atIssue.2 = _ at resolved
      rw [staged, Cache.resolveRemembered (file_ne_directory _ _) handle primitives.openRead stop.atIssue.2] at resolved
      obtain ⟨rfl, cacheAndHeap⟩ := EStateM.Result.ok.inj resolved
      have sameCache := congrArg Prod.fst cacheAndHeap
      have sameHeap := congrArg Prod.snd cacheAndHeap
      refine ⟨beforeWrite, run, handle, rfl, selectedRun, wrote, staged, ?_, sameHeap.symm ▸ issued⟩
      rw [staged]
      simpa [Cache.consume, Cache.remember, pushPending, path] using sameCache.symm

theorem NativeCheckpointSourceStop.runsDirectoryIssue
    (stop : NativeCheckpointSourceStop current primitives fsync .syncRunsDirectory reason reached) :
    let dir := current.current.ready.state.session.directory.path
    stop.completed = runSteps stop.next.table.runs.length ∧
    ∃ handle atEffect,
      stop.atIssue.1.resolve dir dir primitives.openRead stop.atIssue.2 =
        .ok handle (reached.1, atEffect) ∧ fsync handle atEffect = .error reason reached.2 := by
  exact ⟨prefixBeforeRunsDirectory stop.ordered, primitives.issuedFsync stop.stoppedStep⟩

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

private theorem checkpointSyncKeepsDirectory
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap) (fsync : CheckpointFsync heap)
    (dir path : FilePath) {before after : CheckpointWorld heap}
    (returned : (primitives.syncUntilStop dir fsync #[path]).run before = .ok (.ok ()) after) :
    after.1.directory = before.1.directory := by
  obtain ⟨cache, raw⟩ := before
  have frame := resolveKeepsDirectory cache dir path primitives.openRead raw
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
    simp only [resolved, reachedState] at frame
    cases ran : fsync handle heapAtEffect with
    | error reason reached => simp [checkpointSyncUntilStop, resolved, ran] at sync
    | ok result reached =>
      simp only [checkpointSyncUntilStop, resolved, ran] at sync
      cases result <;> cases sync
      exact frame

/-- All preceding run pairs leave the original directory descriptor in
its cache slot. The next barrier issues on that exact descriptor. -/
theorem NativeCheckpointSourceStop.runsDirectoryUsesCachedHandle
    (stop : NativeCheckpointSourceStop current primitives fsync .syncRunsDirectory reason reached) :
    ∃ handle, current.current.ready.state.cache.directory = some handle ∧
      stop.atIssue.1.directory = some handle ∧
      reached.1 = stop.atIssue.1 ∧ fsync handle stop.atIssue.2 = .error reason reached.2 := by
  let directory := current.current.ready.state.session.directory
  have issued := stop.runsDirectoryIssue
  have frame : ∀ step ∈ stop.completed, ∀ before after,
      (primitives.checkpointStepUntilStop directory fsync stop.next stop.manifest step).run before =
        .ok (.ok ()) after → after.1.directory = before.1.directory := by
    intro step member before after returned
    rw [issued.1] at member
    simp only [runSteps, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at member
    obtain ⟨index, within, write | sync⟩ := member
    · subst step
      obtain ⟨_, _, _, _, staged⟩ := checkpointRunWriteReturned
        primitives directory fsync stop.next stop.manifest index returned
      rw [staged]; rfl
    · subst step
      exact checkpointSyncKeepsDirectory primitives fsync directory.path
        (directory.file (.run stop.next.generation index)) returned
  have kept := successfulCheckpointStepsFrame _ (fun world => world.1.directory)
    stop.completed frame stop.returnedPrefix
  obtain ⟨handle, heapAtEffect, resolved, effect⟩ := issued.2
  simp only [Cache.resolve, beq_self_eq_true, ↓reduceIte] at resolved
  cases cached : stop.atIssue.1.directory with
  | none => rw [cached] at resolved; cases resolved
  | some original =>
    rw [cached] at resolved
    obtain ⟨rfl, same⟩ := EStateM.Result.ok.inj resolved
    exact ⟨original, kept.symm.trans cached, rfl, (congrArg Prod.fst same).symm,
      (congrArg Prod.snd same).symm ▸ effect⟩

end Alvoki.Storage.DiskSession
