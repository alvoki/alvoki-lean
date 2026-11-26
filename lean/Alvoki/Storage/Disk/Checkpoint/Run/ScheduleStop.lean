import Alvoki.Storage.Disk.CheckpointRunFileSyncFailure

namespace Alvoki.Storage.CheckpointPublication

open System

/-- A callback can return an ordinary result or stop before returning.
Only an outer stop is annotated with the step that actually issued it. -/
def tagStop {image : Type} (perform : Step → ExceptT IO.Error (EStateM FilePath image) Unit) (step : Step) :
    ExceptT IO.Error (EStateM (Step × FilePath) image) Unit :=
  fun before => match (perform step).run before with
    | .ok returned reached => .ok returned reached
    | .error path reached => .error (step, path) reached

/-- Sequence a returned action without trapping the outer interruption. -/
theorem run_bind {halt image α β : Type} (action : ExceptT IO.Error (EStateM halt image) α)
    (next : α → ExceptT IO.Error (EStateM halt image) β) (before : image) :
    (ExceptT.bind action next).run before =
      match action.run before with
      | .ok result reached =>
        match result with
        | .ok value => (next value).run reached
        | .error cause => .ok (.error cause) reached
      | .error stop reached => .error stop reached := by
  change EStateM.bind action (ExceptT.bindCont next) before = _
  simp only [EStateM.bind, ExceptT.run]
  cases action before with
  | error => rfl
  | ok result => cases result <;> rfl

private def exitResult {halt image : Type} (exit : Except IO.Error halt) (after : image) :
    EStateM.Result halt image (Except IO.Error Unit) :=
  match exit with
  | .error cause => .ok (.error cause) after
  | .ok stop => .error stop after

private theorem forM_firstExit {image : Type}
    (actions : List Step) (perform : Step → ExceptT IO.Error (EStateM FilePath image) Unit)
    {before after : image} {exit : Except IO.Error (Step × FilePath)}
    (ended : (actions.forM (tagStop perform)).run before = exitResult exit after) :
    ∃ done step remaining atIssue, actions = done ++ step :: remaining ∧
      (done.forM perform).run before = .ok (.ok ()) atIssue ∧
      (tagStop perform step).run atIssue = exitResult exit after := by
  induction actions generalizing before with
  | nil =>
    change EStateM.Result.ok (Except.ok ()) before = exitResult exit after at ended
    cases exit <;> cases ended
  | cons issued tail ih =>
    change (ExceptT.bind (tagStop perform issued) (fun _ => tail.forM (tagStop perform))).run before = _ at ended
    rw [run_bind] at ended
    cases call : (perform issued).run before with
    | error stoppedPath reached =>
      have tagged : (tagStop perform issued).run before = .error (issued, stoppedPath) reached := by
        change perform issued before = _ at call
        simp only [tagStop, ExceptT.run, call]
      rw [tagged] at ended
      exact ⟨[], issued, tail, before, rfl, rfl, tagged.trans ended⟩
    | ok returned reached =>
      have tagged : (tagStop perform issued).run before = .ok returned reached := by
        change perform issued before = _ at call
        simp only [tagStop, ExceptT.run, call]
      rw [tagged] at ended
      cases returned with
      | error cause => exact ⟨[], issued, tail, before, rfl, rfl, tagged.trans ended⟩
      | ok value =>
        obtain ⟨done, step, remaining, atIssue, order, returnedPrefix, cut⟩ := ih ended
        refine ⟨issued :: done, step, remaining, atIssue, congrArg (List.cons issued) order, ?_, cut⟩
        change (ExceptT.bind (perform issued) (fun _ => done.forM perform)).run before = _
        rw [run_bind, call]
        exact returnedPrefix

/-- Extract the successful prefix and precise issued callback from the
whole checkpoint schedule, without supplying a completed list. -/
theorem run_firstStop {image : Type} {count : Nat}
    {perform : Step → ExceptT IO.Error (EStateM FilePath image) Unit}
    {before after : image} {step : Step} {path : FilePath}
    (stopped : (run count (tagStop perform)).run before = .error (step, path) after) :
    ∃ done remaining atIssue, steps count = done ++ step :: remaining ∧
      (done.forM perform).run before = .ok (.ok ()) atIssue ∧
      (perform step).run atIssue = .error path after := by
  obtain ⟨done, issued, remaining, atIssue, ordered, earlier, cut⟩ :=
    forM_firstExit (steps count) perform (exit := .ok (step, path)) stopped
  change (tagStop perform issued).run atIssue = .error (step, path) after at cut
  simp only [tagStop, ExceptT.run] at cut
  cases call : perform issued atIssue with
  | ok value heap => simp [call] at cut
  | error reason heap =>
    rw [call] at cut
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := EStateM.Result.error.inj cut
    exact ⟨done, remaining, atIssue, ordered, earlier, call⟩

/-- A returned diagnostic also fixes the first failing step and the exact
heap reached by its successful predecessors. An earlier stop or ordinary
error cannot be replayed as another issue. -/
theorem run_firstReturnedError {image : Type} {count : Nat}
    {perform : Step → ExceptT IO.Error (EStateM FilePath image) Unit}
    {before after : image} {cause : IO.Error}
    (failed : (run count (tagStop perform)).run before = .ok (.error cause) after) :
    ∃ done step remaining atIssue, steps count = done ++ step :: remaining ∧
      (done.forM perform).run before = .ok (.ok ()) atIssue ∧
      (perform step).run atIssue = .ok (.error cause) after := by
  obtain ⟨done, issued, remaining, atIssue, ordered, earlier, cut⟩ :=
    forM_firstExit (steps count) perform (exit := .error cause) failed
  change (tagStop perform issued).run atIssue = .ok (.error cause) after at cut
  simp only [tagStop, ExceptT.run] at cut
  cases call : perform issued atIssue with
  | error reason heap => simp [call] at cut
  | ok value heap =>
    rw [call] at cut
    obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj cut
    exact ⟨done, issued, remaining, atIssue, ordered, earlier, call⟩

private theorem runSteps_nodup (count : Nat) : (runSteps count).Nodup := by
  induction count with
  | zero => simp [runSteps]
  | succ count ih =>
    have order : runSteps (count + 1) = runSteps count ++ [.writeRun count, .syncRun count] := by
      simp [runSteps, List.range_succ]
    rw [order, List.nodup_append]
    refine ⟨ih, by simp, ?_⟩
    intro step earlier other pair same
    subst other
    simp [runSteps, List.mem_flatMap] at earlier
    obtain ⟨index, bounded, same | same⟩ := earlier
    all_goals
      subst step
      simp [Nat.ne_of_lt bounded] at pair

private theorem steps_nodup (count : Nat) : (steps count).Nodup := by
  simp only [steps, List.append_assoc, List.singleton_append, List.nodup_append]
  refine ⟨runSteps_nodup count, by decide, ?_⟩
  intro step earlier other later same
  subst other
  simp [runSteps, List.mem_flatMap] at earlier
  obtain ⟨index, _, same | same⟩ := earlier
  all_goals subst step; simp [Publication.steps] at later

private theorem samePrefix {count : Nat} {step : Step} {done remaining earlier later : List Step}
    (observed : steps count = done ++ step :: remaining)
    (canonical : steps count = earlier ++ step :: later) :
    done = earlier := by
  have first : (steps count)[done.length]? = some step := by
    rw [observed]
    simp
  have second : (steps count)[earlier.length]? = some step := by
    rw [canonical]
    simp
  have within : done.length < (steps count).length := by simp [observed]
  have same := (steps_nodup count).eq_of_getElem?_eq within (first.trans second.symm)
  calc
    done = (steps count).take done.length := by simp [observed]
    _ = (steps count).take earlier.length := congrArg ((steps count).take ·) same
    _ = earlier := by simp [canonical]

/-- Identify the canonical earlier run pairs and selected write from the
position of the issued run sync. -/
theorem prefixBeforeRunSync {count index : Nat} {done remaining : List Step}
    (ordered : steps count = done ++ .syncRun index :: remaining) :
    index < count ∧ done = runSteps index ++ [.writeRun index] := by
  have present : .syncRun index ∈ steps count := by rw [ordered]; simp
  have within : index < count := by
    simpa [steps, runSteps, List.mem_flatMap, Publication.steps] using present
  obtain ⟨later, canonical⟩ := steps_atRunPair within
  refine ⟨within, samePrefix ordered (remaining := remaining) (later := later) ?_⟩
  simpa [List.append_assoc] using canonical

/-- The first directory barrier immediately follows all run pairs. -/
theorem prefixBeforeRunsDirectory {count : Nat} {done remaining : List Step}
    (ordered : steps count = done ++ .syncRunsDirectory :: remaining) :
    done = runSteps count := by
  have canonical : steps count =
      runSteps count ++ .syncRunsDirectory :: Publication.steps.map Step.manifest := by
    simp [steps, List.append_assoc]
  exact samePrefix ordered canonical

theorem prefixBeforeManifestSync {count : Nat} {done remaining : List Step}
    (ordered : steps count = done ++ .manifest .syncStaged :: remaining) :
    done = (runSteps count ++ [.syncRunsDirectory]) ++ [.manifest .writeStaged] := by
  apply samePrefix ordered (later := [.manifest .renameStaged, .manifest .syncDirectory])
  simp [steps, Publication.steps, List.append_assoc]

/-- The manifest rename follows the successful staged file sync. -/
theorem prefixBeforeManifestRename {count : Nat} {done remaining : List Step}
    (ordered : steps count = done ++ .manifest .renameStaged :: remaining) :
    done = runSteps count ++ [.syncRunsDirectory, .manifest .writeStaged, .manifest .syncStaged] := by
  apply samePrefix ordered (later := [.manifest .syncDirectory])
  simp [steps, Publication.steps, List.append_assoc]

/-- The manifest directory barrier follows the returned rename. -/
theorem prefixBeforeManifestDirectory {count : Nat} {done remaining : List Step}
    (ordered : steps count = done ++ .manifest .syncDirectory :: remaining) :
    done = (runSteps count ++ [.syncRunsDirectory, .manifest .writeStaged, .manifest .syncStaged]) ++
      [.manifest .renameStaged] := by
  apply samePrefix ordered (later := [])
  simp [steps, Publication.steps, List.append_assoc]

/-- A returned prefix ending in a step determines that step's entry heap. -/
theorem returnedLastStep {image : Type} (perform : Step → ExceptT IO.Error (EStateM FilePath image) Unit)
    (priorSteps : List Step) (last : Step) {before after : image}
    (returned : ((priorSteps ++ [last]).forM perform).run before = .ok (.ok ()) after) :
    ∃ atLast, (priorSteps.forM perform).run before = .ok (.ok ()) atLast ∧
      (perform last).run atLast = .ok (.ok ()) after := by
  rw [List.forM_eq_forM, List.forM_append] at returned
  change (ExceptT.bind (priorSteps.forM perform)
    (fun _ => ExceptT.bind (perform last) (fun _ => pure ()))).run before = _ at returned
  rw [run_bind] at returned
  cases ran : (priorSteps.forM perform).run before with
  | error rejected reached => rw [ran] at returned; cases returned
  | ok result atLast =>
    rw [ran] at returned
    cases result with
    | error cause => cases returned
    | ok value =>
      cases value
      change (ExceptT.bind (perform last) (fun _ => pure ())).run atLast = _ at returned
      rw [run_bind] at returned
      refine ⟨atLast, rfl, ?_⟩
      cases wrote : (perform last).run atLast with
      | error rejected reached => rw [wrote] at returned; cases returned
      | ok result reached =>
        rw [wrote] at returned
        cases result with
        | error cause => cases returned
        | ok value =>
          cases value
          exact congrArg (EStateM.Result.ok (Except.ok () : Except IO.Error Unit))
            (EStateM.Result.ok.inj returned).2

end Alvoki.Storage.CheckpointPublication

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication

private abbrev returned {image α : Type} (call : EStateM IO.Error image α) :
    ExceptT IO.Error (EStateM FilePath image) α :=
  fun before => match call before with
    | .ok result reached => .ok (.ok result) reached
    | .error cause reached => .ok (.error cause) reached

/-- Use the production dispatcher with ordinary write and rename
callbacks and a sync callback that can stop without a return. -/
def CheckpointFileCallbacks.performUntilSyncStop {image : Type} (calls : CheckpointFileCallbacks image)
    (sync : Array FilePath → ExceptT IO.Error (EStateM FilePath image) Unit)
    (directory : DiskDirectory) (next : Installed) (manifest : ByteArray) : Step →
      ExceptT IO.Error (EStateM FilePath image) Unit :=
  performCheckpointFileStep directory next.generation next.table.runs.toArray (directory.file .stagedManifest)
    manifest (fun found => match found with
      | some run => pure run
      | none => throw (IO.userError "checkpoint run index is out of bounds"))
    (fun path bytes => returned (calls.writeRun path bytes))
    (fun path bytes => returned (calls.writeStaged path bytes)) sync
    (fun source target => returned (calls.rename source target))

/-- A returned write step records the actual write result and cache. -/
theorem CheckpointFileCallbacks.performRunWriteUntilSyncStop {image : Type}
    (calls : CheckpointFileCallbacks image) (sync : Array FilePath → ExceptT IO.Error (EStateM FilePath image) Unit)
    (directory : DiskDirectory) (next : Installed) (manifest : ByteArray) {index : Nat}
    {run : Compaction.CheckedRun} (found : next.table.runs.toArray[index]? = some run) (before : image) :
    (calls.performUntilSyncStop sync directory next manifest (.writeRun index)).run before =
      match calls.writeRun (directory.file (.run next.generation index)) run.run.bytes before with
      | .ok value after => .ok (.ok value) after
      | .error cause after => .ok (.error cause) after := by
  simp only [performUntilSyncStop, performCheckpointFileStep, found, Bind.bind,
    ExceptT.bind, ExceptT.bindCont, ExceptT.run, ExceptT.mk, EStateM.bind, Pure.pure, ExceptT.pure, EStateM.pure,
    returned]
  cases calls.writeRun (directory.file (.run next.generation index)) run.run.bytes before <;> rfl

theorem CheckpointFileCallbacks.performManifestWriteUntilSyncStop {image : Type}
    (calls : CheckpointFileCallbacks image) (sync : Array FilePath → ExceptT IO.Error (EStateM FilePath image) Unit)
    (directory : DiskDirectory) (next : Installed) (manifest : ByteArray) (before : image) :
    (calls.performUntilSyncStop sync directory next manifest (.manifest .writeStaged)).run before =
      match calls.writeStaged (directory.file .stagedManifest) manifest before with
      | .ok value after => .ok (.ok value) after
      | .error cause after => .ok (.error cause) after := by
  simp only [performUntilSyncStop, performCheckpointFileStep, Publication.performReplacement, ExceptT.run, returned]
  cases calls.writeStaged (directory.file .stagedManifest) manifest before <;> rfl

theorem CheckpointFileCallbacks.performManifestRenameUntilSyncStop {image : Type}
    (calls : CheckpointFileCallbacks image) (sync : Array FilePath → ExceptT IO.Error (EStateM FilePath image) Unit)
    (directory : DiskDirectory) (next : Installed) (manifest : ByteArray) (before : image) :
    (calls.performUntilSyncStop sync directory next manifest (.manifest .renameStaged)).run before =
      match calls.rename (directory.file .stagedManifest) (directory.file .manifest) before with
      | .ok value after => .ok (.ok value) after
      | .error cause after => .ok (.error cause) after := by
  simp only [performUntilSyncStop, performCheckpointFileStep, Publication.performReplacement, ExceptT.run, returned]
  cases calls.rename (directory.file .stagedManifest) (directory.file .manifest) before <;> rfl

end Alvoki.Storage.DiskSession
