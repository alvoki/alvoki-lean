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

private theorem forM_firstStop {image : Type}
    (actions : List Step) (perform : Step → ExceptT IO.Error (EStateM FilePath image) Unit)
    {before after : image} {step : Step} {path : FilePath}
    (stopped : (actions.forM (tagStop perform)).run before = .error (step, path) after) :
    ∃ done remaining atIssue, actions = done ++ step :: remaining ∧
      (done.forM perform).run before = .ok (.ok ()) atIssue ∧
      (perform step).run atIssue = .error path after := by
  induction actions generalizing before with
  | nil =>
    change EStateM.Result.ok (Except.ok ()) before = .error (step, path) after at stopped
    cases stopped
  | cons issued tail ih =>
    change (ExceptT.bind (tagStop perform issued) (fun _ => tail.forM (tagStop perform))).run before = _ at stopped
    rw [run_bind] at stopped
    cases call : (perform issued).run before with
    | error stoppedPath reached =>
      have tagged : (tagStop perform issued).run before = .error (issued, stoppedPath) reached := by
        change perform issued before = _ at call
        simp only [tagStop, ExceptT.run, call]
      rw [tagged] at stopped
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := EStateM.Result.error.inj stopped
      exact ⟨[], tail, before, rfl, rfl, call⟩
    | ok returned reached =>
      have tagged : (tagStop perform issued).run before = .ok returned reached := by
        change perform issued before = _ at call
        simp only [tagStop, ExceptT.run, call]
      rw [tagged] at stopped
      cases returned with
      | error cause => cases stopped
      | ok value =>
        obtain ⟨done, remaining, atIssue, order, returnedPrefix, cut⟩ := ih stopped
        refine ⟨issued :: done, remaining, atIssue, congrArg (List.cons issued) order, ?_, cut⟩
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
      (perform step).run atIssue = .error path after :=
  forM_firstStop (steps count) perform stopped

/-- A successful returned prefix followed by a stopped callback is
enough to run the whole schedule to the same outer stop and reached heap. -/
theorem run_stopsAt {image : Type} {count : Nat}
    {perform : Step → ExceptT IO.Error (EStateM FilePath image) Unit}
    {done remaining : List Step} {step : Step} {path : FilePath} {before atIssue after : image}
    (ordered : steps count = done ++ step :: remaining)
    (completed : (done.forM perform).run before = .ok (.ok ()) atIssue)
    (stopped : (perform step).run atIssue = .error path after) :
    (run count (tagStop perform)).run before = .error (step, path) after := by
  change ((steps count).forM (tagStop perform)).run before = _
  rw [ordered]
  clear ordered
  induction done generalizing before with
  | nil =>
    have tagged : (tagStop perform step).run before = .error (step, path) after := by
      have same := (EStateM.Result.ok.inj completed).2
      rw [← same] at stopped
      change perform step before = _ at stopped
      simp only [tagStop, ExceptT.run, stopped]
    change (ExceptT.bind (tagStop perform step) (fun _ => remaining.forM (tagStop perform))).run before = _
    rw [run_bind, tagged]
  | cons prev rest ih =>
    change (ExceptT.bind (perform prev) (fun _ => rest.forM perform)).run before = _ at completed
    rw [run_bind] at completed
    cases call : (perform prev).run before with
    | error reason reached => rw [call] at completed; cases completed
    | ok result reached =>
      rw [call] at completed
      cases result with
      | error cause => cases completed
      | ok value =>
        have tagged : (tagStop perform prev).run before = .ok (.ok value) reached := by
          change perform prev before = _ at call
          simp only [tagStop, ExceptT.run, call]
        change (ExceptT.bind (tagStop perform prev) (fun _ =>
          (rest ++ step :: remaining).forM (tagStop perform))).run before = _
        rw [run_bind, tagged]
        exact ih completed

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

end Alvoki.Storage.CheckpointPublication

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication

private def returned {image α : Type} (call : EStateM IO.Error image α) :
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

variable {image : Type} (calls : CheckpointFileCallbacks image)
  (sync : Array FilePath → ExceptT IO.Error (EStateM FilePath image) Unit)
  (directory : DiskDirectory) (next : Installed) (manifest : ByteArray)
  {before after : image} {path : FilePath}

/-- A stopped run sync reached the same selected write and prior run
pairs in the complete file schedule. Its callback gets the canonical run path. -/
theorem CheckpointFileCallbacks.firstRunSyncStop {index : Nat}
    (stopped : (run next.table.runs.length
      (tagStop (calls.performUntilSyncStop sync directory next manifest))).run before = .error (.syncRun index, path) after) :
    let done := runSteps index ++ [.writeRun index]
    index < next.table.runs.length ∧ ∃ remaining atIssue,
      steps next.table.runs.length = done ++ .syncRun index :: remaining ∧
      (done.forM (calls.performUntilSyncStop sync directory next manifest)).run before = .ok (.ok ()) atIssue ∧
      (sync #[directory.file (.run next.generation index)]).run atIssue = .error path after := by
  obtain ⟨done, remaining, atIssue, ordered, returnedPrefix, cut⟩ := run_firstStop stopped
  obtain ⟨within, rfl⟩ := prefixBeforeRunSync ordered
  exact ⟨within, remaining, atIssue, ordered, returnedPrefix, cut⟩

/-- A stopped first directory sync reached all returned run pairs
before the canonical directory callback. The manifest suffix is unreached. -/
theorem CheckpointFileCallbacks.firstRunsDirectoryStop
    (stopped : (run next.table.runs.length
      (tagStop (calls.performUntilSyncStop sync directory next manifest))).run before = .error (.syncRunsDirectory, path) after) :
    ∃ atIssue,
      ((runSteps next.table.runs.length).forM (calls.performUntilSyncStop sync directory next manifest)).run before =
        .ok (.ok ()) atIssue ∧ (sync #[directory.path]).run atIssue = .error path after := by
  obtain ⟨done, _, atIssue, ordered, returnedPrefix, cut⟩ := run_firstStop stopped
  exact ⟨atIssue, prefixBeforeRunsDirectory ordered ▸ returnedPrefix, cut⟩

end Alvoki.Storage.DiskSession
