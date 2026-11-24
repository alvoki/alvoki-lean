import Alvoki.Storage.Publication.RunCollection
import Alvoki.Storage.Disk.RunUnlinkEffects

namespace Alvoki.Storage.CheckpointPublication

/-- Existing names take the modeled unlink effect. An accepted ENOENT on
an already absent owned name leaves earlier crash possibilities alone. -/
def RunUnlinkImage.applyCollectionStep (image : RunUnlinkImage) : RunCollection.Step RunAddress → RunUnlinkImage
  | .unlink name =>
    if image.visible name.1 name.2 = none then image else image.unlink name
  | .syncDirectory => image.syncDirectory

/-- The primitive's report supplies its modeled effect. An error can keep
the old image or have the full effect of the reported operation. Payloads
are already individually durable. The barrier concerns directory names. -/
def RunUnlinkEffectContract {error : Type}
    (perform : RunCollection.Step RunAddress → EStateM error RunUnlinkImage Unit) : Prop :=
  ∀ action before, match perform action before with
    | .ok _ after => after = before.applyCollectionStep action
    | .error _ after => after = before ∨ after = before.applyCollectionStep action

/-- Connect raw unlink and directory-sync reports to the shared path
dispatcher. Accepted ENOENT requires the owned name already absent and
leaves the namespace unchanged. An unlink error can follow removal. -/
theorem RunUnlinkEffectContract.ofPaths {path : Type}
    (removeFile : path → EStateM IO.Error RunUnlinkImage (Except IO.Error Unit))
    (syncDirectory : path → EStateM IO.Error RunUnlinkImage Unit)
    (file : RunAddress → path) (directory : path)
    (unlinks : ∀ name before, match removeFile (file name) before with
      | .error _ after => after = before ∨ after = before.applyCollectionStep (.unlink name)
      | .ok (.ok _) after => after = before.applyCollectionStep (.unlink name)
      | .ok (.error cause) after => match RunCollection.ownedUnlinkResult (.error cause) with
        | .ok _ => before.visible name.1 name.2 = none ∧ after = before
        | .error _ => after = before ∨ after = before.applyCollectionStep (.unlink name))
    (syncs : ∀ before, match syncDirectory directory before with
      | .ok _ after => after = before.syncDirectory
      | .error _ after => after = before ∨ after = before.syncDirectory) :
    RunUnlinkEffectContract (RunCollection.performPaths removeFile syncDirectory
      (fun error before => .error error before) file directory) := by
  intro action before
  cases action with
  | syncDirectory =>
    have synced := syncs before
    simp only [RunCollection.performPaths, RunUnlinkImage.applyCollectionStep]
    cases reported : syncDirectory directory before <;> simpa only [reported] using synced
  | unlink name =>
    simp only [RunCollection.performPaths, Bind.bind, EStateM.bind]
    have observed := unlinks name before
    cases reported : removeFile (file name) before with
    | error cause after =>
      rw [reported] at observed
      exact observed
    | ok result after =>
      rw [reported] at observed
      cases result with
      | ok success => cases success; exact observed
      | error cause =>
        change (match RunCollection.ownedUnlinkResult (.error cause) with
          | .ok _ => before.visible name.1 name.2 = none ∧ after = before
          | .error _ => after = before ∨ after = before.applyCollectionStep (.unlink name)) at observed
        cases accepted : RunCollection.ownedUnlinkResult (.error cause) with
        | ok success =>
          cases success
          rw [accepted] at observed
          simp [accepted, Pure.pure, EStateM.pure, RunUnlinkImage.applyCollectionStep,
            observed.1, observed.2]
        | error propagated =>
          simpa [accepted] using observed

private theorem foldlM_collectionSteps (before : RunUnlinkImage) (actions : List (RunCollection.Step RunAddress)) :
    actions.foldlM (fun state action => some (state.applyCollectionStep action)) before =
      some (actions.foldl RunUnlinkImage.applyCollectionStep before) := by
  induction actions generalizing before with
  | nil => rfl
  | cons action rest later =>
    simpa only [List.foldlM_cons, List.foldl_cons, Bind.bind, Option.bind] using
      later (before.applyCollectionStep action)

private theorem RunUnlinkImage.applyCollectionStep_visible (image : RunUnlinkImage) (name : RunAddress) :
    (image.applyCollectionStep (.unlink name)).visible = (image.unlink name).visible := by
  simp only [applyCollectionStep]
  split
  · rename_i absent
    funext generation index
    change image.visible generation index = image.visible.eraseName name generation index
    by_cases named : (generation, index) = name
    · obtain rfl := named.symm
      simpa [RunFiles.eraseName] using absent
    · simp [RunFiles.eraseName, named]
  · rfl

private theorem foldl_collection_visible {before other : RunUnlinkImage} (names : List RunAddress)
    (visible : before.visible = other.visible) :
    ((names.map RunCollection.Step.unlink).foldl RunUnlinkImage.applyCollectionStep before).visible =
      (names.foldl RunUnlinkImage.unlink other).visible := by
  induction names generalizing before other with
  | nil => exact visible
  | cons name rest later =>
    simp only [List.map_cons, List.foldl_cons]
    exact later ((before.applyCollectionStep_visible name).trans
      (congrArg (fun names => names.eraseName name) visible))

private theorem foldl_collectionSteps (before : RunUnlinkImage) (names : List RunAddress) :
    (RunCollection.steps names).foldl RunUnlinkImage.applyCollectionStep before = before.finishPass names := by
  simp only [RunCollection.steps, List.foldl_append, List.foldl_cons, List.foldl_nil, RunUnlinkImage.finishPass,
    RunUnlinkImage.applyCollectionStep, RunUnlinkImage.syncDirectory]
  exact congrArg RunUnlinkImage.settled (foldl_collection_visible names rfl)

/-- Success of the actual finite schedule completes the durable pass. A
reported failure returns exactly the effect of a prefix, which can include
the operation that returned an error. -/
theorem runUnlinkSchedule_outcome {error : Type} (names : List RunAddress) (before : RunUnlinkImage)
    (perform : RunCollection.Step RunAddress → EStateM error RunUnlinkImage Unit)
    (reports : RunUnlinkEffectContract perform) :
    match RunCollection.run names perform before with
    | .ok _ after => after = before.finishPass names
    | .error _ after => ∃ cut, after = ((RunCollection.steps names).take cut).foldl RunUnlinkImage.applyCollectionStep before := by
  have outcomes := Publication.run_effects_outcome (fun state action => some (state.applyCollectionStep action))
    perform (by
      intro action state
      have report := reports action state
      cases applied : perform action state <;> simpa only [applied, Option.some.injEq, eq_comm] using report)
    (RunCollection.steps names) before
  unfold RunCollection.run
  cases applied : ((RunCollection.steps names).forM perform) before with
  | ok _ after =>
    rw [applied, foldlM_collectionSteps] at outcomes
    exact (Option.some.inj outcomes).symm.trans (foldl_collectionSteps before names)
  | error _ after =>
    rw [applied] at outcomes
    obtain ⟨cut, outcome⟩ := outcomes
    rw [foldlM_collectionSteps] at outcome
    exact ⟨cut, (Option.some.inj outcome).symm⟩

private theorem RunUnlinkRetry.collectionSteps {approved : List RunAddress} {initial before : RunUnlinkImage}
    (prior : RunUnlinkRetry approved initial before) (actions : List (RunCollection.Step RunAddress))
    (eligible : ∀ action ∈ actions, match action with | .unlink name => name ∈ approved | .syncDirectory => True) :
    RunUnlinkRetry approved initial (actions.foldl RunUnlinkImage.applyCollectionStep before) := by
  induction actions generalizing before with
  | nil => exact prior
  | cons action rest later =>
    have chosen := eligible action List.mem_cons_self
    have effect : RunUnlinkRetry approved initial (before.applyCollectionStep action) := by
      cases action with
      | unlink name =>
        simp only [RunUnlinkImage.applyCollectionStep]
        split
        · exact prior
        · exact .unlink prior chosen
      | syncDirectory => exact .sync prior
    exact later effect (fun next member => eligible next (List.mem_cons_of_mem _ member))

/-- Every reported result of the ordered schedule extends the admissible
retry trace. Subsequent crashes therefore use the proved namespace and
checkpoint-preservation invariants. -/
theorem RunUnlinkRetry.runSchedule {error : Type} {approved : List RunAddress} {initial before : RunUnlinkImage}
    (prior : RunUnlinkRetry approved initial before) (names : List RunAddress)
    (eligible : ∀ name ∈ names, name ∈ approved)
    (perform : RunCollection.Step RunAddress → EStateM error RunUnlinkImage Unit)
    (reports : RunUnlinkEffectContract perform) :
    match RunCollection.run names perform before with
    | .ok _ after | .error _ after => RunUnlinkRetry approved initial after := by
  have allowed : ∀ action ∈ RunCollection.steps names,
      match action with | .unlink name => name ∈ approved | .syncDirectory => True := by
    intro action present
    unfold RunCollection.steps at present
    rcases List.mem_append.mp present with unlink | barrier
    · obtain ⟨name, chosen, rfl⟩ := List.mem_map.mp unlink
      exact eligible name chosen
    · obtain rfl := List.mem_singleton.mp barrier
      trivial
  have outcome := runUnlinkSchedule_outcome names before perform reports
  cases ran : RunCollection.run names perform before with
  | ok _ after =>
    rw [ran] at outcome
    rw [outcome, ← foldl_collectionSteps]
    exact prior.collectionSteps _ allowed
  | error _ after =>
    rw [ran] at outcome
    obtain ⟨cut, rfl⟩ := outcome
    exact prior.collectionSteps _ (fun action chosen => allowed action (List.mem_of_mem_take chosen))

end Alvoki.Storage.CheckpointPublication
