import Alvoki.Experiments.L0.Trace

namespace ExperimentalL0.Execution

variable {ops : Components (StorageM σ)} {selected : σ → Selected}

theorem Run.writeOk (prior : Run events (some session) (selected s))
    (laws : ComponentEffects ops selected) (ran : write ops session change s = .ok next after) :
    Run (events ++ [.written change]) (some next) (selected after) := by
  refine .written prior (fun _ installed => ?_)
  have effect := write_refines laws s session installed change
  rwa [ran] at effect

theorem Run.writeInterrupted (prior : Run events (some session) (selected s))
    (laws : ComponentEffects ops selected) (ran : write ops session change s = result) :
    Run (events ++ [.writeUncertain change]) none
      (selected (match result with | .ok _ after | .error _ after => after)) := by
  refine .writeUncertain prior (fun _ installed => ?_)
  have effect := write_refines laws s session installed change
  rw [ran] at effect
  cases result with
  | ok value after =>
    obtain ⟨d, _, _⟩ := effect
    exact Or.inr ⟨d⟩
  | error error after => exact effect

theorem Run.onlineInstalled (prior : Run events (some session) image) :
    ∃ history, Installed session image history := by
  obtain ⟨_ | _, _, represented⟩ := prior.refines
  · obtain ⟨_, history, equality, _, installed⟩ := represented
    cases equality
    exact ⟨history, installed⟩
  · have impossible := represented.1
    contradiction

theorem Run.getOk (prior : Run events (some session) (selected s))
    (effect : ∀ history, Installed session (selected s) history →
      match get ops session key s with
      | .ok value after => value = denote history key ∧ selected after = selected s
      | .error _ after => selected after = selected s)
    (ran : get ops session key s = .ok value after) :
    Run (events ++ [.got key value]) (some session) (selected after) := by
  obtain ⟨_, witness⟩ := prior.onlineInstalled
  have frame := effect _ witness
  rw [ran] at frame
  rw [frame.2]
  refine .got prior (fun history installed => ?_)
  have read := effect history installed
  rw [ran] at read
  exact read.1

theorem Run.getError (prior : Run events (some session) (selected s))
    (effect : ∀ history, Installed session (selected s) history →
      match get ops session key s with
      | .ok value after => value = denote history key ∧ selected after = selected s
      | .error _ after => selected after = selected s)
    (ran : get ops session key s = .error error after) :
    Run events (some session) (selected after) := by
  obtain ⟨_, installed⟩ := prior.onlineInstalled
  have frame := effect _ installed
  rw [ran] at frame
  exact frame ▸ prior

theorem Run.flushObserved (prior : Run events (some session) (selected s))
    (laws : FlushEffects ops selected) (ran : flush ops session s = result)
    (observed : FlushObservation result) :
    Run (events ++ [observed.event]) observed.session
      (selected (match result with | .ok _ after | .error _ after => after)) := by
  have effect (history : Rows) (installed : Installed session (selected s) history) :
      match result with
      | .ok next after => Installed next (selected after) history
      | .error _ after => Nonempty (Durable (selected after) history) := by
    have reached := flush_refines laws s session installed
    rw [ran] at reached
    cases result <;> exact reached
  cases observed with
  | delivered => exact .flushed prior effect
  | reportedError => exact .flushUncertain prior effect
  | replyLost =>
    exact .flushUncertain prior (fun history installed => ⟨(effect history installed).choose⟩)
  | interrupted =>
    cases result with
    | ok value after =>
      exact .flushUncertain prior (fun history installed => ⟨(effect history installed).choose⟩)
    | error error after => exact .flushUncertain prior effect

theorem Run.recoverOk (prior : Run events none (selected s))
    (laws : RecoveryEffects ops selected) (ran : recover ops s = .ok session after) :
    Run (events ++ [.reopened]) (some session) (selected after) := by
  refine .reopened prior (fun _ durable => ?_)
  have effect := recover_refines laws s durable
  rw [ran] at effect
  exact effect.2

theorem Run.recoverError (prior : Run events none (selected s))
    (laws : RecoveryEffects ops selected) (ran : recover ops s = .error error after) :
    Run (events ++ [.openFailed]) none (selected after) := by
  refine .openFailed prior (fun _ durable => ?_)
  have effect := recover_refines laws s durable
  rw [ran] at effect
  exact ⟨effect ▸ durable⟩

end ExperimentalL0.Execution
