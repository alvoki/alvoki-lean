import Alvoki.Experiments.L0.Trace

namespace ExperimentalL0.Execution

variable {ops : Components (StorageM σ)} {selected : σ → Selected}

theorem Run.writeOk (prior : Run events (some session) (selected s))
    (laws : ComponentLaws ops selected) (ran : write ops session change s = .ok next after) :
    Run (events ++ [.written change]) (some next) (selected after) := by
  refine .written prior (fun _ installed => ?_)
  have effect := write_refines laws s session installed change
  rwa [ran] at effect

theorem Run.writeInterrupted (prior : Run events (some session) (selected s))
    (laws : ComponentLaws ops selected) (ran : write ops session change s = result) :
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

private theorem onlineInstalled (prior : Run events (some session) image) :
    ∃ history, Installed session image history := by
  obtain ⟨_ | _, _, represented⟩ := prior.refines
  · obtain ⟨_, history, equality, _, installed⟩ := represented
    cases equality
    exact ⟨history, installed⟩
  · have impossible := represented.1
    contradiction

theorem Run.getOk (prior : Run events (some session) (selected s))
    (laws : ComponentLaws ops selected) (ran : get ops session key s = .ok value after) :
    Run (events ++ [.got key value]) (some session) (selected after) := by
  obtain ⟨_, witness⟩ := onlineInstalled prior
  have frame := get_refines laws s session witness key
  rw [ran] at frame
  rw [frame.2]
  refine .got prior (fun _ installed => ?_)
  have effect := get_refines laws s session installed key
  rw [ran] at effect
  exact effect.1

theorem Run.getError (prior : Run events (some session) (selected s))
    (laws : ComponentLaws ops selected) (ran : get ops session key s = .error error after) :
    Run events (some session) (selected after) := by
  obtain ⟨_, installed⟩ := onlineInstalled prior
  have frame := get_refines laws s session installed key
  rw [ran] at frame
  exact frame ▸ prior

theorem Run.flushOk (prior : Run events (some session) (selected s))
    (laws : ComponentLaws ops selected) (ran : flush ops session s = .ok next after) :
    Run (events ++ [.flushed]) (some next) (selected after) := by
  refine .flushed prior (fun _ installed => ?_)
  have effect := flush_refines laws s session installed
  rwa [ran] at effect

theorem Run.flushInterrupted (prior : Run events (some session) (selected s))
    (laws : ComponentLaws ops selected) (ran : flush ops session s = result) :
    Run (events ++ [.flushUncertain]) none
      (selected (match result with | .ok _ after | .error _ after => after)) := by
  refine .flushUncertain prior (fun _ installed => ?_)
  have effect := flush_refines laws s session installed
  rw [ran] at effect
  cases result with
  | ok value after =>
    obtain ⟨d, _, _⟩ := effect
    exact ⟨d⟩
  | error error after => exact effect

theorem Run.recoverOk (prior : Run events none (selected s))
    (laws : ComponentLaws ops selected) (ran : recover ops s = .ok session after) :
    Run (events ++ [.reopened]) (some session) (selected after) := by
  refine .reopened prior (fun _ durable => ?_)
  have effect := recover_refines laws s durable
  rw [ran] at effect
  exact effect.2

theorem Run.recoverError (prior : Run events none (selected s))
    (laws : ComponentLaws ops selected) (ran : recover ops s = .error error after) :
    Run (events ++ [.openFailed]) none (selected after) := by
  refine .openFailed prior (fun _ durable => ?_)
  have effect := recover_refines laws s durable
  rw [ran] at effect
  exact ⟨effect ▸ durable⟩

end ExperimentalL0.Execution
