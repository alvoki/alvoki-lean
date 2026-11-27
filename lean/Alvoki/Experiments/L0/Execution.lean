import Alvoki.Experiments.L0.Trace
import Alvoki.Experiments.L0.ModelRefinement

namespace ExperimentalL0
namespace Model

private def reached : EStateM.Result String Image α → Image
  | .ok _ image | .error _ image => image

/-- Finite executions of the actual operation schedule in the component
interpreter. A completed component effect can lose its client reply. -/
inductive Run : List Event → Option Session → Image → Prop where
  | initial : Run [] none {}
  | written : Run events (some session) image →
      write (components faults) session change image = .ok next after →
      Run (events ++ [.written change]) (some next) after
  | writeUncertain : Run events (some session) image →
      write (components faults) session change image = result →
      Run (events ++ [.writeUncertain change]) none (reached result)
  | got : Run events (some session) image →
      get (components faults) session key image = .ok value image →
      Run (events ++ [.got key value]) (some session) image
  | flushed : Run events (some session) image →
      flush (components faults) session image = .ok next after →
      Run (events ++ [.flushed]) (some next) after
  | flushUncertain : Run events (some session) image →
      flush (components faults) session image = result →
      Run (events ++ [.flushUncertain]) none (reached result)
  | reopened : Run events none image →
      recover (components faults) image = .ok session after →
      Run (events ++ [.reopened]) (some session) after
  | openFailed : Run events none image →
      recover (components faults) image = .error error after →
      Run (events ++ [.openFailed]) none after
  | stop : Run events session image → Run (events ++ [.stop]) none image

private theorem initial_durable : Nonempty (Durable ({} : Image).selected []) :=
  ⟨⟨[], [], rfl, Nat.le_refl _, rfl, rfl, List.nodup_nil, [], rfl, fun _ => rfl, by simp⟩⟩

/-- Interpret the concrete schedule using the generic operation theorems,
then retain only the selected image for trace refinement. -/
theorem Run.projects (run : Run events session image) :
    Execution.Run events session image.selected := by
  induction run with
  | initial => exact .initial initial_durable
  | @written _ session image faults change next after _ ran ih =>
    refine .written ih fun _ installed => ?_
    have effect := write_refines (componentLaws faults) image session installed change
    rw [ran] at effect
    exact effect
  | @writeUncertain _ session image faults change result _ ran ih =>
    refine .writeUncertain ih fun _ installed => ?_
    have effect := write_refines (componentLaws faults) image session installed change
    rw [ran] at effect
    cases result with
    | ok next after =>
      obtain ⟨d, _, _⟩ := effect
      exact Or.inr ⟨d⟩
    | error error after => exact effect
  | @got _ session image faults key value _ ran ih =>
    refine .got ih fun _ installed => ?_
    have read := get_refines (componentLaws faults) image session installed key
    rw [ran] at read
    exact read.1
  | @flushed _ session image faults next after _ ran ih =>
    refine .flushed ih fun _ installed => ?_
    have effect := flush_refines (componentLaws faults) image session installed
    rw [ran] at effect
    exact effect
  | @flushUncertain _ session image faults result _ ran ih =>
    refine .flushUncertain ih fun _ installed => ?_
    have effect := flush_refines (componentLaws faults) image session installed
    rw [ran] at effect
    cases result with
    | ok next after =>
      obtain ⟨d, _, _⟩ := effect
      exact ⟨d⟩
    | error error after => exact effect
  | @reopened _ image faults session after _ ran ih =>
    refine .reopened ih fun _ durable => ?_
    have effect := recover_refines (componentLaws faults) image durable
    rw [ran] at effect
    exact effect.2
  | @openFailed _ image faults error after _ ran ih =>
    refine .openFailed ih fun _ durable => ?_
    have effect := recover_refines (componentLaws faults) image durable
    rw [ran] at effect
    exact ⟨effect ▸ durable⟩
  | stop _ ih => exact .stop ih

theorem Run.refines (run : Run events session image) :
    ∃ state, Client.Allows events state ∧ Execution.Represents session image.selected state :=
  run.projects.refines

theorem Run.healthy_open (run : Run events none image) :
    ∃ session, Run (events ++ [.reopened]) (some session) image := by
  obtain ⟨_ | _, _, represented⟩ := run.refines
  · obtain ⟨_, _, impossible, _, _⟩ := represented
    contradiction
  · obtain ⟨_, _, _, ⟨d⟩⟩ := represented
    exact ⟨_, .reopened run (recover_healthy image {} d rfl rfl)⟩

end Model
end ExperimentalL0
