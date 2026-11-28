import Alvoki.Experiments.L0.ScheduleSteps
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
  | flushObserved : Run events (some session) image →
      flush (components faults) session image = result →
      (observed : FlushObservation result) →
      Run (events ++ [observed.event]) observed.session (reached result)
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
  | @written _ _ _ faults _ _ _ _ ran ih =>
    exact ih.writeOk (componentLaws faults).toComponentEffects ran
  | @writeUncertain _ _ _ faults _ result _ ran ih =>
    cases result <;> exact ih.writeInterrupted (componentLaws faults).toComponentEffects ran
  | @got _ _ _ faults _ _ _ ran ih =>
    exact ih.getOk (fun _ installed => get_refines (componentLaws faults) _ _ installed _) ran
  | @flushed _ _ _ faults _ _ _ ran ih =>
    exact ih.flushObserved (componentLaws faults).toComponentEffects ran .delivered
  | @flushObserved _ _ _ faults result _ ran observed ih =>
    cases result <;> exact ih.flushObserved (componentLaws faults).toComponentEffects ran observed
  | @reopened _ _ faults _ _ _ ran ih =>
    exact ih.recoverOk (componentLaws faults).toComponentEffects ran
  | @openFailed _ _ faults _ _ _ ran ih =>
    exact ih.recoverError (componentLaws faults).toComponentEffects ran
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
