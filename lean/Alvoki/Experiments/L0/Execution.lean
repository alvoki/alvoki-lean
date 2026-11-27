import Alvoki.Experiments.L0.Client
import Alvoki.Experiments.L0.Refinement

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

private def Represents (session : Option Session) (image : Image) : Client.State → Prop
  | .ready db => ∃ online history, session = some online ∧ db = denote history ∧
      Installed online image history
  | .offline known pending => session = none ∧ ∃ history,
      Client.Permitted known (denote history) pending ∧ Nonempty (Durable image history)

private theorem initial_durable : Nonempty (Durable ({} : Image) []) :=
  ⟨⟨[], [], rfl, Nat.le_refl _, rfl, rfl, List.nodup_nil, [], rfl, fun _ => rfl, by simp⟩⟩

theorem Run.refines (run : Run events session image) :
    ∃ state, Client.Allows events state ∧ Represents session image state := by
  induction run with
  | initial => exact ⟨_, .initial, rfl, [], Or.inl rfl, initial_durable⟩
  | @written _ session image faults change next after _ ran ih =>
    obtain ⟨_ | _, allowed, represented⟩ := ih
    · obtain ⟨_, history, equal, rfl, installed⟩ := represented
      cases equal
      have effect := write_refines image faults session installed change
      rw [ran] at effect
      exact ⟨_, allowed.next .written, next, _, rfl, (denote_write history change).symm, effect⟩
    · exact by have impossible := represented.1; contradiction
  | @writeUncertain _ session image faults change result _ ran ih =>
    obtain ⟨_ | _, allowed, represented⟩ := ih
    · obtain ⟨_, history, equal, rfl, installed⟩ := represented
      cases equal
      have effect := write_refines image faults session installed change
      rw [ran] at effect
      refine ⟨_, allowed.next .writeUncertain, rfl, ?_⟩
      have previous (d : Nonempty (Durable (reached result) history)) :
          ∃ actual, Client.Permitted (denote history) (denote actual) (some change) ∧
            Nonempty (Durable (reached result) actual) := ⟨_, Or.inl rfl, d⟩
      have appended (d : Nonempty (Durable (reached result) (history ++ [change]))) :
          ∃ actual, Client.Permitted (denote history) (denote actual) (some change) ∧
            Nonempty (Durable (reached result) actual) :=
        ⟨_, Or.inr ⟨_, rfl, denote_write ..⟩, d⟩
      cases result with
      | ok next after =>
        obtain ⟨d, _, _⟩ := effect
        exact appended ⟨d⟩
      | error error after =>
        exact effect.elim previous appended
    · exact by have impossible := represented.1; contradiction
  | @got _ session image faults key value _ ran ih =>
    obtain ⟨_ | _, allowed, represented⟩ := ih
    · obtain ⟨_, history, equal, rfl, installed⟩ := represented
      cases equal
      rw [get_refines image faults session installed key] at ran
      cases ran
      exact ⟨_, allowed.next .got, _, _, rfl, rfl, installed⟩
    · exact by have impossible := represented.1; contradiction
  | @flushed _ session image faults next after _ ran ih =>
    obtain ⟨_ | _, allowed, represented⟩ := ih
    · obtain ⟨_, history, equal, rfl, installed⟩ := represented
      cases equal
      have effect := flush_refines image faults session installed
      rw [ran] at effect
      exact ⟨_, allowed.next .flushed, _, _, rfl, rfl, effect⟩
    · exact by have impossible := represented.1; contradiction
  | @flushUncertain _ session image faults result _ ran ih =>
    obtain ⟨_ | _, allowed, represented⟩ := ih
    · obtain ⟨_, history, equal, rfl, installed⟩ := represented
      cases equal
      have effect := flush_refines image faults session installed
      rw [ran] at effect
      refine ⟨_, allowed.next .flushUncertain, rfl, history, Or.inl rfl, ?_⟩
      cases result with
      | ok next after =>
        obtain ⟨d, _, _⟩ := effect
        exact ⟨d⟩
      | error error after => exact effect
    · exact by have impossible := represented.1; contradiction
  | @reopened _ image faults session after _ ran ih =>
    obtain ⟨_ | _, allowed, represented⟩ := ih
    · obtain ⟨_, _, impossible, _, _⟩ := represented
      contradiction
    · obtain ⟨_, history, selected, ⟨d⟩⟩ := represented
      have effect := recover_refines image faults d
      rw [ran] at effect
      exact ⟨_, allowed.next (.reopened selected), _, _, rfl, rfl, effect.2⟩
  | @openFailed _ image faults error after _ ran ih =>
    obtain ⟨_ | _, allowed, represented⟩ := ih
    · obtain ⟨_, _, impossible, _, _⟩ := represented
      contradiction
    · obtain ⟨_, history, selected, ⟨d⟩⟩ := represented
      have effect := recover_refines image faults d
      rw [ran] at effect
      exact ⟨_, allowed.next .openFailed, rfl, history, selected, ⟨effect ▸ d⟩⟩
  | stop _ ih =>
    obtain ⟨_ | _, allowed, represented⟩ := ih
    · obtain ⟨_, history, _, rfl, d, _, _⟩ := represented
      exact ⟨_, allowed.next .stop, rfl, history, Or.inl rfl, ⟨d⟩⟩
    · exact ⟨_, allowed.next .stopAgain, rfl, represented.2⟩

theorem Run.healthy_open (run : Run events none image) :
    ∃ session, Run (events ++ [.reopened]) (some session) image := by
  obtain ⟨_ | _, _, represented⟩ := run.refines
  · obtain ⟨_, _, impossible, _, _⟩ := represented
    contradiction
  · obtain ⟨_, _, _, ⟨d⟩⟩ := represented
    exact ⟨_, .reopened run (recover_healthy image {} d rfl rfl)⟩

end Model
end ExperimentalL0
