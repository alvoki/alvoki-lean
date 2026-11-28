import Alvoki.Experiments.L0.Client
import Alvoki.Experiments.L0.Refinement

namespace ExperimentalL0.Execution

/-- Observable execution boundaries. Each constructor consumes a law for the
reached operation, so the induction is independent of the carrier of adapter
state and of the way component effects are established. -/
inductive Run : List Event → Option Session → Selected → Prop where
  | initial : Nonempty (Durable image []) → Run [] none image
  | written : Run events (some session) image →
      (∀ history, Installed session image history → Installed next after (history ++ [change])) →
      Run (events ++ [.written change]) (some next) after
  | writeUncertain : Run events (some session) image →
      (∀ history, Installed session image history →
        Nonempty (Durable after history) ∨ Nonempty (Durable after (history ++ [change]))) →
      Run (events ++ [.writeUncertain change]) none after
  | got : Run events (some session) image →
      (∀ history, Installed session image history → value = denote history key) →
      Run (events ++ [.got key value]) (some session) image
  | flushed : Run events (some session) image →
      (∀ history, Installed session image history → Installed next after history) →
      Run (events ++ [.flushed]) (some next) after
  | flushUncertain : Run events (some session) image →
      (∀ history, Installed session image history → Nonempty (Durable after history)) →
      Run (events ++ [.flushUncertain]) none after
  | reopened : Run events none image →
      (∀ history, Durable image history → Installed session after history) →
      Run (events ++ [.reopened]) (some session) after
  | openFailed : Run events none image →
      (∀ history, Durable image history → Nonempty (Durable after history)) →
      Run (events ++ [.openFailed]) none after
  | stop : Run events session image → Run (events ++ [.stop]) none image

def Represents (session : Option Session) (image : Selected) : Client.State → Prop
  | .ready db => ∃ online history, session = some online ∧ db = denote history ∧
      Installed online image history
  | .offline known pending => session = none ∧ ∃ history,
      Client.Permitted known (denote history) pending ∧ Nonempty (Durable image history)

theorem Run.refines (run : Run events session image) :
    ∃ state, Client.Allows events state ∧ Represents session image state := by
  induction run with
  | initial durable => exact ⟨_, .initial, rfl, [], Or.inl rfl, durable⟩
  | @written _ session image next after change _ step ih =>
    obtain ⟨_ | _, allowed, represented⟩ := ih
    · obtain ⟨_, history, equal, rfl, installed⟩ := represented
      cases equal
      exact ⟨_, allowed.next .written, _, _, rfl, (denote_write history change).symm,
        step history installed⟩
    · exact by have impossible := represented.1; contradiction
  | @writeUncertain _ session image after change _ step ih =>
    obtain ⟨_ | _, allowed, represented⟩ := ih
    · obtain ⟨_, history, equal, rfl, installed⟩ := represented
      cases equal
      refine ⟨_, allowed.next .writeUncertain, rfl, ?_⟩
      have previous (d : Nonempty (Durable after history)) :
          ∃ actual, Client.Permitted (denote history) (denote actual) (some change) ∧
            Nonempty (Durable after actual) := ⟨_, Or.inl rfl, d⟩
      have appended (d : Nonempty (Durable after (history ++ [change]))) :
          ∃ actual, Client.Permitted (denote history) (denote actual) (some change) ∧
            Nonempty (Durable after actual) :=
        ⟨_, Or.inr ⟨_, rfl, denote_write ..⟩, d⟩
      exact (step history installed).elim previous appended
    · exact by have impossible := represented.1; contradiction
  | got _ step ih =>
    obtain ⟨_ | _, allowed, represented⟩ := ih
    · obtain ⟨_, history, equal, rfl, installed⟩ := represented
      cases equal
      cases step history installed
      exact ⟨_, allowed.next .got, _, _, rfl, rfl, installed⟩
    · exact by have impossible := represented.1; contradiction
  | flushed _ step ih =>
    obtain ⟨_ | _, allowed, represented⟩ := ih
    · obtain ⟨_, history, equal, rfl, installed⟩ := represented
      cases equal
      exact ⟨_, allowed.next .flushed, _, _, rfl, rfl, step history installed⟩
    · exact by have impossible := represented.1; contradiction
  | flushUncertain _ step ih =>
    obtain ⟨_ | _, allowed, represented⟩ := ih
    · obtain ⟨_, history, equal, rfl, installed⟩ := represented
      cases equal
      exact ⟨_, allowed.next .flushUncertain, rfl, history, Or.inl rfl, step history installed⟩
    · exact by have impossible := represented.1; contradiction
  | reopened _ step ih =>
    obtain ⟨_ | _, allowed, represented⟩ := ih
    · obtain ⟨_, _, impossible, _, _⟩ := represented
      contradiction
    · obtain ⟨_, history, selected, ⟨d⟩⟩ := represented
      exact ⟨_, allowed.next (.reopened selected), _, _, rfl, rfl, step history d⟩
  | openFailed _ step ih =>
    obtain ⟨_ | _, allowed, represented⟩ := ih
    · obtain ⟨_, _, impossible, _, _⟩ := represented
      contradiction
    · obtain ⟨_, history, selected, ⟨d⟩⟩ := represented
      exact ⟨_, allowed.next .openFailed, rfl, history, selected, step history d⟩
  | stop _ ih =>
    obtain ⟨_ | _, allowed, represented⟩ := ih
    · obtain ⟨_, history, _, rfl, d, _, _⟩ := represented
      exact ⟨_, allowed.next .stop, rfl, history, Or.inl rfl, ⟨d⟩⟩
    · exact ⟨_, allowed.next .stopAgain, rfl, represented.2⟩

end ExperimentalL0.Execution
