import Alvoki.Experiments.DurableBlob.Contract

namespace DurableBlob

def Event.map (f : α → β) : Event α → Event β
  | .published v => .published (f v)
  | .uncertain v => .uncertain (f v)
  | .stop => .stop
  | .openFailed => .openFailed
  | .opened v => .opened (f v)

def State.map (f : α → β) : State α → State β
  | .ready v => .ready (f v)
  | .offline v p => .offline (f v) (p.map f)

/-- The caller supplies payloads only for publication. Reopen payloads are
selected by the backend from the values already in the session. -/
def Event.Submitted (P : α → Prop) : Event α → Prop
  | .published v | .uncertain v => P v
  | _ => True

def Event.Values (P : α → Prop) : Event α → Prop
  | .opened v => P v
  | event => event.Submitted P

def State.Values (P : α → Prop) : State α → Prop
  | .ready v => P v
  | .offline v pending => P v ∧ ∀ x ∈ pending, P x

private theorem Step.lift (f : α → β) (valid : α → Prop)
    (step : Step (before.map f) event after) (prior : before.Values valid)
    (submitted : event.Submitted (fun b => ∃ a, valid a ∧ f a = b)) :
    ∃ observed next, Step before observed next ∧ observed.map f = event ∧ next.map f = after ∧
      observed.Values valid ∧ next.Values valid := by
  cases before with
  | ready old =>
    cases step with
    | published =>
      obtain ⟨_, accepted, rfl⟩ := submitted
      exact ⟨_, _, .published, rfl, rfl, accepted, accepted⟩
    | uncertain =>
      obtain ⟨_, accepted, rfl⟩ := submitted
      exact ⟨_, _, .uncertain, rfl, rfl, accepted, prior, by simpa⟩
    | stop => exact ⟨_, _, .stop, rfl, rfl, trivial, prior, by simp⟩
  | offline old pending =>
    cases step with
    | stopAgain => exact ⟨_, _, .stopAgain, rfl, rfl, trivial, prior⟩
    | openFailed => exact ⟨_, _, .openFailed, rfl, rfl, trivial, prior⟩
    | opened chosen =>
      rcases chosen with same | proposed
      · subst_vars
        exact ⟨_, _, .opened (Or.inl rfl), rfl, rfl, prior.1, prior.1⟩
      · cases pending with
        | none => contradiction
        | some v =>
          simp only [Option.map_some, Option.some.injEq] at proposed
          subst_vars
          have accepted := prior.2 v (by simp)
          exact ⟨_, _, .opened (Or.inr rfl), rfl, rfl, accepted, accepted⟩

/-- Lift a byte-level session through an encoding. Only submitted values
need preimages: the contract itself accounts for every reopened value. -/
theorem Allows.lift (f : α → β) (valid : α → Prop) (initial : α)
    (trace : Allows (f initial) events state) (start : valid initial)
    (submitted : ∀ event ∈ events, event.Submitted (fun b => ∃ a, valid a ∧ f a = b)) :
    ∃ observed next, Allows initial observed next ∧
      observed.map (Event.map f) = events ∧ next.map f = state ∧
      (∀ event ∈ observed, event.Values valid) ∧ next.Values valid := by
  induction trace with
  | initial => exact ⟨[], _, .initial, rfl, rfl, by simp, start, by simp⟩
  | next _ step ih =>
    obtain ⟨observed, before, allowed, rfl, rfl, validPrior, prior⟩ :=
      ih (fun event member => submitted event (List.mem_append_left _ member))
    obtain ⟨event, after, lifted, rfl, rfl, accepted, nextValid⟩ :=
      step.lift f valid prior (submitted _ (by simp))
    refine ⟨_, after, allowed.next lifted, List.map_append, rfl, ?_, nextValid⟩
    intro value member
    rcases List.mem_append.mp member with earlier | latest
    · exact validPrior value earlier
    · simpa using (List.mem_singleton.mp latest).symm ▸ accepted

end DurableBlob
