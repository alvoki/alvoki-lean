namespace DurableBlob

/-- A session starts offline with an already initialized durable value.
After an uncertain publication, recover before publishing again. -/
inductive State (α : Type) where
  | ready (value : α)
  | offline (known : α) (pending : Option α)

/-- Events describe responses, plus loss of the current session. -/
inductive Event (α : Type) where
  | published (value : α)
  | uncertain (proposed : α)
  | stop
  | openFailed
  | opened (value : α)

def Permitted (known : α) (pending : Option α) (value : α) : Prop :=
  value = known ∨ pending = some value

inductive Step : State α → Event α → State α → Prop where
  | published : Step (.ready old) (.published new) (.ready new)
  | uncertain : Step (.ready old) (.uncertain new) (.offline old (some new))
  | stop : Step (.ready old) .stop (.offline old none)
  | stopAgain : Step (.offline old pending) .stop (.offline old pending)
  | openFailed : Step (.offline old pending) .openFailed (.offline old pending)
  | opened : Permitted old pending value → Step (.offline old pending) (.opened value) (.ready value)

inductive Allows (initial : α) : List (Event α) → State α → Prop where
  | initial : Allows initial [] (.offline initial none)
  | next : Allows initial events before → Step before event after →
      Allows initial (events ++ [event]) after

/-- An adapter supplies whole-value operations. Its behavior is specified by
`Allows` with the session discipline in `State`. -/
structure Backend (m : Type → Type) (α : Type) where
  publish : α → m Unit
  reopen : m α

end DurableBlob
