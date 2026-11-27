import Alvoki.Experiments.L0.Basic

namespace ExperimentalL0

inductive Event where
  | written (change : Change)
  | writeUncertain (change : Change)
  | got (key : UInt64) (value : Option UInt64)
  | flushed
  | flushUncertain
  | stop
  | openFailed
  | reopened

namespace Client

inductive State where
  | ready (db : Database)
  | offline (known : Database) (pending : Option Change)

def Permitted (known db : Database) (pending : Option Change) : Prop :=
  db = known ∨ ∃ change, pending = some change ∧ db = change.apply known

inductive Step : State → Event → State → Prop where
  | written : Step (.ready db) (.written change) (.ready (change.apply db))
  | writeUncertain : Step (.ready db) (.writeUncertain change) (.offline db (some change))
  | got : Step (.ready db) (.got key (db key)) (.ready db)
  | flushed : Step (.ready db) .flushed (.ready db)
  | flushUncertain : Step (.ready db) .flushUncertain (.offline db none)
  | stop : Step (.ready db) .stop (.offline db none)
  | stopAgain : Step (.offline db pending) .stop (.offline db pending)
  | openFailed : Step (.offline db pending) .openFailed (.offline db pending)
  | reopened : Permitted known db pending → Step (.offline known pending) .reopened (.ready db)

inductive Allows : List Event → State → Prop where
  | initial : Allows [] (.offline (fun _ => none) none)
  | next : Allows events prior → Step prior event after → Allows (events ++ [event]) after

end Client

end ExperimentalL0
