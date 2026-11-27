/-! Client observations of a single-writer append-only WAL, in whole batches. -/
namespace WalRecoverySlice.Contract

abbrev Batch := List UInt8
abbrev History := List Batch

inductive Event where
  | ack (batch : Batch)
  | uncertain (batch : Batch)
  | stop
  | openFailed
  | opened (history : History)
  | scan (history : History)

inductive View where
  | online (history : History)
  | offline (known : History) (pending : Option Batch)

/-- A successful open resolves at most the one submission that had no ACK. -/
def Permitted (known : History) (pending : Option Batch) (observed : History) : Prop :=
  observed = known ∨ observed = known ++ pending.toList

inductive Step : View → Event → View → Prop where
  | ack : Step (.online h) (.ack p) (.online (h ++ [p]))
  | uncertain : Step (.online h) (.uncertain p) (.offline h (some p))
  | stop : Step (.online h) .stop (.offline h none)
  | stoppedAgain : Step (.offline h p) .stop (.offline h p)
  | failed : Step (.offline h p) .openFailed (.offline h p)
  | opened : Permitted h p seen → Step (.offline h p) (.opened seen) (.online seen)
  | scan : Step (.online h) (.scan h) (.online h)

inductive Allows : List Event → View → Prop where
  | fresh : Allows [] (.online [])
  | next : Allows events prior → Step prior event nextView → Allows (events ++ [event]) nextView

end WalRecoverySlice.Contract
