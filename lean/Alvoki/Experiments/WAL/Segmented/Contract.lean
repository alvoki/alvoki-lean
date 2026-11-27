/-! Observed batch positions start at one. Their numbers survive release of a
prefix. Position zero is the initial release boundary. -/
namespace WalRecoverySlice.Segmented.Contract

abbrev Batch := List UInt8

structure View where
  base : Nat
  batches : List Batch
  deriving BEq, Repr

def View.tail (v : View) : Nat := v.base + v.batches.length

def View.append (v : View) (batch : Batch) : View :=
  {v with batches := v.batches ++ [batch]}

def View.discardThrough (v : View) (k : Nat) : View :=
  ⟨max k v.base, v.batches.drop (k - v.base)⟩

inductive Request where
  | append (batch : Batch)
  | discardThrough (position : Nat)

def Request.apply (r : Request) (v : View) : Option View :=
  match r with
  | .append p => some (v.append p)
  | .discardThrough k => if k ≤ v.tail then some (v.discardThrough k) else none

inductive Event where
  | ack (r : Request)
  | uncertain (r : Request)
  | stop
  | openFailed
  | opened (view : View)
  | scan (view : View)

inductive State where
  | online (view : View)
  | offline (known : View) (pending : Option Request)

/-- A failed call may have taken effect. The next successful open chooses a
single view; later calls start with that choice. -/
inductive Step : State → Event → State → Prop where
  | ack : r.apply v = some next → Step (.online v) (.ack r) (.online next)
  | uncertain : Step (.online v) (.uncertain r) (.offline v (some r))
  | stop : Step (.online v) .stop (.offline v none)
  | stopAgain : Step (.offline v r) .stop (.offline v r)
  | openFailed : Step (.offline v r) .openFailed (.offline v r)
  | opened : (observed = v ∨ r.bind (fun req => req.apply v) = some observed) →
      Step (.offline v r) (.opened observed) (.online observed)
  | scan : Step (.online v) (.scan v) (.online v)

inductive Allows : List Event → State → Prop where
  | fresh : Allows [] (.online ⟨0, []⟩)
  | next : Allows events prior → Step prior event nextState → Allows (events ++ [event]) nextState

end WalRecoverySlice.Segmented.Contract
