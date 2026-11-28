import Alvoki.Experiments.WAL.Recovery
import Alvoki.Experiments.WAL.Segmented.Contract

namespace WalRecoverySlice.Segmented

structure Control where
  policy : Policy
  capacity : Nat
  active : Nat
  discarded : Nat
  deriving BEq, Repr

def Control.firstNeeded (c : Control) := min c.active (c.discarded / c.capacity)

structure Session where
  control : Control
  activeCount : Nat
  view : Contract.View
  deriving BEq, Repr

/-- One-based last batch position (zero for an empty WAL). Every prior segment is full. -/
def Session.tailPosition (s : Session) : Nat :=
  s.control.active * s.control.capacity + s.activeCount

/-- Segment calls invoke the existing single-file WAL. Preparation supplies an
empty segment at an unpublished ID, including its durable child contents.
Root synchronization settles names. The staged control record and its rename
are distinct operations in the exclusively owned directory. -/
structure Ops (m : Type → Type) where
  prepareSegment : Policy → Nat → m Unit
  syncRoot : m Unit
  stageControl : Control → m Unit
  syncControl : m Unit
  renameControl : m Unit
  readControl : m Control
  openSegment : Policy → Nat → m (List Bytes)
  appendSegment : Policy → Nat → Bytes → m Unit
  listSegments : m (List Nat)
  removeSegment : Nat → m Unit

section
variable {m : Type → Type} [Monad m] [MonadExceptOf String m]

def publish (ops : Ops m) (c : Control) : m Unit := do
  ops.stageControl c
  ops.syncControl
  ops.renameControl
  ops.syncRoot

def create (ops : Ops m) (policy : Policy) (capacity : Nat) : m Session := do
  if capacity = 0 || capacity > 255 then throw "segment capacity out of bounds"
  let c : Control := ⟨policy, capacity, 0, 0⟩
  ops.prepareSegment policy 0
  ops.syncRoot
  publish ops c
  return ⟨c, 0, ⟨0, []⟩⟩

def removeRetired (ops : Ops m) (first : Nat) : List Nat → m Unit
  | [] => pure ()
  | id :: rest => do
    if id < first then ops.removeSegment id
    removeRetired ops first rest

def collect (ops : Ops m) (c : Control) : m Unit := do
  removeRetired ops c.firstNeeded (← ops.listSegments)
  ops.syncRoot

def rotateIfFull (ops : Ops m) (session : Session) : m (Control × Nat) := do
  let c := session.control
  if session.activeCount = c.capacity then
    let next := { c with active := c.active + 1 }
    ops.prepareSegment c.policy next.active
    ops.syncRoot
    publish ops next
    return (next, 0)
  return (c, session.activeCount)

def append (ops : Ops m) (session : Session) (payload : Bytes) : m Session := do
  if payload.length > 32 then throw "batch out of bounds"
  if session.view.tail ≥ Contract.maxPosition then throw "segmented WAL position exhausted"
  let (next, used) ← rotateIfFull ops session
  ops.appendSegment next.policy next.active payload
  return ⟨next, used + 1, session.view.append payload⟩

def discardThrough (ops : Ops m) (session : Session) (k : Nat) : m Session := do
  if k > session.view.tail then throw "discard past end"
  if k ≤ session.view.base then return session
  let next := {session.control with discarded := k}
  publish ops next
  collect ops next
  return {session with control := next, view := session.view.discardThrough k}

/-- Read and validate the contiguous sealed IDs in increasing order. -/
def readSealed (ops : Ops m) (policy : Policy) (capacity first count : Nat)
    (acc : Array Bytes) : m (Array Bytes) :=
  match count with
  | 0 => pure acc
  | n + 1 => do
    let batches ← ops.openSegment policy first
    if batches.length != capacity then throw "incomplete sealed segment"
    readSealed ops policy capacity (first + 1) n (acc ++ batches.toArray)

@[inline] def reopenPrefix (ops : Ops m) : m (Control × Array Bytes) := do
  let c ← ops.readControl
  if c.capacity = 0 || c.capacity > 255 then throw "invalid segment capacity"
  if c.discarded > (c.active + 1) * c.capacity then throw "invalid release position"
  -- A process exit can leave a renamed control record visible before root sync.
  ops.syncRoot
  let sealed ← readSealed ops c.policy c.capacity c.firstNeeded (c.active - c.firstNeeded) #[]
  return (c, sealed)

@[inline] def finishReopen (ops : Ops m) (c : Control) (sealed : Array Bytes)
    (active : List Bytes) : m Session := do
  if active.length > c.capacity then throw "oversized active segment"
  if c.discarded > c.active * c.capacity + active.length then throw "release beyond recovered data"
  let retained := (sealed.toList ++ active).drop (c.discarded - c.firstNeeded * c.capacity)
  collect ops c
  return ⟨c, active.length, ⟨c.discarded, retained⟩⟩

/-- The active child is in scope through validation and collection. The
caller supplies its lifetime and receives it explicitly on success. -/
def reopenWith (ops : Ops m)
    (withActive : Policy → Nat → (child → List Bytes → m result) → m result)
    (finish : Session → child → m result) : m result := do
  let (c, sealed) ← reopenPrefix ops
  withActive c.policy c.active fun child active => do
    finish (← finishReopen ops c sealed active) child

def reopen (ops : Ops m) : m Session :=
  reopenWith ops (fun policy id resume => do resume () (← ops.openSegment policy id))
    (fun session () => pure session)

end
end WalRecoverySlice.Segmented
