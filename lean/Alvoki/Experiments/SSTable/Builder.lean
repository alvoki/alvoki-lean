import Alvoki.Experiments.SSTable.Core

namespace ImmutableSSTable

structure BuilderState where
  count : Nat := 0
  lastKey : Option UInt64 := none
  deriving Inhabited

/-- One successful push emits exactly one format row and advances its count. -/
def BuilderState.push (state : BuilderState) (row : Entry) :
    Except String (BuilderState × ByteArray) := do
  if state.count ≥ maxRows then throw "SSTable row count exceeds format limit"
  if let some prev := state.lastKey then
    if row.key ≤ prev then throw "SSTable keys must strictly increase"
  return (⟨state.count + 1, some row.key⟩, encodeEntry row)

/-- Bytes backpatched at offset zero once the input stream ends. -/
def BuilderState.header (state : BuilderState) : ByteArray := encodeHeader state.count

/-- Operations on a fresh, exclusively owned file positioned at zero. -/
structure Sink (m : Type → Type) where
  write : ByteArray → m Unit
  flush : m Unit
  rewind : m Unit

def placeholder : ByteArray := ByteArray.mk (Array.replicate headerSize 0)

/-- Keep accepting rows up to the format limit. The final supplier call
    distinguishes a full table from an input that exceeds the limit. -/
@[specialize] def streamRows [Monad m] [MonadExceptOf ε m] (sink : Sink m)
    (nextRow : m (Option Entry)) (invalid : String → ε) (state : BuilderState) :
    Nat → m BuilderState
  | 0 => do
    if (← nextRow).isSome then throw (invalid "SSTable row count exceeds format limit")
    return state
  | room + 1 => do
    match ← nextRow with
    | none => return state
    | some row =>
      match state.push row with
      | .error msg => throw (invalid msg)
      | .ok (updated, bytes) =>
        sink.write bytes
        streamRows sink nextRow invalid updated room

/-- Reserve the header, stream the body, then backpatch the final count.
    Flush before rewind and after overwriting the header. -/
@[specialize] def Sink.writeTable [Monad m] (sink : Sink m) (body : m BuilderState) : m Nat := do
  sink.write placeholder
  let last ← body
  sink.flush
  sink.rewind
  sink.write last.header
  sink.flush
  return last.count

/-- Complete construction schedule used by both the native writer and model. -/
@[specialize] def buildStream [Monad m] [MonadExceptOf ε m] (sink : Sink m)
    (nextRow : m (Option Entry)) (invalid : String → ε) : m Nat :=
  sink.writeTable (streamRows sink nextRow invalid {} maxRows)

end ImmutableSSTable
