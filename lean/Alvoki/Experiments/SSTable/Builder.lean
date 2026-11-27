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

end ImmutableSSTable
