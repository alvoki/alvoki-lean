import Alvoki.Experiments.SSTable.Core

namespace ImmutableSSTable

/-- Even before accounting for the data and footer, each row needs an eight-byte offset. -/
def maxRows : Nat := maxFileSize / 8

structure BuilderState where
  count : Nat := 0
  dataEnd : Nat := 0
  lastKey : Option ByteArray := none
  deriving Inhabited

/-- Check the size before encoding the row and reserve the metadata for the
resulting file, including the sentinel offset and footer. -/
def BuilderState.push (state : BuilderState) (row : Entry) :
    Except String (BuilderState × ByteArray) := do
  unless state.lastKey.all (fun prev => decide (prev < row.key)) do
    throw "SSTable keys must strictly increase"
  let size := entrySize row
  unless size ≤ maxRowSize do throw "SSTable row exceeds format size limit"
  let count := state.count + 1
  let dataEnd := state.dataEnd + size
  unless dataEnd + 8 * (count + 1) + footerSize ≤ maxFileSize do
    throw "SSTable file exceeds signed offset limit"
  return (⟨count, dataEnd, some row.key⟩, encodeEntry row)

/-- Two streams owned by the builder. The offset stream is appended, in order,
to the end of the data stream once all rows and the sentinel have been written. -/
structure Sink (m : Type → Type) where
  writeData : ByteArray → m Unit
  writeOffset : ByteArray → m Unit
  appendOffsets : m Unit
  flush : m Unit

/-- Write each accepted row and remember its start in the separate offset stream.
The final supplier call distinguishes EOF from input that exceeds the limit. -/
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
        sink.writeData bytes
        sink.writeOffset (encodeOffset state.dataEnd)
        streamRows sink nextRow invalid updated room

/-- Finalize the complete image in append order. -/
@[specialize] def Sink.writeTable [Monad m] (sink : Sink m) (body : m BuilderState) : m Nat := do
  let last ← body
  sink.writeOffset (encodeOffset last.dataEnd)
  sink.appendOffsets
  sink.writeData (encodeFooter last.count last.dataEnd)
  sink.flush
  return last.count

/-- Complete construction schedule used by the native writer and its model. -/
@[specialize] def buildStream [Monad m] [MonadExceptOf ε m] (sink : Sink m)
    (nextRow : m (Option Entry)) (invalid : String → ε) : m Nat :=
  sink.writeTable (streamRows sink nextRow invalid {} maxRows)

end ImmutableSSTable
