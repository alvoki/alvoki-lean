import Alvoki.Experiments.SSTable.FixedFormat

namespace ImmutableSSTable.Fixed

/-- A fresh output stream owned exclusively by the builder until it returns. -/
structure Sink (m : Type → Type) where
  write : ByteArray → m Unit
  flush : m Unit

structure BuilderState where
  count : Nat := 0
  blocks : Nat := 0
  pendingRows : Nat := 0
  pending : ByteArray := .empty
  lastKey : Option ByteArray := none

def BuilderState.checkRow (state : BuilderState) (layout : Layout) (row : Entry) :
    Except String Unit :=
  if layout.RowFits row then
    if state.lastKey.all (fun prev => decide (prev < row.key)) then
      if layout.Fits (state.count + 1) then .ok ()
      else .error "SSTable file exceeds signed offset limit"
    else .error "SSTable keys must strictly increase"
  else .error "SSTable row does not match fixed widths"

def BuilderState.buffer (state : BuilderState) (row : Entry) : BuilderState :=
  { state with
    count := state.count + 1
    pendingRows := state.pendingRows + 1
    pending := state.pending ++ encodeRow row
    lastKey := some row.key }

def BuilderState.advance (state : BuilderState) : BuilderState :=
  { state with blocks := state.blocks + 1, pendingRows := 0, pending := .empty }

/-- Accept each row once and retain only the pending block and previous key.
Emit a full block immediately and continue with an empty buffer. -/
@[specialize] def streamRows [Monad m] [MonadExceptOf ε m] (layout : Layout) (sink : Sink m)
    (nextRow : m (Option Entry)) (invalid : String → ε) (state : BuilderState) :
    Nat → m BuilderState
  | 0 => do
    if (← nextRow).isSome then throw (invalid "SSTable row count exceeds format limit")
    return state
  | room + 1 => do
    match ← nextRow with
    | none => return state
    | some row =>
      match state.checkRow layout row with
      | .error error => throw (invalid error)
      | .ok () =>
        let buffered := state.buffer row
        if buffered.pendingRows = layout.rowsPerBlock then
          sink.write (encodeBlock layout buffered.blocks buffered.pending)
          streamRows layout sink nextRow invalid buffered.advance room
        else
          streamRows layout sink nextRow invalid buffered room

/-- Write the final short block, if there is one, followed by the footer. -/
@[specialize] def Sink.finish [Monad m] (sink : Sink m) (layout : Layout)
    (state : BuilderState) : m Nat := do
  if state.pendingRows ≠ 0 then
    sink.write (encodeBlock layout state.blocks state.pending)
  sink.write (encodeFooter layout state.count)
  sink.flush
  return state.count

@[specialize] def buildStream [Monad m] [MonadExceptOf ε m] (layout : Layout) (sink : Sink m)
    (nextRow : m (Option Entry)) (invalid : String → ε) : m Nat := do
  unless layout.Fits 0 do throw (invalid "invalid SSTable fixed layout")
  let last ← streamRows layout sink nextRow invalid {} maxFileSize
  sink.finish layout last

end ImmutableSSTable.Fixed
