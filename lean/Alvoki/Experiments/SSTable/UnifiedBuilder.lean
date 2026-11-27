import Alvoki.Experiments.SSTable.UnifiedFormat
import Alvoki.Experiments.SSTable.UnifiedIntegrity

namespace ImmutableSSTable.Unified

/-- Targets include the packet checksum. An individual row or index entry can
use a larger packet if it fits the hard packet bound. -/
structure BuildOptions where
  dataTarget : Nat := 16 * 1024
  leafTarget : Nat := 16 * 1024

def footerPacketSize : Nat := footerBodySize + checksumSize

def dataSize (layout : Layout) (rows payload : Nat) : Nat :=
  payload + (if layout.hasOffsets then 8 * (rows + 1) else 0) + checksumSize

/-- Offset is the end of the bytes already sent to the sink. The pending rows
cover the suffix of the accepted row count. Leaf refs cover consecutive written
data blocks; root refs cover consecutive written leaves. The three byte counts
track unframed sizes so each buffer can be bounded before encoding it. -/
structure BuilderState where
  offset : Nat := 0
  count : Nat := 0
  lastKey : Option ByteArray := none
  data : Array Entry := #[]
  payloadBytes : Nat := 0
  leaf : Array Ref := #[]
  leafBytes : Nat := 0
  root : Array Ref := #[]
  rootBytes : Nat := 0

structure Writer (m : Type → Type) (ε : Type) where
  crc : Checksum
  layout : Layout
  sink : Sink m
  invalid : String → ε
  options : BuildOptions

def Writer.writePacket [Monad m] [MonadExceptOf ε m] (writer : Writer m ε)
    (kind : UInt64) (offset : Nat) (body : ByteArray) : m Nat := do
  let size := body.size + checksumSize
  unless size ≤ maxRowSize do throw (writer.invalid "SSTable packet exceeds size limit")
  let next := offset + size
  unless next + footerPacketSize ≤ maxFileSize do
    throw (writer.invalid "SSTable file exceeds signed offset limit")
  writer.sink.write (encodePacket writer.crc writer.layout.tableId kind offset body)
  return next

def Writer.flushLeaf [Monad m] [MonadExceptOf ε m] (writer : Writer m ε)
    (state : BuilderState) : m BuilderState := do
  match state.leaf[0]?, state.leaf.back? with
  | some first, some last =>
    let rootBytes := state.rootBytes + indexEntrySize last.lastKey
    unless rootBytes + checksumSize ≤ maxRowSize do
      throw (writer.invalid "SSTable root index exceeds size limit")
    let next ← writer.writePacket 2 state.offset (encodeIndex state.leaf)
    let ref : Ref :=
      { lastKey := last.lastKey
        offset := state.offset
        size := next - state.offset
        firstRow := first.firstRow
        count := last.firstRow + last.count - first.firstRow }
    return { state with
      offset := next
      root := state.root.push ref
      rootBytes := rootBytes
      leaf := #[]
      leafBytes := 0 }
  | _, _ => return state

def Writer.flushData [Monad m] [MonadExceptOf ε m] (writer : Writer m ε)
    (state : BuilderState) : m BuilderState := do
  match state.data.back? with
  | none => return state
  | some last =>
    let refBytes := indexEntrySize last.key
    let prepare : m BuilderState :=
      if !state.leaf.isEmpty && state.leafBytes + refBytes + checksumSize > writer.options.leafTarget then
        writer.flushLeaf state
      else
        pure state
    let state ← prepare
    let next ← writer.writePacket 1 state.offset (encodeData writer.layout state.data)
    let ref : Ref :=
      { lastKey := last.key
        offset := state.offset
        size := next - state.offset
        firstRow := state.count - state.data.size
        count := state.data.size }
    return { state with
      offset := next
      data := #[]
      payloadBytes := 0
      leaf := state.leaf.push ref
      leafBytes := state.leafBytes + refBytes }

def BuilderState.checkRow (state : BuilderState) (layout : Layout) (row : Entry) :
    Except String Unit :=
  if !rowFits layout row then .error "SSTable row does not match fixed widths"
  else if !state.lastKey.all (fun prev => decide (prev < row.key)) then
    .error "SSTable keys must strictly increase"
  else if dataSize layout 1 (entrySize layout row) > maxRowSize then
    .error "SSTable row exceeds packet size limit"
  else if indexEntrySize row.key + checksumSize > maxRowSize then
    .error "SSTable index key exceeds packet size limit"
  else .ok ()

def BuilderState.addRow (state : BuilderState) (layout : Layout) (row : Entry) : BuilderState :=
  { state with
    count := state.count + 1
    lastKey := some row.key
    data := state.data.push row
    payloadBytes := state.payloadBytes + entrySize layout row }

def Writer.accept [Monad m] [MonadExceptOf ε m] (writer : Writer m ε)
    (state : BuilderState) (row : Entry) : m BuilderState := do
  match state.checkRow writer.layout row with
  | .error error => throw (writer.invalid error)
  | .ok () =>
    let prepare : m BuilderState :=
      if !state.data.isEmpty &&
          dataSize writer.layout (state.data.size + 1)
            (state.payloadBytes + entrySize writer.layout row) > writer.options.dataTarget then
        writer.flushData state
      else
        pure state
    let state ← prepare
    return state.addRow writer.layout row

@[specialize] def Writer.streamRows [Monad m] [MonadExceptOf ε m] (writer : Writer m ε)
    (nextRow : m (Option Entry)) (state : BuilderState) : Nat → m BuilderState
  | 0 => do
    if (← nextRow).isSome then throw (writer.invalid "SSTable row count exceeds format limit")
    return state
  | room + 1 => do
    match ← nextRow with
    | none => return state
    | some row =>
      let next ← writer.accept state row
      writer.streamRows nextRow next room

def Writer.finish [Monad m] [MonadExceptOf ε m] (writer : Writer m ε)
    (state : BuilderState) : m Nat := do
  let state ← writer.flushData state
  let state ← writer.flushLeaf state
  let putRoot : m (Nat × Nat) :=
    if state.root.isEmpty then pure (0, 0)
    else do
      let stop ← writer.writePacket 3 state.offset (encodeIndex state.root)
      pure (state.offset, stop - state.offset)
  let (rootOffset, rootSize) ← putRoot
  let footer : Footer := { layout := writer.layout, count := state.count, rootOffset, rootSize }
  writer.sink.write (encodePacket writer.crc 0 4 0 (encodeFooterBody footer))
  writer.sink.flush
  return state.count

/-- Write ordered rows once. Completed data blocks and leaf pages are appended
as they fill. The final root encodes at most one packet of leaf references. -/
@[specialize] def buildStream [Monad m] [MonadExceptOf ε m] (crc : Checksum) (layout : Layout)
    (sink : Sink m) (nextRow : m (Option Entry)) (invalid : String → ε)
    (options : BuildOptions := {}) : m Nat := do
  unless layout.Valid do throw (invalid "invalid SSTable layout")
  unless 0 < options.dataTarget ∧ options.dataTarget ≤ maxRowSize ∧
      0 < options.leafTarget ∧ options.leafTarget ≤ maxRowSize do
    throw (invalid "invalid SSTable packet targets")
  let writer : Writer m ε := ⟨crc, layout, sink, invalid, options⟩
  let state ← writer.streamRows nextRow {} maxFileSize
  writer.finish state

end ImmutableSSTable.Unified
