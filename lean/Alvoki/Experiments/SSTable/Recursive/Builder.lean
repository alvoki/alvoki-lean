import Alvoki.Experiments.SSTable.Recursive.Format
import Alvoki.Experiments.SSTable.UnifiedBuilder

namespace ImmutableSSTable.Recursive

open Unified (Layout Ref Checksum checksumSize dataSize entrySize indexEntrySize
  encodePacket encodeData encodeIndex)

structure BuildOptions where
  dataTarget : Nat := 16 * 1024
  indexTarget : Nat := 16 * 1024
  membershipFilter : Bool := false

structure Page where
  refs : Array Ref := #[]
  bytes : Nat := 0

def Page.add (page : Page) (ref : Ref) : Page :=
  ⟨page.refs.push ref, page.bytes + indexEntrySize ref.lastKey⟩

def Page.shouldFlush (page : Page) (ref : Ref) (target : Nat) : Bool :=
  page.refs.size ≥ 2 && page.bytes + indexEntrySize ref.lastKey + checksumSize > target

structure BuilderState where
  offset : Nat := 0
  count : Nat := 0
  lastKey : Option ByteArray := none
  data : Array Entry := #[]
  payloadBytes : Nat := 0
  pages : List Page := []

structure Writer (m : Type → Type) (ε : Type) where
  crc : Checksum
  layout : Layout
  sink : Sink m
  invalid : String → ε
  options : BuildOptions

def Writer.writePacket [Monad m] [MonadExceptOf ε m] (writer : Writer m ε)
    (kind : UInt64) (limit offset : Nat) (body : ByteArray) : m Nat := do
  let size := body.size + checksumSize
  unless size ≤ limit do throw (writer.invalid "SSTable packet exceeds size limit")
  let next := offset + size
  unless next + footerPacketSize ≤ maxFileSize do
    throw (writer.invalid "SSTable file exceeds signed offset limit")
  writer.sink.write (encodePacket writer.crc writer.layout.tableId kind offset body)
  return next

def Writer.writePage [Monad m] [MonadExceptOf ε m] (writer : Writer m ε) (height offset : Nat)
    (page : Page) : m (Ref × Nat) := do
  let some first := page.refs[0]? | throw (writer.invalid "empty SSTable index page")
  let some last := page.refs.back? | throw (writer.invalid "empty SSTable index page")
  let next ← writer.writePacket (indexKind height) maxIndexSize offset (encodeIndex page.refs)
  return (⟨last.lastKey, offset, next - offset, first.firstRow,
    last.firstRow + last.count - first.firstRow⟩, next)

/-- Feed a completed child to the current level. Only a page with at least two
children can be promoted during streaming. Each call uses one unit of height. -/
def Writer.push [Monad m] [MonadExceptOf ε m] (writer : Writer m ε)
    (height offset : Nat) (ref : Ref) (pages : List Page) : Nat → m (Nat × List Page)
  | 0 => throw (writer.invalid "SSTable index height exceeds format limit")
  | fuel + 1 => do
    match pages with
    | [] => return (offset, [(Page.add {} ref)])
    | page :: upper =>
      if page.shouldFlush ref writer.options.indexTarget then
        let (promoted, next) ← writer.writePage height offset page
        let (stop, remaining) ← writer.push (height + 1) next promoted upper fuel
        return (stop, Page.add {} ref :: remaining)
      else
        return (offset, page.add ref :: upper)

def Writer.writeFilter [Monad m] [MonadExceptOf ε m] (writer : Writer m ε)
    (offset : Nat) (rows : Array Entry) : m Nat :=
  if writer.options.membershipFilter && useFilter rows.size then
    writer.writePacket filterKind maxRowSize offset (Bloom.build rows)
  else pure offset

def Writer.flushData [Monad m] [MonadExceptOf ε m] (writer : Writer m ε)
    (state : BuilderState) : m BuilderState := do
  let some last := state.data.back? | return state
  let offset ← writer.writeFilter state.offset state.data
  let next ← writer.writePacket dataKind maxRowSize offset (encodeData writer.layout state.data)
  let ref : Ref := ⟨last.key, offset, next - offset,
    state.count - state.data.size, state.data.size⟩
  let (offset, pages) ← writer.push 1 next ref state.pages maxHeight
  return { state with offset, pages, data := #[], payloadBytes := 0 }

def Writer.accept [Monad m] [MonadExceptOf ε m] (writer : Writer m ε)
    (state : BuilderState) (row : Entry) : m BuilderState := do
  -- Use the same input validation as ALVSST05, including its maximum fence size.
  let validation : Unified.BuilderState := { lastKey := state.lastKey }
  match validation.checkRow writer.layout row with
  | .error error => throw (writer.invalid error)
  | .ok () =>
    let rowBytes := entrySize writer.layout row
    let state ← if !state.data.isEmpty &&
        dataSize writer.layout (state.data.size + 1) (state.payloadBytes + rowBytes) >
          writer.options.dataTarget then writer.flushData state else pure state
    return { state with
      count := state.count + 1
      lastKey := some row.key
      data := state.data.push row
      payloadBytes := state.payloadBytes + rowBytes }

@[specialize] def Writer.streamRows [Monad m] [MonadExceptOf ε m] (writer : Writer m ε)
    (nextRow : m (Option Entry)) (state : BuilderState) : Nat → m BuilderState
  | 0 => do
    if (← nextRow).isSome then throw (writer.invalid "SSTable row count exceeds format limit")
    return state
  | room + 1 => do
    let some row ← nextRow | return state
    let next ← writer.accept state row
    writer.streamRows nextRow next room

/-- Promote the final fringe only while an upper level already exists. -/
def Writer.finishPages [Monad m] [MonadExceptOf ε m] (writer : Writer m ε)
    (height offset : Nat) (pages : List Page) : Nat → m (Nat × Nat × Nat)
  | 0 => throw (writer.invalid "SSTable index height exceeds format limit")
  | fuel + 1 => do
    match pages with
    | [] => return (0, 0, 0)
    | page :: upper =>
      let (ref, next) ← writer.writePage height offset page
      if upper.isEmpty then
        return (height, ref.offset, ref.size)
      let (stop, remaining) ← writer.push (height + 1) next ref upper fuel
      writer.finishPages (height + 1) stop remaining fuel

@[specialize] def buildStream [Monad m] [MonadExceptOf ε m] (crc : Checksum) (layout : Layout)
    (sink : Sink m) (nextRow : m (Option Entry)) (invalid : String → ε)
    (options : BuildOptions := {}) : m Nat := do
  unless layout.Valid do throw (invalid "invalid SSTable layout")
  unless 0 < options.dataTarget ∧ options.dataTarget ≤ maxRowSize ∧
      0 < options.indexTarget ∧ options.indexTarget ≤ maxRowSize do
    throw (invalid "invalid SSTable packet targets")
  let writer : Writer m ε := ⟨crc, layout, sink, invalid, options⟩
  let state ← writer.streamRows nextRow {} maxFileSize
  let state ← writer.flushData state
  let (height, offset, size) ← writer.finishPages 1 state.offset state.pages maxHeight
  let footer : Footer := ⟨⟨layout, state.count, offset, size⟩, height, options.membershipFilter⟩
  writer.sink.write (encodePacket crc 0 footerKind 0 (encodeFooter footer))
  writer.sink.flush
  return state.count

end ImmutableSSTable.Recursive
