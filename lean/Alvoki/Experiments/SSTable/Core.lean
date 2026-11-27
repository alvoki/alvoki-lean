import Alvoki.Experiments.SSTable.Search
import Alvoki.Codec.Block

namespace ImmutableSSTable

def magic : ByteArray := "ALVSST03".toUTF8

def footerSize : Nat := 24

def maxFileSize : Nat := 2 ^ 63 - 1

/-- The largest physical row, including its length and checksum words. -/
def maxRowSize : Nat := 16 * 1024 * 1024

def encodeOffset (offset : Nat) : ByteArray :=
  Alvoki.pushWordFast ByteArray.empty offset.toUInt64

def encodeFooter (rows indexStart : Nat) : ByteArray :=
  Alvoki.pushWordFast (Alvoki.pushWordFast magic rows.toUInt64) indexStart.toUInt64

def checksum (bytes : ByteArray) : UInt64 :=
  bytes.foldl (fun hash byte => (hash ^^^ byte.toUInt64) * 1099511628211) 14695981039346656037

def entrySize (row : Entry) : Nat := row.key.size + row.value.size + 16

def encodeEntry (row : Entry) : ByteArray :=
  let payload := encodeOffset row.key.size ++ row.key ++ row.value
  Alvoki.pushWordFast payload (checksum payload)

/-- Specification of the bytes emitted by the streaming builder. -/
def encodeRows : List Entry → ByteArray
  | [] => ByteArray.empty
  | row :: rest => encodeEntry row ++ encodeRows rest

def encodeOffsets (start : Nat) : List Entry → ByteArray
  | [] => encodeOffset start
  | row :: rest => encodeOffset start ++ encodeOffsets (start + (encodeEntry row).size) rest

def encodeImage (rows : List Entry) : ByteArray :=
  encodeRows rows ++ encodeOffsets 0 rows ++ encodeFooter rows.length (encodeRows rows).size

def Fits (rows : List Entry) : Prop :=
  (∀ row ∈ rows, (encodeEntry row).size ≤ maxRowSize) ∧
    (encodeRows rows).size + 8 * (rows.length + 1) + footerSize ≤ maxFileSize

def decodeFooter (bytes : ByteArray) : Except String (Nat × Nat) := do
  unless bytes.size = footerSize do throw "invalid SSTable footer size"
  unless bytes.extract 0 8 == magic do throw "invalid SSTable format"
  return ((Alvoki.word bytes 8).toNat, (Alvoki.word bytes 16).toNat)

def decodeOffsetPair (bytes : ByteArray) : Except String (Nat × Nat) := do
  unless bytes.size = 16 do throw "invalid SSTable offset pair size"
  return ((Alvoki.word bytes 0).toNat, (Alvoki.word bytes 8).toNat)

def decodeEntry (bytes : ByteArray) : Except String Entry := do
  unless 16 ≤ bytes.size ∧ bytes.size ≤ maxRowSize do throw "invalid SSTable row size"
  let keySize := (Alvoki.word bytes 0).toNat
  unless keySize ≤ bytes.size - 16 do throw "invalid SSTable key size"
  let payload := bytes.extract 0 (bytes.size - 8)
  unless Alvoki.word bytes (bytes.size - 8) = checksum payload do
    throw "invalid SSTable row checksum"
  return ⟨bytes.extract 8 (8 + keySize), bytes.extract (8 + keySize) (bytes.size - 8)⟩

/-- A source carries the size and positional read for the same immutable file. -/
structure Source (m : Type → Type) where
  size : m Nat
  readAt : Nat → Nat → m ByteArray

def Source.memory [Monad m] (bytes : ByteArray) : Source m where
  size := pure bytes.size
  readAt offset count := pure (bytes.extract offset (offset + count))

structure Table (m : Type → Type) where private mk ::
  rowCount : Nat
  private readRow : Nat → m Entry

/-- Expose a physical reader through the shared logical operations. The
    reader is called only at valid row indices. -/
def Table.ofReader (count : Nat) (readRow : Nat → m Entry) : Table m :=
  ⟨count, readRow⟩

def liftDecode [Monad m] [MonadExceptOf String m] (result : Except String α) : m α :=
  match result with
  | .ok value => pure value
  | .error error => throw error

/-- Read adjacent offsets together, then check the span before reading the row. -/
def readVariableEntry [Monad m] [MonadExceptOf String m] (source : Source m)
    (indexStart index : Nat) : m Entry := do
  let bytes ← source.readAt (indexStart + 8 * index) 16
  let (start, stop) ← liftDecode (decodeOffsetPair bytes)
  unless start < stop ∧ stop ≤ indexStart ∧ stop - start ≤ maxRowSize do
    throw "invalid SSTable row span"
  let row ← source.readAt start (stop - start)
  unless row.size = stop - start do throw "short SSTable row read"
  liftDecode (decodeEntry row)

/-- Identifies the variable layout and source retained by the returned handle. -/
def Table.BoundTo [Monad m] [MonadExceptOf String m] (table : Table m) (source : Source m)
    (count indexStart : Nat) : Prop :=
  table.rowCount = count ∧ table.readRow = readVariableEntry source indexStart

/-- Admit a footer and the declared directory extent in one positional read. -/
def openTable [Monad m] [MonadExceptOf String m] (source : Source m) : m (Table m) := do
  let size ← source.size
  unless footerSize ≤ size ∧ size ≤ maxFileSize do throw "invalid SSTable file size"
  let bytes ← source.readAt (size - footerSize) footerSize
  let (count, indexStart) ← liftDecode (decodeFooter bytes)
  unless indexStart + 8 * (count + 1) + footerSize = size do
    throw "invalid SSTable index extent"
  return Table.ofReader count (readVariableEntry source indexStart)

def Table.readEntry [Monad m] [MonadExceptOf String m] (table : Table m) (index : Nat) : m Entry := do
  unless index < table.rowCount do throw "SSTable cursor out of bounds"
  table.readRow index

theorem Table.ofReader_readEntry [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {count index : Nat} (readRow : Nat → m Entry) (within : index < count) :
    (Table.ofReader count readRow).readEntry index = readRow index := by
  simp [Table.readEntry, Table.ofReader, within]

def Table.seek [Monad m] [MonadExceptOf String m] (table : Table m) (key : ByteArray) : m Nat :=
  seekBetween table.readEntry key 0 table.rowCount

def Table.next [Monad m] [MonadExceptOf String m] (table : Table m) (index : Nat) :
    m (Option (Entry × Nat)) := do
  if index < table.rowCount then
    let row ← table.readEntry index
    return some (row, index + 1)
  else
    return none

def Table.lookup [Monad m] [MonadExceptOf String m] (table : Table m) (key : ByteArray) :
    m (Option ByteArray) := do
  let index ← table.seek key
  match ← table.next index with
  | some (row, _) => return if row.key = key then some row.value else none
  | none => return none

/-- A caller-selected typed view of a byte table. Retain the same codecs
when building and reopening a table. -/
structure TypedTable (m : Type → Type) (κ ν : Type) where
  table : Table m
  keyCodec : Codec κ
  valueCodec : Codec ν

def TypedTable.seek [Monad m] [MonadExceptOf String m] (table : TypedTable m κ ν) (key : κ) : m Nat :=
  table.table.seek (table.keyCodec.encode key)

def TypedTable.lookup [Monad m] [MonadExceptOf String m] (table : TypedTable m κ ν) (key : κ) :
    m (Option ν) := do
  match ← table.table.lookup (table.keyCodec.encode key) with
  | none => return none
  | some value => return some (← liftDecode (table.valueCodec.decode value))

def TypedTable.next [Monad m] [MonadExceptOf String m] (table : TypedTable m κ ν) (index : Nat) :
    m (Option ((κ × ν) × Nat)) := do
  match ← table.table.next index with
  | none => return none
  | some (row, nextIndex) =>
    let key ← liftDecode (table.keyCodec.decode row.key)
    let value ← liftDecode (table.valueCodec.decode row.value)
    return some ((key, value), nextIndex)

end ImmutableSSTable
