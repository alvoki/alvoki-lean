import Alvoki.Codec.Block
import Alvoki.Experiments.SSTable.Search

namespace ImmutableSSTable

/-- The header is an eight-byte format identifier followed by the row count. -/
def magic : ByteArray := "ALVSST01".toUTF8

def headerSize : Nat := 16

def rowSize : Nat := 16

/-- All valid file sizes fit a nonnegative signed 64-bit positional offset. -/
def maxRows : Nat := (2 ^ 63 - 1 - headerSize) / rowSize

def fileSize (rows : Nat) : Nat := headerSize + rowSize * rows

def rowOffset (index : Nat) : Nat := fileSize index

def encodeHeader (rows : Nat) : ByteArray :=
  Alvoki.pushWordFast magic rows.toUInt64

def encodeEntry (row : Entry) : ByteArray :=
  Alvoki.pushWordFast (Alvoki.pushWordFast (ByteArray.emptyWithCapacity rowSize) row.key) row.value

/-- Row bytes produced by repeated streaming writes, in their given order. -/
def encodeRows (rows : List Entry) : ByteArray :=
  (rows.flatMap fun row => (encodeEntry row).data.toList).toByteArray

def encodeImage (rows : List Entry) : ByteArray := encodeHeader rows.length ++ encodeRows rows

def decodeHeader (bytes : ByteArray) : Except String Nat := do
  unless bytes.size = headerSize do throw "invalid SSTable header size"
  unless (bytes.extract 0 8).data = magic.data do throw "invalid SSTable format"
  let count := (Alvoki.word bytes 8).toNat
  unless count ≤ maxRows do throw "SSTable row count exceeds signed offset limit"
  return count

def decodeEntry (bytes : ByteArray) : Except String Entry := do
  unless bytes.size = rowSize do throw "invalid SSTable row size"
  return ⟨Alvoki.word bytes 0, Alvoki.word bytes 8⟩

/-- A source carries the size and positional read for the same immutable file. -/
structure Source (m : Type → Type) where
  size : m Nat
  readAt : Nat → Nat → m ByteArray

def Source.memory [Monad m] (bytes : ByteArray) : Source m where
  size := pure bytes.size
  readAt offset count := pure (bytes.extract offset (offset + count))

structure Table (m : Type → Type) where private mk ::
  rowCount : Nat
  private source : Source m

/-- Identifies the source and header count retained by the returned handle. -/
def Table.BoundTo (table : Table m) (source : Source m) (count : Nat) : Prop :=
  table.rowCount = count ∧ table.source = source

private def liftDecode [Monad m] [MonadExceptOf String m] (result : Except String α) : m α :=
  match result with
  | .ok value => pure value
  | .error error => throw error

@[simp] private theorem liftDecode_ok [Monad m] [MonadExceptOf String m] (value : α) :
    liftDecode (m := m) (.ok value) = pure value := rfl

/-- Admit a correctly sized header and file, using at most one positional read.
Strict key order comes from the immutable file's builder. -/
def openTable [Monad m] [MonadExceptOf String m] (source : Source m) : m (Table m) := do
  let size ← source.size
  unless headerSize ≤ size do throw "SSTable is shorter than its header"
  let bytes ← source.readAt 0 headerSize
  let count ← liftDecode (decodeHeader bytes)
  unless size = fileSize count do throw "SSTable file size does not match its header"
  return ⟨count, source⟩

/-- Read one row at its positional offset. A short read is an error. -/
def Table.readEntry [Monad m] [MonadExceptOf String m] (table : Table m) (index : Nat) : m Entry := do
  unless index < table.rowCount do throw "SSTable cursor out of bounds"
  let bytes ← table.source.readAt (rowOffset index) rowSize
  liftDecode (decodeEntry bytes)

/-- Find the first row with key greater than or equal to the query. The cursor
is `rowCount` when all keys are smaller. -/
def Table.seek [Monad m] [MonadExceptOf String m] (table : Table m) (key : UInt64) : m Nat :=
  seekBetween table.readEntry key 0 table.rowCount

/-- Read the next row and advance one cursor position. End needs no file read. -/
def Table.next [Monad m] [MonadExceptOf String m] (table : Table m) (index : Nat) :
    m (Option (Entry × Nat)) := do
  if index < table.rowCount then
    let row ← table.readEntry index
    return some (row, index + 1)
  else
    return none

def Table.lookup [Monad m] [MonadExceptOf String m] (table : Table m) (key : UInt64) :
    m (Option UInt64) := do
  let index ← table.seek key
  match ← table.next index with
  | some (row, _) => return if row.key = key then some row.value else none
  | none => return none

end ImmutableSSTable
