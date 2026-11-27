import Alvoki.Experiments.SSTable.Search
import Alvoki.Codec.Block

namespace ImmutableSSTable

def maxFileSize : Nat := 2 ^ 63 - 1

/-- The largest physical row, including its length and checksum words. -/
def maxRowSize : Nat := 16 * 1024 * 1024

def encodeOffset (offset : Nat) : ByteArray :=
  Alvoki.pushWordFast ByteArray.empty offset.toUInt64

/-- A source carries the size and positional read for the same immutable file. -/
structure Source (m : Type → Type) where
  size : m Nat
  readAt : Nat → Nat → m ByteArray

def Source.memory [Monad m] (bytes : ByteArray) : Source m where
  size := pure bytes.size
  readAt offset count := pure (bytes.extract offset (offset + count))

/-- A streaming sink owns one fresh output until the builder returns. -/
structure Sink (m : Type → Type) where
  write : ByteArray → m Unit
  flush : m Unit

/-- Public operations of an opened immutable table. The constructor packages
the reader's real operations, including its optimized search. -/
structure Table (m : Type → Type) where
  rowCount : Nat
  lookup : ByteArray → m (Option ByteArray)
  seek : ByteArray → m Nat
  next : Nat → m (Option (Entry × Nat))

def liftDecode [Monad m] [MonadExceptOf String m] (result : Except String α) : m α :=
  match result with
  | .ok value => pure value
  | .error error => throw error

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
