import Std

namespace ImmutableSSTable
/-- Caller-selected serialization. Typed correctness uses roundtrip laws and, for
keys, preservation of the caller’s order. -/
structure Codec (α : Type) where
  encode : α → ByteArray
  decode : ByteArray → Except String α

/-- The experiment stores opaque key and value bytes. -/
structure Entry where
  key : ByteArray
  value : ByteArray
  deriving DecidableEq, BEq

def Entry.encode (keyCodec : Codec κ) (valueCodec : Codec ν) (row : κ × ν) : Entry :=
  ⟨keyCodec.encode row.1, valueCodec.encode row.2⟩

/-- A lower-bound cursor splits the ordered keys at the first eligible row. -/
def LowerBound (keyAt : Nat → ByteArray) (rows : Nat) (key : ByteArray) (index : Nat) : Prop :=
  index ≤ rows ∧
    (∀ i, i < index → keyAt i < key) ∧
    (∀ i, index ≤ i → i < rows → key ≤ keyAt i)

/-- The logical contents are a finite sequence in strictly increasing key order.
Cursors are zero-based positions in that sequence. -/
def Ordered (rows : List Entry) : Prop := rows.Pairwise fun a b => a.key < b.key

namespace Contents

def lookup (rows : List Entry) (key : ByteArray) : Option ByteArray :=
  (rows.find? fun row => row.key == key).map Entry.value

def next (rows : List Entry) (i : Nat) : Option (Entry × Nat) :=
  if h : i < rows.length then some (rows[i], i + 1) else none

/-- Only in-range keys participate in the partition. -/
def IsSeek (rows : List Entry) (key : ByteArray) (i : Nat) : Prop :=
  LowerBound (fun n => (rows[n]?.getD ⟨ByteArray.empty, ByteArray.empty⟩).key) rows.length key i

end Contents
end ImmutableSSTable
