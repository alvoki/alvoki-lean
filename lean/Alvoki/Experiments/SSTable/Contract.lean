import Std

namespace ImmutableSSTable

/-- The experiment stores unsigned 64-bit keys and values. -/
structure Entry where
  key : UInt64
  value : UInt64
  deriving DecidableEq, Repr

/-- A lower-bound cursor splits the ordered keys at the first eligible row. -/
def LowerBound (keyAt : Nat → UInt64) (rows : Nat) (key : UInt64) (index : Nat) : Prop :=
  index ≤ rows ∧
    (∀ i, i < index → keyAt i < key) ∧
    (∀ i, index ≤ i → i < rows → key ≤ keyAt i)

/-- The logical contents are a finite sequence in strictly increasing key order.
Cursors are zero-based positions in that sequence. -/
def Ordered (rows : List Entry) : Prop := rows.Pairwise fun a b => a.key < b.key

namespace Contents

def lookup (rows : List Entry) (key : UInt64) : Option UInt64 :=
  (rows.find? fun row => row.key == key).map Entry.value

def next (rows : List Entry) (i : Nat) : Option (Entry × Nat) :=
  if h : i < rows.length then some (rows[i], i + 1) else none

/-- Only in-range keys participate in the partition. -/
def IsSeek (rows : List Entry) (key : UInt64) (i : Nat) : Prop :=
  LowerBound (fun n => (rows[n]?.getD ⟨0, 0⟩).key) rows.length key i

end Contents
end ImmutableSSTable
