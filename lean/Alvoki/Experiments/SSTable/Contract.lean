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

end ImmutableSSTable
