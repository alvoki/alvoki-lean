import Alvoki.Experiments.SSTable.Representation

namespace ImmutableSSTable

/-- A stable source returns the exact requested bytes of the same file. -/
structure Source.Serves [Monad m] (source : Source m) (image : ByteArray) : Prop where
  size : source.size = pure image.size
  readAt : ∀ offset count, count ≤ maxRowSize → offset + count ≤ image.size →
    source.readAt offset count = pure (image.extract offset (offset + count))

theorem Source.memory_serves [Monad m] (image : ByteArray) :
    (Source.memory (m := m) image).Serves image :=
  ⟨rfl, fun _ _ _ _ => rfl⟩

/-- Total indexing for the search specification. The lower-bound predicate only
compares entries at valid indices. -/
def rowAt (rows : List Entry) (index : Nat) : Entry := rows[index]?.getD ⟨ByteArray.empty, ByteArray.empty⟩

@[simp] theorem rowAt_eq {rows : List Entry} {index : Nat} (within : index < rows.length) :
    rowAt rows index = (getElem rows index within) := by simp [rowAt, List.getElem?_eq_getElem within]


end ImmutableSSTable
