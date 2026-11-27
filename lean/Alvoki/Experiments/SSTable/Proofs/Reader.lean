import Alvoki.Experiments.SSTable.Representation
import Alvoki.Experiments.SSTable.Proofs.Builder
import Alvoki.Experiments.SSTable.Proofs.Search

namespace ImmutableSSTable

/-- A model of a stable positional reader. The callback observations apply to
successful exact reads in the image. The memory source implements this contract. -/
structure Source.Serves [Monad m] (source : Source m) (image : ByteArray) : Prop where
  size : source.size = pure image.size
  readAt : ∀ offset count, count ≤ rowSize → offset + count ≤ image.size →
    source.readAt offset count = pure (image.extract offset (offset + count))

theorem Source.memory_serves [Monad m] (image : ByteArray) :
    (Source.memory (m := m) image).Serves image :=
  ⟨rfl, fun _ _ _ _ => rfl⟩

/-- Opening an encoded image returns a table retaining that same source and the
exact encoded row count. Opening does not read the rows. -/
theorem openTable_encoded [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {source : Source m} {rows : List Entry} (fits : rows.length ≤ maxRows)
    (observed : source.Serves (encodeImage rows)) :
    ∃ table, openTable source = pure table ∧ table.BoundTo source rows.length := by
  have headerWithin : headerSize ≤ fileSize rows.length := by simp [fileSize]
  have header := observed.readAt 0 headerSize (by decide) (by simpa using headerWithin)
  rw [Nat.zero_add, encodeImage_extract_header] at header
  simp [openTable, observed.size, header, fits, encodeImage_size, headerWithin]
  exact ⟨_, rfl, rfl, rfl⟩

/-- The public indexed read issues exactly one in-bounds row read and decodes the
row at that index, independent of bytes in every other row. -/
theorem Table.readEntry_encoded [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {table : Table m} {source : Source m} {rows : List Entry}
    (bound : table.BoundTo source rows.length) (observed : source.Serves (encodeImage rows))
    {index : Nat} (within : index < rows.length) : table.readEntry index = pure rows[index] := by
  obtain ⟨count, sourceEq⟩ := bound
  have span : rowOffset index + rowSize ≤ (encodeImage rows).size := by
    rw [encodeImage_size]
    exact rowSpan within
  have row := observed.readAt (rowOffset index) rowSize (by decide) span
  rw [encodeImage_extract_row rows index within] at row
  simp [Table.readEntry, count, sourceEq, within, row]

/-- A successful iteration step returns exactly the indexed row and advances
once. At and after the end it returns `none`. -/
theorem Table.next_encoded [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {table : Table m} {source : Source m} {rows : List Entry}
    (bound : table.BoundTo source rows.length) (observed : source.Serves (encodeImage rows))
    (index : Nat) : table.next index = pure (Contents.next rows index) := by
  unfold Contents.next
  by_cases within : index < rows.length
  · simp [Table.next, bound.1, within, table.readEntry_encoded bound observed within]
  · simp [Table.next, bound.1, within]

/-- Total indexing for the search specification. The lower-bound predicate only
compares entries at valid indices. -/
def rowAt (rows : List Entry) (index : Nat) : Entry := rows[index]?.getD ⟨0, 0⟩

@[simp] theorem rowAt_eq {rows : List Entry} {index : Nat} (within : index < rows.length) :
    rowAt rows index = rows[index] := by simp [rowAt, List.getElem?_eq_getElem within]

/-- The actual table seeks the first row whose key is at least the target. -/
theorem Table.seek_encoded [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {table : Table m} {source : Source m} {rows : List Entry}
    (bound : table.BoundTo source rows.length) (observed : source.Serves (encodeImage rows))
    (strict : Ordered rows) (key : UInt64) :
    ∃ index, table.seek key = pure index ∧ Contents.IsSeek rows key index := by
  change ∃ i, table.seek key = pure i ∧ LowerBound (fun n => (rowAt rows n).key) rows.length key i
  unfold Table.seek
  rw [bound.1]
  apply seekBetween_correct
  · intro i within
    rw [rowAt_eq within]
    exact table.readEntry_encoded bound observed within
  · intro i j le within
    rcases Nat.eq_or_lt_of_le le with rfl | lt
    · exact UInt64.le_refl _
    · rw [rowAt_eq (Nat.lt_trans lt within), rowAt_eq within]
      exact UInt64.le_of_lt ((show rows.Pairwise _ from strict).rel_getElem_of_lt (Nat.lt_trans lt within) within lt)

private theorem Table.lookup_hit [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {table : Table m} {source : Source m} {rows : List Entry}
    (bound : table.BoundTo source rows.length) (observed : source.Serves (encodeImage rows))
    (strict : Ordered rows) (key : UInt64)
    {i : Nat} (within : i < rows.length) (hit : rows[i].key = key) :
    table.lookup key = pure (some rows[i].value) := by
  obtain ⟨index, seek, _, left, right⟩ := table.seek_encoded bound observed strict key
  have indexEq : index = i := by
    apply Nat.le_antisymm
    · by_cases enough : index ≤ i
      · exact enough
      have smaller := left i (by omega)
      change (rowAt rows i).key < key at smaller
      rw [rowAt_eq within, hit] at smaller
      exact False.elim (UInt64.lt_irrefl _ smaller)
    · by_cases enough : i ≤ index
      · exact enough
      have smaller : index < i := by omega
      have atIndex : index < rows.length := Nat.lt_trans smaller within
      have lower := right index (Nat.le_refl _) atIndex
      change key ≤ (rowAt rows index).key at lower
      rw [rowAt_eq atIndex] at lower
      have ordered := (show rows.Pairwise _ from strict).rel_getElem_of_lt atIndex within smaller
      rw [hit] at ordered
      exact False.elim (UInt64.not_lt.mpr lower ordered)
  have next := table.next_encoded bound observed i
  simp [Table.lookup, seek, indexEq, next, Contents.next, within, hit]

private theorem Table.lookup_miss [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {table : Table m} {source : Source m} {rows : List Entry}
    (bound : table.BoundTo source rows.length) (observed : source.Serves (encodeImage rows))
    (strict : Ordered rows) (key : UInt64)
    (miss : ∀ i (within : i < rows.length), rows[i].key ≠ key) : table.lookup key = pure none := by
  obtain ⟨index, seek, _⟩ := table.seek_encoded bound observed strict key
  have next := table.next_encoded bound observed index
  by_cases within : index < rows.length
  · simp [Table.lookup, seek, next, Contents.next, within, miss index within]
  · simp [Table.lookup, seek, next, Contents.next, within]

/-- Exact lookup on the returned table agrees with a linear search of the
logical rows, including absent keys. Strict key order rules out duplicates. -/
theorem Table.lookup_encoded [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {table : Table m} {source : Source m} {rows : List Entry}
    (bound : table.BoundTo source rows.length) (observed : source.Serves (encodeImage rows))
    (strict : Ordered rows) (key : UInt64) :
    table.lookup key = pure (Contents.lookup rows key) := by
  unfold Contents.lookup
  cases found : rows.find? (fun row => row.key == key) with
  | none =>
    simp only [Option.map_none]
    apply table.lookup_miss bound observed strict key
    intro i within hit
    have absent := List.find?_eq_none.mp found rows[i] (List.getElem_mem within)
    simp [hit] at absent
  | some row =>
    have member := List.mem_of_find?_eq_some found
    obtain ⟨i, within, same⟩ := List.mem_iff_getElem.mp member
    simp only [Option.map_some]
    rw [← same]
    apply table.lookup_hit bound observed strict key within
    rw [same]
    have matched : (row.key == key) = true := List.find?_some (p := fun entry : Entry => entry.key == key) found
    exact beq_iff_eq.mp matched

/-- Open and query the returned handle from the same image. -/
theorem open_lookup_encoded [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {source : Source m} {rows : List Entry} (fits : rows.length ≤ maxRows)
    (observed : source.Serves (encodeImage rows)) (strict : Ordered rows)
    (key : UInt64) :
    (do let table ← openTable source; table.lookup key) =
      pure (Contents.lookup rows key) := by
  obtain ⟨table, opened, bound⟩ := openTable_encoded fits observed
  simp [opened, table.lookup_encoded bound observed strict key]

/-- From the flushed image of the complete writer schedule, healthy positional I/O
returns a handle whose reads implement the input sequence. Input order and the
declared row count follow from the writer having accepted the stream. -/
theorem open_built_table [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {source : Source m} {rows : List Entry} {count bytes}
    (built : modelBuild rows = .ok (count, bytes))
    (observed : source.Serves bytes) :
    ∃ table, openTable source = pure table ∧ table.Represents rows := by
  obtain ⟨fits, ordered, _, image⟩ := modelBuild_ok_iff.mp built
  rw [image] at observed
  obtain ⟨table, opened, bound⟩ := openTable_encoded fits observed
  exact ⟨table, opened, ordered, bound.1, table.lookup_encoded bound observed ordered,
    table.seek_encoded bound observed ordered, table.next_encoded bound observed⟩

end ImmutableSSTable
