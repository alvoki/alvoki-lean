import Alvoki.Experiments.SSTable.Representation
import Alvoki.Experiments.SSTable.Proofs.Builder
import Alvoki.Experiments.SSTable.Proofs.Search

namespace ImmutableSSTable

/-- A stable source returns the exact requested bytes of the same file. -/
structure Source.Serves [Monad m] (source : Source m) (image : ByteArray) : Prop where
  size : source.size = pure image.size
  readAt : ∀ offset count, count ≤ maxRowSize → offset + count ≤ image.size →
    source.readAt offset count = pure (image.extract offset (offset + count))

theorem Source.memory_serves [Monad m] (image : ByteArray) :
    (Source.memory (m := m) image).Serves image :=
  ⟨rfl, fun _ _ _ _ => rfl⟩

theorem openTable_encoded [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {source : Source m} {rows : List Entry} (fits : Fits rows)
    (observed : source.Serves (encodeImage rows)) :
    ∃ table, openTable source = pure table ∧
      table.BoundTo source rows.length (encodeRows rows).size := by
  have extent := encodeImage_size rows
  have footerWithin : footerSize ≤ (encodeImage rows).size := by omega
  have fileFits : (encodeImage rows).size ≤ maxFileSize := by rw [extent]; exact fits.2
  have countFits : rows.length ≤ maxFileSize := by have := fits.2; omega
  have startFits : (encodeRows rows).size ≤ maxFileSize := by have := fits.2; omega
  have footer := observed.readAt _ footerSize (by unfold maxRowSize footerSize; omega)
    (show (encodeImage rows).size - footerSize + footerSize ≤ (encodeImage rows).size by omega)
  rw [Nat.sub_add_cancel footerWithin, encodeImage_extract_footer] at footer
  simp only [openTable, observed.size, pure_bind, ite_eq_left (And.intro footerWithin fileFits), footer,
    decodeFooter_encodeFooter countFits startFits, liftDecode, ite_eq_left extent.symm]
  exact ⟨_, rfl, rfl, rfl⟩

theorem Table.readEntry_encoded [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {table : Table m} {source : Source m} {rows : List Entry}
    (bound : table.BoundTo source rows.length (encodeRows rows).size)
    (observed : source.Serves (encodeImage rows)) (fits : Fits rows)
    {index : Nat} (within : index < rows.length) : table.readEntry index = pure (getElem rows index within) := by
  obtain ⟨count, retained⟩ := bound
  have extent := encodeImage_size rows
  have offsets := observed.readAt ((encodeRows rows).size + 8 * index) 16 (by unfold maxRowSize; omega)
    (show (encodeRows rows).size + 8 * index + 16 ≤ (encodeImage rows).size by omega)
  have stopBound := rowPosition_bound rows (index + 1)
  have advance := rowPosition_succ (start := 0) rows within
  have nonempty := encodeEntry_min (getElem rows index within)
  have sizeBound := fits.1 (getElem rows index within) (List.getElem_mem within)
  have length : rowPosition 0 rows (index + 1) - rowPosition 0 rows index =
      (encodeEntry (getElem rows index within)).size :=
    (congrArg (fun stop => stop - rowPosition 0 rows index) advance).trans
      (Nat.add_sub_cancel_left _ _)
  have span : rowPosition 0 rows index < rowPosition 0 rows (index + 1) ∧
      rowPosition 0 rows (index + 1) ≤ (encodeRows rows).size ∧
      rowPosition 0 rows (index + 1) - rowPosition 0 rows index ≤ maxRowSize :=
    ⟨advance.symm ▸ Nat.lt_add_of_pos_right (Nat.lt_of_lt_of_le (by decide) nonempty),
      stopBound, by rw [length]; exact sizeBound⟩
  have payload := observed.readAt (rowPosition 0 rows index)
    (rowPosition 0 rows (index + 1) - rowPosition 0 rows index) span.2.2
    (by rw [Nat.add_sub_of_le (Nat.le_of_lt span.1), extent]; omega)
  rw [Nat.add_sub_of_le (Nat.le_of_lt span.1), encodeImage_extract_row rows within] at payload
  simp only [Table.readEntry, readVariableEntry, count, retained, ite_eq_left within, offsets, pure_bind,
    decodeImage_offsets rows fits within, liftDecode, ite_eq_left span, payload, ite_eq_left length.symm,
    decodeEntry_encodeEntry _ sizeBound]

/-- A successful iteration step returns exactly the indexed row and advances
once. At and after the end it returns `none`. -/
theorem Table.next_encoded [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {table : Table m} {rows : List Entry}
    (count : table.rowCount = rows.length)
    (reads : ∀ i (within : i < rows.length), table.readEntry i = pure rows[i])
    (index : Nat) : table.next index = pure (Contents.next rows index) := by
  unfold Contents.next
  by_cases within : index < rows.length
  · simp [Table.next, count, within, reads _ within]
  · simp [Table.next, count, within]

/-- Total indexing for the search specification. The lower-bound predicate only
compares entries at valid indices. -/
def rowAt (rows : List Entry) (index : Nat) : Entry := rows[index]?.getD ⟨ByteArray.empty, ByteArray.empty⟩

@[simp] theorem rowAt_eq {rows : List Entry} {index : Nat} (within : index < rows.length) :
    rowAt rows index = (getElem rows index within) := by simp [rowAt, List.getElem?_eq_getElem within]

/-- The actual table seeks the first row whose key is at least the target. -/
theorem Table.seek_encoded [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {table : Table m} {rows : List Entry}
    (count : table.rowCount = rows.length)
    (reads : ∀ i (within : i < rows.length), table.readEntry i = pure rows[i])
    (strict : Ordered rows) (key : ByteArray) :
    ∃ index, table.seek key = pure index ∧ Contents.IsSeek rows key index := by
  change ∃ i, table.seek key = pure i ∧ LowerBound (fun n => (rowAt rows n).key) rows.length key i
  unfold Table.seek
  rw [count]
  apply seekBetween_correct
  · intro i within
    rw [rowAt_eq within]
    exact reads _ within
  · intro i j le within
    rcases Nat.eq_or_lt_of_le le with rfl | lt
    · exact Std.le_refl _
    · rw [rowAt_eq (Nat.lt_trans lt within), rowAt_eq within]
      exact Std.le_of_lt ((show rows.Pairwise _ from strict).rel_getElem_of_lt (Nat.lt_trans lt within) within lt)

private theorem Table.lookup_hit [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {table : Table m} {rows : List Entry}
    (count : table.rowCount = rows.length)
    (reads : ∀ i (within : i < rows.length), table.readEntry i = pure rows[i])
    (strict : Ordered rows) (key : ByteArray)
    {i : Nat} (within : i < rows.length) (hit : rows[i].key = key) :
    table.lookup key = pure (some rows[i].value) := by
  obtain ⟨index, seek, _, left, right⟩ := table.seek_encoded count reads strict key
  have indexEq : index = i := by
    apply Nat.le_antisymm
    · by_cases enough : index ≤ i
      · exact enough
      have smaller := left i (by omega)
      change (rowAt rows i).key < key at smaller
      rw [rowAt_eq within, hit] at smaller
      exact False.elim (Std.lt_irrefl smaller)
    · by_cases enough : i ≤ index
      · exact enough
      have smaller : index < i := by omega
      have atIndex : index < rows.length := Nat.lt_trans smaller within
      have lower := right index (Nat.le_refl _) atIndex
      change key ≤ (rowAt rows index).key at lower
      rw [rowAt_eq atIndex] at lower
      have ordered := (show rows.Pairwise _ from strict).rel_getElem_of_lt atIndex within smaller
      rw [hit] at ordered
      exact False.elim (Std.not_lt.mpr lower ordered)
  have next := table.next_encoded count reads i
  simp [Table.lookup, seek, indexEq, next, Contents.next, within, hit]

private theorem Table.lookup_miss [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {table : Table m} {rows : List Entry}
    (count : table.rowCount = rows.length)
    (reads : ∀ i (within : i < rows.length), table.readEntry i = pure rows[i])
    (strict : Ordered rows) (key : ByteArray)
    (miss : ∀ i (within : i < rows.length), rows[i].key ≠ key) : table.lookup key = pure none := by
  obtain ⟨index, seek, _⟩ := table.seek_encoded count reads strict key
  have next := table.next_encoded count reads index
  by_cases within : index < rows.length
  · simp [Table.lookup, seek, next, Contents.next, within, miss index within]
  · simp [Table.lookup, seek, next, Contents.next, within]

/-- Exact lookup on the returned table agrees with a linear search of the
logical rows, including absent keys. Strict key order rules out duplicates. -/
theorem Table.lookup_encoded [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {table : Table m} {rows : List Entry}
    (count : table.rowCount = rows.length)
    (reads : ∀ i (within : i < rows.length), table.readEntry i = pure rows[i])
    (strict : Ordered rows) (key : ByteArray) :
    table.lookup key = pure (Contents.lookup rows key) := by
  unfold Contents.lookup
  cases found : rows.find? (fun row => row.key == key) with
  | none =>
    simp only [Option.map_none]
    apply table.lookup_miss count reads strict key
    intro i within hit
    have absent := List.find?_eq_none.mp found rows[i] (List.getElem_mem within)
    simp [hit] at absent
  | some row =>
    have member := List.mem_of_find?_eq_some found
    obtain ⟨i, within, same⟩ := List.mem_iff_getElem.mp member
    simp only [Option.map_some]
    rw [← same]
    apply table.lookup_hit count reads strict key within
    rw [same]
    have matched : (row.key == key) = true := List.find?_some (p := fun entry : Entry => entry.key == key) found
    exact beq_iff_eq.mp matched

/-- A physical reader that returns every indexed row implements the public
observations, independently of the storage layout. -/
theorem Table.represents_of_indexed_reads [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {table : Table m} {rows : List Entry} (count : table.rowCount = rows.length)
    (reads : ∀ i (within : i < rows.length), table.readEntry i = pure rows[i])
    (ordered : Ordered rows) : table.Represents rows :=
  ⟨ordered, count, table.lookup_encoded count reads ordered,
    table.seek_encoded count reads ordered, table.next_encoded count reads⟩

theorem open_built_table [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {source : Source m} {rows : List Entry} {count bytes}
    (built : modelBuild rows = .ok (count, bytes))
    (observed : source.Serves bytes) :
    ∃ table, openTable source = pure table ∧ table.Represents rows := by
  obtain ⟨fits, ordered, _, image⟩ := modelBuild_ok built
  rw [image] at observed
  obtain ⟨table, opened, bound⟩ := openTable_encoded fits observed
  have reads := fun (i : Nat) (within : i < rows.length) => table.readEntry_encoded bound observed fits within
  exact ⟨table, opened, table.represents_of_indexed_reads bound.1 reads ordered⟩

end ImmutableSSTable
