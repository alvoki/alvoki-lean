import Alvoki.Experiments.SSTable.UnifiedReader
import Alvoki.Experiments.SSTable.Proofs.Reader
import Alvoki.Experiments.SSTable.Proofs.Search

namespace ImmutableSSTable.Unified

private theorem lowerBound_eq_of_partition {test : Nat → Bool} {n cut : Nat}
    (expected : Alvoki.Partition test n cut) : Alvoki.lowerBound test 0 n = cut := by
  obtain ⟨within, before, after⟩ := expected
  have monotone : ∀ i j, i ≤ j → j < n → test j = true → test i = true := by
    intro i j le jInside pos
    by_cases left : j < cut
    · exact before i (by omega)
    · have no := after j (by omega) jInside
      simp [pos] at no
  obtain ⟨resultWithin, resultBefore, resultAfter⟩ :=
    Alvoki.lowerBound_partition test n 0 n monotone (by omega) (by omega) (by omega)
  apply Nat.le_antisymm
  · by_cases correct : Alvoki.lowerBound test 0 n ≤ cut
    · exact correct
    · have one := resultBefore cut (by omega)
      have zero := after cut (by omega) (by omega)
      simp [one] at zero
  · by_cases correct : cut ≤ Alvoki.lowerBound test 0 n
    · exact correct
    · have one := before (Alvoki.lowerBound test 0 n) (by omega)
      have zero := resultAfter (Alvoki.lowerBound test 0 n) (by omega) (by omega)
      simp [one] at zero

private theorem findRef_at {refs : Array Ref} {before : Ref → Bool}
    (inside : j < refs.size)
    (left : ∀ i (hi : i < refs.size), i < j → before refs[i] = true)
    (right : ∀ i (hi : i < refs.size), j ≤ i → before refs[i] = false) :
    findRef refs before = some refs[j] := by
  let test := fun (i : Nat) => (refs[i]?).elim false before
  have partition : Alvoki.Partition test refs.size j := by
    refine ⟨Nat.le_of_lt inside, ?_, ?_⟩
    · intro i iLeft
      have hi : i < refs.size := by omega
      simpa [test, Array.getElem?_eq_getElem hi] using left i hi iLeft
    · intro i iRight hi
      simpa [test, Array.getElem?_eq_getElem hi] using right i hi iRight
  change refs[Alvoki.lowerBound test 0 refs.size]? = some refs[j]
  rw [lowerBound_eq_of_partition partition, Array.getElem?_eq_getElem inside]

private theorem findRef_none {refs : Array Ref} {before : Ref → Bool}
    (all : ∀ i (hi : i < refs.size), before refs[i] = true) : findRef refs before = none := by
  let test := fun (i : Nat) => (refs[i]?).elim false before
  have partition : Alvoki.Partition test refs.size refs.size := by
    refine ⟨Nat.le_refl _, ?_, ?_⟩
    · intro i hi
      simpa [test, Array.getElem?_eq_getElem hi] using all i hi
    · omega
  change refs[Alvoki.lowerBound test 0 refs.size]? = none
  rw [lowerBound_eq_of_partition partition, Array.getElem?_eq_none (Nat.le_refl _)]

/-- The references partition a contiguous interval of the logical table, and
each fence is the last row key of its own interval. -/
structure RefCovers (rows : List Entry) (first count : Nat) (refs : Array Ref) : Prop where
  extent : first + count ≤ rows.length
  span : ∀ i (hi : i < refs.size), let ref := refs[i]
    0 < ref.count ∧ first ≤ ref.firstRow ∧ ref.firstRow + ref.count ≤ first + count ∧
      ref.lastKey = (rowAt rows (ref.firstRow + ref.count - 1)).key
  separated : ∀ i j (hi : i < refs.size) (hj : j < refs.size), i < j →
    refs[i].firstRow + refs[i].count ≤ refs[j].firstRow
  covers : ∀ index, first ≤ index → index < first + count →
    ∃ j, ∃ hj : j < refs.size, refs[j].firstRow ≤ index ∧ index < refs[j].firstRow + refs[j].count

/-- Use the actual binary search on the reference array to route a row cursor. -/
theorem RefCovers.selectRow {rows : List Entry} {refs : Array Ref}
    (partition : RefCovers rows first count refs) (start : first ≤ index)
    (stop : index < first + count) :
    ∃ j, ∃ hj : j < refs.size,
      findRef refs (fun ref => decide (ref.firstRow + ref.count ≤ index)) = some refs[j] ∧
        refs[j].firstRow ≤ index ∧ index < refs[j].firstRow + refs[j].count := by
  obtain ⟨j, hj, left, right⟩ := partition.covers index start stop
  refine ⟨j, hj, ?_, left, right⟩
  apply findRef_at hj
  · intro i hi earlier
    exact decide_eq_true (Nat.le_trans (partition.separated i j hi hj earlier) left)
  · intro i hi later
    apply decide_eq_false
    rcases Nat.eq_or_lt_of_le later with rfl | later
    · omega
    · have sep := partition.separated j i hj hi later
      omega

/-- Route the global lower-bound cursor by fence keys, using the same search as
the executable lookup. -/
theorem RefCovers.selectKey {rows : List Entry} {refs : Array Ref} {key : ByteArray}
    (partition : RefCovers rows first count refs)
    (lower : LowerBound (fun i => (rowAt rows i).key) rows.length key index)
    (start : first ≤ index) (stop : index < first + count) :
    ∃ j, ∃ hj : j < refs.size,
      findRef refs (fun ref => decide (ref.lastKey < key)) = some refs[j] ∧
        refs[j].firstRow ≤ index ∧ index < refs[j].firstRow + refs[j].count := by
  obtain ⟨j, hj, left, right⟩ := partition.covers index start stop
  refine ⟨j, hj, ?_, left, right⟩
  apply findRef_at hj
  · intro i hi earlier
    obtain ⟨positive, _, _, fence⟩ := partition.span i hi
    have sep := partition.separated i j hi hj earlier
    exact decide_eq_true (fence.symm ▸ lower.2.1 _ (by omega))
  · intro i hi later
    obtain ⟨positive, _, bounded, fence⟩ := partition.span i hi
    have existsHere : index ≤ refs[i].firstRow + refs[i].count - 1 := by
      rcases Nat.eq_or_lt_of_le later with rfl | later
      · omega
      · have sep := partition.separated j i hj hi later
        omega
    have inRows : refs[i].firstRow + refs[i].count - 1 < rows.length := by
      have extent := partition.extent
      omega
    have ge := lower.2.2 _ existsHere inRows
    exact decide_eq_false (Std.not_lt.mpr (fence.symm ▸ ge))

theorem RefCovers.noKey {rows : List Entry} {refs : Array Ref} {key : ByteArray}
    (partition : RefCovers rows first count refs)
    (lower : LowerBound (fun i => (rowAt rows i).key) rows.length key rows.length) :
    findRef refs (fun ref => decide (ref.lastKey < key)) = none := by
  apply findRef_none
  intro i hi
  obtain ⟨positive, _, bounded, fence⟩ := partition.span i hi
  have extent := partition.extent
  exact decide_eq_true (fence.symm ▸ lower.2.1 _ (by omega))

/-- The successful read observations of the two index levels and the data
packets retained by this exact opened handle. -/
structure Handle.Observes [Monad m] [MonadExceptOf String m] (handle : Handle m)
    (rows : List Entry) : Prop where
  count : handle.rowCount = rows.length
  root : RefCovers rows 0 rows.length handle.root
  children : ∀ parent ∈ handle.root.toList, ∃ refs,
    handle.readLeaf parent = pure refs ∧ RefCovers rows parent.firstRow parent.count refs ∧
    ∀ ref ∈ refs.toList, ∃ data, handle.readData ref = pure data ∧
      ∀ i, i < ref.count → data.readRow i = .ok (rowAt rows (ref.firstRow + i))

private theorem array_getElem_mem {xs : Array α} {i : Nat} (inside : i < xs.size) :
    xs[i] ∈ xs.toList := by
  have bound : i < xs.toList.length := by simpa using inside
  exact List.getElem_mem bound

/-- A fixed global lower bound lies at the corresponding local lower bound
when the selected block contains it. -/
theorem seek_local [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {rows : List Entry} {ref : Ref} {data : Data} {index : Nat} {key : ByteArray}
    (reads : ∀ i, i < ref.count → data.readRow i = .ok (rowAt rows (ref.firstRow + i)))
    (lower : LowerBound (fun i => (rowAt rows i).key) rows.length key index)
    (start : ref.firstRow ≤ index) (stop : index < ref.firstRow + ref.count)
    (extent : ref.firstRow + ref.count ≤ rows.length) :
    seekBetween (m := m) (fun i => liftDecode (data.readRow i)) key 0 ref.count =
      pure (index - ref.firstRow) := by
  let logical := fun i => rowAt rows (ref.firstRow + i)
  let pred := fun i => decide ((logical i).key < key)
  have readCorrect : ∀ i, i < ref.count → liftDecode (m := m) (data.readRow i) = pure (logical i) := by
    intro i hi
    simp [reads i hi, liftDecode, logical]
  rw [seekBetween_eq_lowerBound _ logical ref.count readCorrect key 0 ref.count (Nat.le_refl _)]
  have partition : Alvoki.Partition pred ref.count (index - ref.firstRow) := by
    refine ⟨by omega, ?_, ?_⟩
    · intro i earlier
      exact decide_eq_true (lower.2.1 _ (by omega))
    · intro i later inside
      exact decide_eq_false (Std.not_lt.mpr (lower.2.2 _ (by omega) (by omega)))
  rw [lowerBound_eq_of_partition partition]

private theorem Handle.locate_at [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {handle : Handle m} {rows : List Entry} {index : Nat} {key : ByteArray}
    (observed : handle.Observes rows)
    (lower : LowerBound (fun i => (rowAt rows i).key) rows.length key index)
    (inside : index < rows.length) :
    ∃ ref data, handle.locate key = pure (some (ref, data, index - ref.firstRow)) ∧
      ref.firstRow ≤ index ∧ data.readRow (index - ref.firstRow) = .ok rows[index] := by
  obtain ⟨j, hj, pickLeaf, leafStart, leafStop⟩ :=
    observed.root.selectKey lower (Nat.zero_le index) (by simpa using inside)
  obtain ⟨refs, readLeaf, covers, blocks⟩ :=
    observed.children handle.root[j] (array_getElem_mem hj)
  obtain ⟨i, hi, pickData, start, stop⟩ := covers.selectKey lower leafStart leafStop
  obtain ⟨data, readData, readRows⟩ := blocks refs[i] (array_getElem_mem hi)
  have rowInside : index - refs[i].firstRow < refs[i].count := by omega
  have extent : refs[i].firstRow + refs[i].count ≤ rows.length :=
    Nat.le_trans (covers.span i hi).2.2.1 covers.extent
  have localSeek := seek_local (m := m) readRows lower start stop extent
  have rowRead := readRows (index - refs[i].firstRow) rowInside
  rw [Nat.add_sub_of_le start, rowAt_eq inside] at rowRead
  refine ⟨refs[i], data, ?_, start, rowRead⟩
  simp [Handle.locate, pickLeaf, readLeaf, pickData, readData, localSeek, rowInside]

theorem exists_lowerBound {rows : List Entry} (ordered : Ordered rows) (key : ByteArray) :
    ∃ index, LowerBound (fun i => (rowAt rows i).key) rows.length key index := by
  have sorted : ∀ i j, i ≤ j → j < rows.length →
      (rowAt rows i).key ≤ (rowAt rows j).key := by
    intro i j le inside
    rcases Nat.eq_or_lt_of_le le with rfl | lt
    · exact Std.le_refl _
    · have iInside := Nat.lt_trans lt inside
      rw [rowAt_eq iInside, rowAt_eq inside]
      exact Std.le_of_lt (ordered.rel_getElem_of_lt iInside inside lt)
  obtain ⟨index, _, lower⟩ :=
    seekBetween_correct (m := Id) (rowAt rows) (rowAt rows) rows.length (fun _ _ => rfl)
      sorted key
  exact ⟨index, lower⟩

/-- Unified seek agrees with the same logical lower-bound contract as the
single-row reader. Its executable search routes by the decoded fences. -/
theorem Handle.seek_observed [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {handle : Handle m} {rows : List Entry} (observed : handle.Observes rows)
    (ordered : Ordered rows) (key : ByteArray) :
    ∃ index, handle.seek key = pure index ∧ Contents.IsSeek rows key index := by
  obtain ⟨index, lower⟩ := exists_lowerBound ordered key
  refine ⟨index, ?_, lower⟩
  by_cases inside : index < rows.length
  · obtain ⟨ref, data, located, start, _⟩ := handle.locate_at observed lower inside
    simp [Handle.seek, located, Nat.add_sub_of_le start]
  · have atEnd : index = rows.length := by have := lower.1; omega
    subst index
    have noKey := observed.root.noKey lower
    simp [Handle.seek, Handle.locate, noKey, observed.count]

/-- Iteration calls the same verified data decoder selected by row ranges. -/
theorem Handle.next_observed [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {handle : Handle m} {rows : List Entry} (observed : handle.Observes rows) (index : Nat) :
    handle.next index = pure (Contents.next rows index) := by
  by_cases inside : index < rows.length
  · obtain ⟨j, hj, pickLeaf, leafStart, leafStop⟩ :=
      observed.root.selectRow (Nat.zero_le index) (by simpa using inside)
    obtain ⟨refs, readLeaf, covers, blocks⟩ :=
      observed.children handle.root[j] (array_getElem_mem hj)
    obtain ⟨i, hi, pickData, start, stop⟩ := covers.selectRow leafStart leafStop
    obtain ⟨data, readData, readRows⟩ := blocks refs[i] (array_getElem_mem hi)
    have rowRead := readRows (index - refs[i].firstRow) (by omega)
    rw [Nat.add_sub_of_le start, rowAt_eq inside] at rowRead
    simp [Handle.next, Contents.next, observed.count, inside, Nat.not_le_of_lt inside,
      pickLeaf, readLeaf, pickData, readData, rowRead, liftDecode]
  · simp [Handle.next, Contents.next, observed.count, inside, Nat.le_of_not_gt inside]

private theorem hit_atLowerBound {rows : List Entry} {key : ByteArray}
    (ordered : Ordered rows)
    (lower : LowerBound (fun i => (rowAt rows i).key) rows.length key index)
    (inside : i < rows.length) (matchKey : rows[i].key = key) : i = index := by
  apply Nat.le_antisymm
  · by_cases correct : i ≤ index
    · exact correct
    · have atIndex : index < rows.length := by omega
      have ge := lower.2.2 index (Nat.le_refl _) atIndex
      have lt := ordered.rel_getElem_of_lt atIndex inside (by omega)
      change key ≤ (rowAt rows index).key at ge
      rw [rowAt_eq atIndex] at ge
      rw [matchKey] at lt
      exact False.elim (Std.not_lt.mpr ge lt)
  · by_cases correct : index ≤ i
    · exact correct
    · have smaller := lower.2.1 i (by omega)
      change (rowAt rows i).key < key at smaller
      rw [rowAt_eq inside, matchKey] at smaller
      exact False.elim (Std.lt_irrefl smaller)

theorem lookup_of_lowerBound {rows : List Entry} {key : ByteArray}
    (ordered : Ordered rows)
    (lower : LowerBound (fun i => (rowAt rows i).key) rows.length key index) :
    Contents.lookup rows key =
      if inside : index < rows.length then
        if rows[index].key = key then some rows[index].value else none
      else none := by
  unfold Contents.lookup
  cases found : rows.find? (fun row => row.key == key) with
  | none =>
    by_cases inside : index < rows.length
    · have absent := List.find?_eq_none.mp found rows[index] (List.getElem_mem inside)
      have different : rows[index].key ≠ key := fun same => absent (beq_iff_eq.mpr same)
      simp [inside, different]
    · simp [inside]
  | some row =>
    obtain ⟨i, inside, same⟩ := List.mem_iff_getElem.mp (List.mem_of_find?_eq_some found)
    have keyEq : rows[i].key = key := by
      rw [same]
      exact beq_iff_eq.mp (List.find?_some (p := fun entry : Entry => entry.key == key) found)
    have here := hit_atLowerBound ordered lower inside keyEq
    subst i
    rw [same] at keyEq
    simp [inside, keyEq, same]

/-- A lookup uses the selected data packet directly. This proof covers the
executable lookup that reuses the located packet for the final comparison. -/
theorem Handle.lookup_observed [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {handle : Handle m} {rows : List Entry} (observed : handle.Observes rows)
    (ordered : Ordered rows) (key : ByteArray) :
    handle.lookup key = pure (Contents.lookup rows key) := by
  obtain ⟨index, lower⟩ := exists_lowerBound ordered key
  rw [lookup_of_lowerBound ordered lower]
  by_cases inside : index < rows.length
  · obtain ⟨ref, data, located, _, readRow⟩ := handle.locate_at observed lower inside
    simp [Handle.lookup, located, inside, readRow, liftDecode]
  · have atEnd : index = rows.length := by have := lower.1; omega
    subst index
    have noKey := observed.root.noKey lower
    simp [Handle.lookup, Handle.locate, noKey]

end ImmutableSSTable.Unified
