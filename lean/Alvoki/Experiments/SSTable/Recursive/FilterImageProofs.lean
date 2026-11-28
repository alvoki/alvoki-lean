import Alvoki.Experiments.SSTable.Recursive.Image
import Alvoki.Experiments.SSTable.Recursive.FilteredReader

namespace ImmutableSSTable.Recursive

open Unified (Layout Ref Checksum)

theorem FilterAt.read [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {source : Source m} (filter : FilterAt layout crc image ref entries)
    (served : source.Serves image) :
    readFilter source crc layout.tableId ref = pure (Bloom.build entries) := by
  have ends : ref.offset - filterPacketSize ref.count + filterPacketSize ref.count ≤ ref.offset :=
    Nat.le_of_eq (Nat.sub_add_cancel filter.within)
  simp [readFilter, filter.within, filter.packet.read served ends]

theorem FilterAt.accepts [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {source : Source m} (filter : FilterAt layout crc image ref entries)
    (served : source.Serves image) (entry : Entry) (member : entry ∈ entries.toList) :
    (Bloom.mayContain · entry.key) <$> readFilter source crc layout.tableId ref = pure true := by
  rw [filter.read served, map_pure, Bloom.build_covers _ _ member]

/-- Checking an advertised region returns a definite negative only for keys
outside the exact rows in its data block. Every encoded value participates. -/
theorem DataAt.checkedFilter [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {handle : Handle m} (data : DataAt handle.layout handle.crc image rows ref parent handle.filtered)
    (served : handle.source.Serves image) (enabled : handle.filtered = true) (key : ByteArray) :
    ∃ maybe, handle.checkFilter ref key = pure maybe ∧
      (∀ i, ref.firstRow ≤ i → i < ref.firstRow + ref.count →
        (rowAt rows i).key = key → maybe = true) := by
  by_cases active : useFilter ref.count = true
  · obtain ⟨block, count, _, rowsMatch, _, _, filter⟩ := data.body
    have stored := filter enabled active
    refine ⟨Bloom.mayContain (Bloom.build block) key, ?_, ?_⟩
    · simp [Handle.checkFilter, active, stored.read served]
    · intro i start stop query
      have inside : i - ref.firstRow < block.size := by omega
      have row := rowsMatch (i - ref.firstRow) inside
      rw [Nat.add_sub_of_le start] at row
      have keyMatch : (block[i - ref.firstRow]'inside).key = key :=
        (congrArg Entry.key row).trans query
      rw [← keyMatch]
      exact Bloom.build_covers block _ (by simp)
  · exact ⟨true, by simp [Handle.checkFilter, active], fun _ _ _ _ => rfl⟩

private theorem DataAt.lookupInData [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {handle : Handle m} (data : DataAt handle.layout handle.crc image rows ref parent handle.filtered)
    (served : handle.source.Serves image) (valid : handle.layout.Valid)
    (lower : LowerBound (fun i => (rowAt rows i).key) rows.length key index)
    (start : ref.firstRow ≤ index) (stop : index < ref.firstRow + ref.count)
    (inside : index < rows.length) :
    handle.lookupInData ref parent key =
      pure (if rows[index].key = key then some rows[index].value else none) := by
  obtain ⟨decoded, readData, reads⟩ := data.read served valid
  have localSeek := Unified.seek_local (m := m) reads lower start stop data.rowExtent
  have inBlock : index - ref.firstRow < ref.count := by omega
  have row := reads _ inBlock
  rw [Nat.add_sub_of_le start, rowAt_eq inside] at row
  simp only [Handle.lookupInData, readData, pure_bind, localSeek, inBlock, ↓reduceIte, row]
  simp [liftDecode]

theorem Handle.Observes.filtered_represents [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {handle : Handle m} (observed : handle.Observes image rows) (ordered : Ordered rows) :
    handle.filteredTable.Represents rows := by
  have baseline := observed.represents ordered
  refine ⟨ordered, baseline.rowCount, ?_, baseline.seek, baseline.next⟩
  intro key
  change handle.filteredLookup key = _
  by_cases enabled : handle.filtered = true
  · obtain ⟨index, lower⟩ := Unified.exists_lowerBound ordered key
    rw [Unified.lookup_of_lowerBound ordered lower]
    by_cases inside : index < rows.length
    · obtain ⟨rootChild, ref, parent, selected, descended, data, start, stop⟩ :=
        observed.route (Routes.key lower) inside
      obtain ⟨maybe, checked, safe⟩ := data.checkedFilter observed.serves enabled key
      have exact := data.lookupInData observed.serves observed.valid lower start stop inside
      cases observedBit : maybe with
      | false =>
        have distinct : rows[index].key ≠ key := by
          intro hit
          have result := safe index start stop (by simpa [rowAt_eq inside])
          simp [observedBit] at result
        simp [Handle.filteredLookup, enabled, selected, descended, checked, observedBit, inside, distinct]
      | true =>
        simp [Handle.filteredLookup, enabled, selected, descended, checked, observedBit, inside, exact]
    · have atEnd : index = rows.length := by have := lower.1; omega
      subst index
      simp [Handle.filteredLookup, enabled, observed.root.noKey lower]
  · simpa [Handle.filteredLookup, Handle.table, Bool.eq_false_iff.mpr enabled] using baseline.lookup key

theorem Image.open_filtered_represents [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {source : Source m} (exact : Image layout crc image rows) (served : source.Serves image) :
    ∃ handle, openChecked source crc layout.tableId = pure handle ∧ handle.filteredTable.Represents rows := by
  obtain ⟨handle, opened, observed⟩ := exact.open_observes served
  exact ⟨handle, opened, observed.filtered_represents exact.ordered⟩

end ImmutableSSTable.Recursive
