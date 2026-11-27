import Alvoki.Experiments.SSTable.Core

namespace ImmutableSSTable

/-- A failed probe on the search's required path. Each preceding comparison
records the actual row and the state supplied to the following probe. -/
inductive RequiredProbeError {σ : Type} (read : Nat → EStateM String σ Entry)
    (key : ByteArray) (message : String) (reached : σ) : Nat → Nat → σ → Prop where
  | here (range : lo < hi)
      (failed : read (lo + (hi - lo) / 2) before = .error message reached) :
      RequiredProbeError read key message reached lo hi before
  | right (range : lo < hi)
      (got : read (lo + (hi - lo) / 2) before = .ok row after)
      (less : row.key < key)
      (later : RequiredProbeError read key message reached (lo + (hi - lo) / 2 + 1) hi after) :
      RequiredProbeError read key message reached lo hi before
  | left (range : lo < hi)
      (got : read (lo + (hi - lo) / 2) before = .ok row after)
      (notLess : ¬row.key < key)
      (later : RequiredProbeError read key message reached lo (lo + (hi - lo) / 2) after) :
      RequiredProbeError read key message reached lo hi before

/-- The executable search returns the first required probe's error verbatim,
including the state at which that probe fails. -/
theorem RequiredProbeError.propagates {read : Nat → EStateM String σ Entry}
    (path : RequiredProbeError read key message reached lo hi before) :
    seekBetween read key lo hi before = .error message reached := by
  induction path with
  | here range failed =>
    rw [seekBetween]
    simp [range, Bind.bind, EStateM.bind, failed]
  | right range got less _ ih =>
    rw [seekBetween]
    simpa [range, Bind.bind, EStateM.bind, got, less] using ih
  | left range got notLess _ ih =>
    rw [seekBetween]
    simpa [range, Bind.bind, EStateM.bind, got, notLess] using ih

theorem Table.readEntry_index_error {table : Table (EStateM String σ)} {source}
    (bound : table.BoundTo source count indexStart) (within : index < count)
    (failed : source.readAt (indexStart + 8 * index) 16 before = .error message reached) :
    table.readEntry index before = .error message reached := by
  obtain ⟨rowCount, directory, retained⟩ := bound
  simp [Table.readEntry, rowCount, within, directory, retained, Bind.bind, EStateM.bind, failed]

theorem Table.readEntry_index_decode_error {table : Table (EStateM String σ)} {source}
    (bound : table.BoundTo source count indexStart) (within : index < count)
    (received : source.readAt (indexStart + 8 * index) 16 before = .ok bytes reached)
    (invalid : decodeOffsetPair bytes = .error message) :
    table.readEntry index before = .error message reached := by
  obtain ⟨rowCount, directory, retained⟩ := bound
  simp [Table.readEntry, rowCount, within, directory, retained, Bind.bind, EStateM.bind,
    received, invalid, liftDecode]
  rfl

theorem Table.readEntry_source_error {table : Table (EStateM String σ)} {source}
    (bound : table.BoundTo source count indexStart) (within : index < count)
    (received : source.readAt (indexStart + 8 * index) 16 before = .ok offsets afterIndex)
    (decoded : decodeOffsetPair offsets = .ok (start, stop))
    (span : start < stop ∧ stop ≤ indexStart ∧ stop - start ≤ maxRowSize)
    (failed : source.readAt start (stop - start) afterIndex = .error message reached) :
    table.readEntry index before = .error message reached := by
  obtain ⟨rowCount, directory, retained⟩ := bound
  simp [Table.readEntry, rowCount, within, directory, retained, Bind.bind, EStateM.bind,
    received, decoded, liftDecode, Pure.pure, EStateM.pure, span, (show stop ≤ maxRowSize + start by have := span.2.2; omega), failed]

theorem Table.readEntry_decode_error {table : Table (EStateM String σ)} {source}
    (bound : table.BoundTo source count indexStart) (within : index < count)
    (gotOffsets : source.readAt (indexStart + 8 * index) 16 before = .ok offsets afterIndex)
    (decoded : decodeOffsetPair offsets = .ok (start, stop))
    (span : start < stop ∧ stop ≤ indexStart ∧ stop - start ≤ maxRowSize)
    (gotRow : source.readAt start (stop - start) afterIndex = .ok bytes reached)
    (size : bytes.size = stop - start) (invalid : decodeEntry bytes = .error message) :
    table.readEntry index before = .error message reached := by
  obtain ⟨rowCount, directory, retained⟩ := bound
  simp [Table.readEntry, rowCount, within, directory, retained, Bind.bind, EStateM.bind,
    gotOffsets, decoded, liftDecode, Pure.pure, EStateM.pure, span, (show stop ≤ maxRowSize + start by have := span.2.2; omega), gotRow, size, invalid]
  rfl

theorem Table.next_read_error {table : Table (EStateM String σ)}
    (within : index < table.rowCount) (failed : table.readEntry index before = .error message reached) :
    table.next index before = .error message reached := by
  simp [Table.next, within, Bind.bind, EStateM.bind, failed]

theorem Table.seek_read_error {table : Table (EStateM String σ)}
    (path : RequiredProbeError table.readEntry key message reached 0 table.rowCount before) :
    table.seek key before = .error message reached :=
  path.propagates

theorem Table.lookup_search_error {table : Table (EStateM String σ)}
    (path : RequiredProbeError table.readEntry key message reached 0 table.rowCount before) :
    table.lookup key before = .error message reached := by
  simp [Table.lookup, Bind.bind, EStateM.bind, Table.seek_read_error path]

/-- The final lookup read can fail even after a successful seek. Its callback
is issued from the state reached by that exact seek. -/
theorem Table.lookup_final_read_error {table : Table (EStateM String σ)}
    (located : table.seek key before = .ok index afterSeek) (within : index < table.rowCount)
    (failed : table.readEntry index afterSeek = .error message reached) :
    table.lookup key before = .error message reached := by
  simp [Table.lookup, Bind.bind, EStateM.bind, located, Table.next_read_error within failed]

end ImmutableSSTable
