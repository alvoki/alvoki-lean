import Alvoki.Experiments.SSTable.Builder
import Alvoki.Experiments.SSTable.Proofs.Format

namespace ImmutableSSTable

open Std

private def before (key : ByteArray) (prev : Option ByteArray) : Prop :=
  ∀ p ∈ prev, p < key

private theorem all_before (key : ByteArray) (prev : Option ByteArray) :
    prev.all (fun p => decide (p < key)) = true ↔ before key prev := by
  simp [Option.all_eq_true, before]

theorem push_rejects_key {state : BuilderState} (previous : state.lastKey = some key)
    (bad : row.key ≤ key) :
    state.push row = .error "SSTable keys must strictly increase" := by
  have notBefore : ¬ key < row.key := Std.not_lt.mpr bad
  simp [BuilderState.push, previous, notBefore, throw]
  rfl

private def advance (state : BuilderState) (row : Entry) : BuilderState :=
  ⟨state.count + 1, state.dataEnd + entrySize row, some row.key⟩

private def fitsFile (state : BuilderState) (rows : List Entry) : Prop :=
  state.dataEnd + (encodeRows rows).size + 8 * (state.count + rows.length + 1) + footerSize ≤
    maxFileSize

private def Valid (state : BuilderState) (room : Nat) (rows : List Entry) : Prop :=
  rows.length ≤ room ∧ Ordered rows ∧
    (∀ row ∈ rows, before row.key state.lastKey) ∧
    (∀ row ∈ rows, (encodeEntry row).size ≤ maxRowSize) ∧ fitsFile state rows

private def Accepts (state : BuilderState) (row : Entry) : Prop :=
  before row.key state.lastKey ∧ entrySize row ≤ maxRowSize ∧ fitsFile (advance state row) []

private theorem push_ok (state : BuilderState) (row : Entry) (ok : Accepts state row) :
    state.push row = .ok (advance state row, encodeEntry row) := by
  obtain ⟨ordered, size, extent⟩ := ok
  have ordered' := (all_before row.key state.lastKey).mpr ordered
  have extent' : state.dataEnd + entrySize row + 8 * (state.count + 1 + 1) + footerSize ≤
      maxFileSize := by
    simpa [fitsFile, advance, encodeRows] using extent
  simp [BuilderState.push, ordered', size, extent', advance, Pure.pure, Except.pure]

private theorem push_error (state : BuilderState) (row : Entry) (bad : ¬Accepts state row) :
    ∃ error, state.push row = .error error := by
  by_cases order : state.lastKey.all (fun prev => decide (prev < row.key)) = true
  · by_cases size : entrySize row ≤ maxRowSize
    · have extent : ¬state.dataEnd + entrySize row + 8 * (state.count + 1 + 1) + footerSize ≤
          maxFileSize := by
        intro fileFits
        have finalFits : fitsFile (advance state row) [] := by
          simpa [fitsFile, advance, encodeRows] using fileFits
        exact bad ⟨(all_before _ _).mp order, size, finalFits⟩
      exact ⟨"SSTable file exceeds signed offset limit", by
        simp [BuilderState.push, order, size, extent, throw]
        rfl⟩
    · exact ⟨"SSTable row exceeds format size limit", by
      simp [BuilderState.push, order, size, throw]
      rfl⟩
  · exact ⟨"SSTable keys must strictly increase", by
    simp [BuilderState.push, order, throw]
    rfl⟩

private theorem fitsFile_cons (state : BuilderState) (row : Entry) (tail : List Entry) :
    fitsFile state (row :: tail) ↔ fitsFile (advance state row) tail := by
  simp [fitsFile, advance, encodeRows, encodeEntry_size]
  omega

private theorem fitsFile_nil_of_fitsFile (state : BuilderState) (rows : List Entry)
    (fits : fitsFile state rows) : fitsFile state [] := by
  simp [fitsFile, encodeRows] at *
  omega

private theorem valid_cons (state : BuilderState) (room : Nat) (row : Entry) (tail : List Entry) :
    Valid state (room + 1) (row :: tail) ↔
      Accepts state row ∧ Valid (advance state row) room tail := by
  constructor
  · rintro ⟨count, sorted, later, sizes, extent⟩
    obtain ⟨ahead, sorted⟩ := List.pairwise_cons.mp sorted
    have rest := (fitsFile_cons state row tail).mp extent
    refine ⟨⟨later row (by simp), ?_, fitsFile_nil_of_fitsFile _ _ rest⟩,
      ?_, sorted, ?_, fun r member => sizes r (List.mem_cons_of_mem _ member), rest⟩
    · simpa only [encodeEntry_size] using sizes row (by simp)
    · simpa using count
    · intro r member key previous
      have same : row.key = key := Option.mem_some.mp previous
      simpa only [← same] using ahead r member
  · rintro ⟨⟨ahead, size, _⟩, count, sorted, later, sizes, extent⟩
    have next : ∀ r ∈ tail, row.key < r.key := fun r member => later r member row.key rfl
    refine ⟨by simpa using count, List.pairwise_cons.mpr ⟨next, sorted⟩, ?_, ?_,
      (fitsFile_cons state row tail).mpr extent⟩
    · intro r member key previous
      rcases List.mem_cons.mp member with rfl | inside
      · exact ahead key previous
      · exact Std.lt_trans (ahead key previous) (next r inside)
    · intro r member
      rcases List.mem_cons.mp member with rfl | inside
      · simpa only [encodeEntry_size] using size
      · exact sizes r inside

/-- A fresh pair of append streams with successful I/O. The offset stream is
copied verbatim when finalized. The native sink performs that copy in chunks. -/
private structure BuildState where
  rows : List Entry
  data : ByteArray := .empty
  offsets : ByteArray := .empty

private abbrev BuildM := StateT BuildState (Except String)

private def modelSink : Sink BuildM where
  writeData bytes := fun s => .ok ((), {s with data := s.data ++ bytes})
  writeOffset bytes := fun s => .ok ((), {s with offsets := s.offsets ++ bytes})
  appendOffsets := fun s => .ok ((), {s with data := s.data ++ s.offsets})
  flush := pure ()

private def modelNext : BuildM (Option Entry) := fun s =>
  match s.rows with
  | [] => .ok (none, s)
  | row :: tail => .ok (some row, {s with rows := tail})

def modelBuild (rows : List Entry) : Except String (Nat × ByteArray) := do
  let (count, file) ← (buildStream modelSink modelNext id).run {rows}
  return (count, file.data)

private theorem streamRows_spec (rows : List Entry) (state : BuilderState) (room : Nat)
    (currentFits : fitsFile state []) (data offsets : ByteArray) :
    match (streamRows modelSink modelNext id state room).run ⟨rows, data, offsets⟩ with
    | .error _ => ¬Valid state room rows
    | .ok (last, file) => Valid state room rows ∧ last.count = state.count + rows.length ∧
        last.dataEnd = state.dataEnd + (encodeRows rows).size ∧
        file.rows = [] ∧ file.data = data ++ encodeRows rows ∧
        file.offsets ++ encodeOffset last.dataEnd = offsets ++ encodeOffsets state.dataEnd rows := by
  induction rows generalizing state room data offsets with
  | nil =>
    simp [fitsFile, encodeRows] at currentFits
    cases room <;> simp [streamRows, modelNext, Valid, Ordered, fitsFile, currentFits, encodeRows,
      encodeOffsets, Bind.bind, StateT.bind, Pure.pure, StateT.pure, Except.bind, Except.pure, StateT.run]
  | cons row tail ih =>
    cases room with
    | zero =>
      change ¬Valid state 0 (row :: tail)
      simp [Valid]
    | succ room =>
      by_cases accepts : Accepts state row
      · have step := push_ok state row accepts
        have rest := ih (advance state row) room accepts.2.2
          (data ++ encodeEntry row) (offsets ++ encodeOffset state.dataEnd)
        have consumed : (streamRows modelSink modelNext id state (room + 1)).run
            ⟨row :: tail, data, offsets⟩ =
            (streamRows modelSink modelNext id (advance state row) room).run
            ⟨tail, data ++ encodeEntry row, offsets ++ encodeOffset state.dataEnd⟩ := by
          simp only [streamRows, modelNext, step, modelSink, Bind.bind, StateT.bind, StateT.run, Except.bind]
        rw [consumed]
        cases received : (streamRows modelSink modelNext id (advance state row) room).run
            ⟨tail, data ++ encodeEntry row, offsets ++ encodeOffset state.dataEnd⟩ with
        | error error =>
          rw [received] at rest
          exact fun valid => rest ((valid_cons ..).mp valid).2
        | ok out =>
          obtain ⟨last, file⟩ := out
          rw [received] at rest
          obtain ⟨valid, count, extent, exhausted, written, indexed⟩ := rest
          refine ⟨(valid_cons ..).mpr ⟨accepts, valid⟩, ?_, ?_, exhausted, ?_, ?_⟩
          · simp [advance] at count ⊢
            omega
          · simp [advance, encodeRows, encodeEntry_size] at extent ⊢
            omega
          · simpa only [encodeRows, ByteArray.append_assoc] using written
          · simpa only [advance, encodeOffsets, encodeEntry_size, ByteArray.append_assoc] using indexed
      · obtain ⟨error, failed⟩ := push_error state row accepts
        simp only [streamRows, modelNext, failed, Bind.bind, StateT.bind, StateT.run, Except.bind]
        change ¬ Valid state (room + 1) (row :: tail)
        exact fun valid => accepts ((valid_cons ..).mp valid).1

private theorem initial_valid (rows : List Entry) :
    Valid {} maxRows rows ↔ Fits rows ∧ Ordered rows := by
  constructor
  · rintro ⟨_, ordered, _, sizes, extent⟩
    exact ⟨⟨sizes, by simpa [fitsFile] using extent⟩, ordered⟩
  · rintro ⟨⟨sizes, extent⟩, ordered⟩
    have length : rows.length ≤ maxRows := by
      unfold maxRows
      exact (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
    exact ⟨length, ordered, by simp [before], sizes, by simpa [fitsFile] using extent⟩

/-- Building over healthy fresh streams succeeds exactly when the rows are
ordered and fit the format. The result is the count and complete wire image. -/
theorem modelBuild_ok_iff {rows : List Entry} {count : Nat} {bytes : ByteArray} :
    modelBuild rows = .ok (count, bytes) ↔
      Fits rows ∧ Ordered rows ∧ count = rows.length ∧ bytes = encodeImage rows := by
  have initial : fitsFile {} [] := by unfold fitsFile; decide
  have spec := streamRows_spec rows {} maxRows initial .empty .empty
  cases body : (streamRows modelSink modelNext id {} maxRows).run {rows} with
  | error error =>
    rw [body] at spec
    have failed : modelBuild rows = .error error := by
      simp only [modelBuild, buildStream, Sink.writeTable, Bind.bind, StateT.bind, StateT.run]
      rw [show streamRows modelSink modelNext id {} maxRows {rows} = .error error from body]
      rfl
    rw [failed]
    simp only [reduceCtorEq, false_iff]
    rintro ⟨fits, ordered, _, _⟩
    exact spec ((initial_valid rows).mpr ⟨fits, ordered⟩)
  | ok out =>
    obtain ⟨last, file⟩ := out
    rw [body] at spec
    obtain ⟨valid, length, extent, _, written, indexed⟩ := spec
    obtain ⟨fits, ordered⟩ := (initial_valid rows).mp valid
    have length' : last.count = rows.length := by simpa using length
    have extent' : last.dataEnd = (encodeRows rows).size := by simpa using extent
    have result : modelBuild rows = .ok (rows.length, encodeImage rows) := by
      unfold modelBuild buildStream Sink.writeTable
      simp only [Bind.bind, StateT.bind, StateT.run]
      rw [show streamRows modelSink modelNext id {} maxRows {rows} = .ok (last, file) from body]
      have index' : file.offsets ++ encodeOffset (encodeRows rows).size = encodeOffsets 0 rows := by
        simpa [extent'] using indexed
      simp [modelSink, Except.bind, Pure.pure, StateT.pure, Except.pure, written, index', length',
        extent', encodeImage]
    rw [result, Except.ok.injEq, Prod.mk.injEq]
    simp [fits, ordered, eq_comm]

theorem modelBuild_ok {rows : List Entry} {count : Nat} {bytes : ByteArray}
    (built : modelBuild rows = .ok (count, bytes)) :
    Fits rows ∧ Ordered rows ∧ count = rows.length ∧ bytes = encodeImage rows :=
  modelBuild_ok_iff.mp built

end ImmutableSSTable
