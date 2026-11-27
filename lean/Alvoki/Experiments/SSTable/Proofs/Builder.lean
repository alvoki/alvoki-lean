import Alvoki.Experiments.SSTable.Builder
import Alvoki.Experiments.SSTable.Proofs.Format

namespace ImmutableSSTable

theorem push_rejects_key {state : BuilderState} (room : state.count < maxRows)
    (previous : state.lastKey = some key) (bad : row.key ≤ key) :
    state.push row = .error "SSTable keys must strictly increase" := by
  simp [BuilderState.push, Nat.not_le.mpr room, previous, bad]
  rfl

private theorem push_ok {state : BuilderState} (room : state.count < maxRows)
    (ordered : ∀ prev ∈ state.lastKey, prev < row.key) :
    state.push row = .ok (⟨state.count + 1, some row.key⟩, encodeEntry row) := by
  cases h : state.lastKey with
  | none => simp [BuilderState.push, Nat.not_le.mpr room, h]; rfl
  | some key =>
    have good : key < row.key := ordered key (by simp [h])
    simp [BuilderState.push, Nat.not_le.mpr room, h, UInt64.not_le.mpr good]
    rfl

/-- The committed bytes are split at the file cursor. Writes accumulate in
    `pending` until flush, which overwrites the corresponding suffix. Rewind
    requires a flushed cursor. The row supplier and file belong to one run. -/
private structure BuildState where
  rows : List Entry
  left : ByteArray := .empty
  right : ByteArray := .empty
  pending : ByteArray := .empty

private abbrev BuildM := StateT BuildState (Except String)

private def modelSink : Sink BuildM where
  write bytes := modify fun s => {s with pending := s.pending ++ bytes}
  flush := modify fun s =>
    {s with left := s.left ++ s.pending, right := s.right.extract s.pending.size s.right.size, pending := .empty}
  rewind := fun s =>
    if s.pending.isEmpty then .ok ((), {s with left := .empty, right := s.left ++ s.right})
    else .error "cannot rewind with pending output"

private def modelNext : BuildM (Option Entry) := fun s =>
  match s.rows with
  | [] => .ok (none, s)
  | row :: tail => .ok (some row, {s with rows := tail})

/-- Result and flushed file contents of the exact native construction schedule
    interpreted with successful positional file operations on a fresh file. -/
def modelBuild (rows : List Entry) : Except String (Nat × ByteArray) := do
  let (count, file) ← (buildStream modelSink modelNext id).run {rows}
  return (count, file.left ++ file.right)

/-- Valid continuation of an existing streaming writer. -/
private def Valid (state : BuilderState) (room : Nat) (rows : List Entry) : Prop :=
  rows.length ≤ room ∧ rows.Pairwise (fun a b => a.key < b.key) ∧
    ∀ key ∈ state.lastKey, ∀ r ∈ rows, key < r.key

private theorem valid_cons (state : BuilderState) (room : Nat) (row : Entry) (tail : List Entry) :
    Valid state (room + 1) (row :: tail) ↔
      (∀ key ∈ state.lastKey, key < row.key) ∧ Valid ⟨state.count + 1, some row.key⟩ room tail := by
  constructor
  · rintro ⟨fits, sorted, later⟩
    obtain ⟨ahead, sorted⟩ := List.pairwise_cons.mp sorted
    exact ⟨fun key member => later key member row (by simp), by simpa using fits, sorted,
      fun key member => (Option.some.inj member) ▸ ahead⟩
  · rintro ⟨ahead, fits, sorted, later⟩
    have next := later row.key rfl
    refine ⟨by simpa using fits, List.pairwise_cons.mpr ⟨next, sorted⟩, ?_⟩
    intro key member r present
    rcases List.mem_cons.mp present with rfl | inside
    · exact ahead key member
    · exact UInt64.lt_trans (ahead key member) (next r inside)

/-- The actual streaming loop consumes all supplied rows on success. Failure
    is possible in this fresh-file model precisely when the remaining input
    violates capacity or ordering. -/
private theorem streamRows_spec (rows : List Entry) (state : BuilderState) (room : Nat)
    (remaining : state.count + room = maxRows) (written : ByteArray) :
    match (streamRows modelSink modelNext id state room).run ⟨rows, .empty, .empty, written⟩ with
    | .error _ => ¬ Valid state room rows
    | .ok (last, file) => Valid state room rows ∧ last.count = state.count + rows.length ∧
        file = ⟨[], .empty, .empty, written ++ encodeRows rows⟩ := by
  induction rows generalizing state room written with
  | nil =>
    cases room <;> simp [streamRows, modelNext, Valid, encodeRows, Bind.bind, StateT.bind,
      Pure.pure, StateT.pure, Except.bind, Except.pure, StateT.run]
  | cons row tail ih =>
    cases room with
    | zero =>
      simp [streamRows, modelNext, Valid, Bind.bind, StateT.bind, StateT.run, Except.bind, throw]
      trivial
    | succ room =>
      by_cases ahead : ∀ key ∈ state.lastKey, key < row.key
      · let next : BuilderState := ⟨state.count + 1, some row.key⟩
        have step : state.push row = .ok (next, encodeEntry row) := push_ok (by omega) ahead
        have rest := ih next room (by dsimp [next]; omega) (written ++ encodeEntry row)
        have consumed : (streamRows modelSink modelNext id state (room + 1)).run
            ⟨row :: tail, .empty, .empty, written⟩ = (streamRows modelSink modelNext id next room).run
            ⟨tail, .empty, .empty, written ++ encodeEntry row⟩ := by
          simp only [streamRows, modelNext, step, Bind.bind, StateT.bind, StateT.run, Except.bind]
          rfl
        rw [consumed]
        cases received : (streamRows modelSink modelNext id next room).run
            ⟨tail, .empty, .empty, written ++ encodeEntry row⟩ with
        | error => rw [received] at rest; exact fun valid => rest ((valid_cons ..).mp valid).2
        | ok out =>
          obtain ⟨last, file⟩ := out
          rw [received] at rest
          obtain ⟨valid, count, actual⟩ := rest
          refine ⟨(valid_cons ..).mpr ⟨ahead, valid⟩, ?_, ?_⟩
          · dsimp [next] at count; simp only [List.length_cons]; omega
          · simpa only [encodeRows_cons, ByteArray.append_assoc] using actual
      · cases prev : state.lastKey with
        | none => simp [prev] at ahead
        | some key =>
          have bad : row.key ≤ key := UInt64.not_lt.mp (fun good => ahead (by simpa [prev] using good))
          have failed := push_rejects_key (by omega : state.count < maxRows) prev bad
          simp only [streamRows, modelNext, failed, Bind.bind, StateT.bind, StateT.run, Except.bind]
          exact fun valid => ahead ((valid_cons ..).mp valid).1

/-- Finalize the buffered sink after the source loop returned its actual file
    or error. Backpatching the header preserves all previously emitted rows. -/
private theorem finish_modelBuild (rows : List Entry) (action : BuildM BuilderState)
    (last : BuilderState) (bytes : ByteArray)
    (ok : action.run ⟨rows, .empty, .empty, placeholder⟩ =
      .ok (last, ⟨[], .empty, .empty, placeholder ++ bytes⟩)) :
    (do let (count, file) ← (modelSink.writeTable action).run {rows}
        pure (count, file.left ++ file.right)) = (.ok (last.count, last.header ++ bytes) : Except String _) := by
  have tailBytes : (placeholder ++ bytes).extract last.header.size (placeholder ++ bytes).size = bytes := by
    apply ByteArray.extract_append_eq_right
    · rw [BuilderState.header, encodeHeader_size]; rfl
    · simp
  have noTail (i : Nat) : ByteArray.empty.extract i ByteArray.empty.size = ByteArray.empty :=
    ByteArray.extract_eq_empty_iff.mpr (by simp)
  simp only [Sink.writeTable, Bind.bind, StateT.bind, StateT.run, modelSink, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, Pure.pure, StateT.pure, Except.bind, Except.pure,
    ByteArray.empty_append]
  dsimp only [StateT.run] at ok
  rw [ok]
  simp only [show ByteArray.empty.isEmpty = true from rfl, ↓reduceIte, ByteArray.empty_append,
    noTail, ByteArray.append_empty, tailBytes]

/-- On the fresh, buffered model file, the actual build schedule succeeds
    exactly for ordered inputs within the format limit. Its returned count
    and its flushed bytes are determined by the supplied sequence. -/
theorem modelBuild_ok_iff {rows : List Entry} {count : Nat} {bytes : ByteArray} :
    modelBuild rows = .ok (count, bytes) ↔
    rows.length ≤ maxRows ∧ rows.Pairwise (fun a b => a.key < b.key) ∧
    count = rows.length ∧ bytes = encodeImage rows := by
  have spec := streamRows_spec rows {} maxRows (by simp) placeholder
  let action := streamRows modelSink modelNext id {} maxRows
  cases done_ : action.run ⟨rows, .empty, .empty, placeholder⟩ with
  | error e =>
    change (streamRows modelSink modelNext id {} maxRows).run _ = _ at done_
    rw [done_] at spec
    have fail : modelBuild rows = .error e := by
      change (do let (n, file) ← (modelSink.writeTable action).run {rows}; pure (n, file.left ++ file.right)) = _
      unfold Sink.writeTable
      simp only [Bind.bind, StateT.bind, StateT.run, modelSink, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, Pure.pure, StateT.pure, Except.bind, Except.pure, ByteArray.empty_append]
      change action ⟨rows, .empty, .empty, placeholder⟩ = .error e at done_
      rw [done_]
    rw [fail]
    simp only [reduceCtorEq, false_iff, not_and]
    intro fits ordered
    exact False.elim (spec ⟨fits, ordered, by simp⟩)
  | ok out =>
    obtain ⟨last, file⟩ := out
    change (streamRows modelSink modelNext id {} maxRows).run _ = _ at done_
    rw [done_] at spec
    obtain ⟨valid, length, rfl⟩ := spec
    have length' : last.count = rows.length := by simpa using length
    have result : modelBuild rows = .ok (last.count, last.header ++ encodeRows rows) :=
      finish_modelBuild rows action last _ done_
    rw [result, BuilderState.header, length']
    simp [encodeImage, valid.1, valid.2.1, eq_comm]

end ImmutableSSTable
