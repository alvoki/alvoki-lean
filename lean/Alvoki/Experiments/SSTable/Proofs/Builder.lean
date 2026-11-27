import Alvoki.Experiments.SSTable.Builder
import Alvoki.Experiments.SSTable.Proofs.Format

namespace ImmutableSSTable

/-- Observe the state and concatenated output of successive native builder pushes.
    The native sink writes each chunk immediately. It does not retain this trace. -/
def runPushes (state : BuilderState) : List Entry → Except String (BuilderState × ByteArray)
  | [] => .ok (state, ByteArray.empty)
  | row :: rest => do
    let (next, bytes) ← state.push row
    let (last, suffix) ← runPushes next rest
    return (last, bytes ++ suffix)

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

private theorem runPushes_from (rows : List Entry) (state : BuilderState)
    (fits : state.count + rows.length ≤ maxRows)
    (ordered : rows.Pairwise (fun a b => a.key < b.key))
    (afterLast : ∀ prev ∈ state.lastKey, ∀ r ∈ rows, prev < r.key) :
    ∃ last, runPushes state rows = .ok (last, encodeRows rows) ∧
      last.count = state.count + rows.length := by
  induction rows generalizing state with
  | nil => exact ⟨state, rfl, by simp⟩
  | cons row rest ih =>
    obtain ⟨ahead, tailOrdered⟩ := List.pairwise_cons.mp ordered
    let next : BuilderState := ⟨state.count + 1, some row.key⟩
    have length := List.length_cons (a := row) (as := rest)
    have step : state.push row = .ok (next, encodeEntry row) :=
      push_ok (by omega) (fun prev hp => afterLast prev hp row (by simp))
    obtain ⟨last, tail, count⟩ := ih next (by dsimp [next]; omega) tailOrdered (by
      intro prev hp
      have hp' : prev = row.key := by simpa [next, Option.mem_def] using hp.symm
      simpa [hp'] using ahead)
    refine ⟨last, ?_, ?_⟩
    · simp [runPushes, step, tail, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · dsimp [next] at count
      omega

/-- For a sorted bounded input, the bytes emitted by all successful pushes and
    the actual final header together form the exact canonical file image. -/
theorem builder_constructs_image (rows : List Entry) (fits : rows.length ≤ maxRows)
    (ordered : rows.Pairwise (fun a b => a.key < b.key)) :
    ∃ last, runPushes {} rows = .ok (last, encodeRows rows) ∧
      last.count = rows.length ∧ last.header ++ encodeRows rows = encodeImage rows := by
  obtain ⟨last, output, count⟩ := runPushes_from rows {} (by simpa using fits) ordered (by simp)
  exact ⟨last, output, by simpa using count, by simp [BuilderState.header, count, encodeImage]⟩

private theorem runPushes_ordered {state : BuilderState} {rows : List Entry} {last bytes}
    (bound : state.count ≤ maxRows) (ok : runPushes state rows = .ok (last, bytes)) :
    state.count + rows.length ≤ maxRows ∧
    rows.Pairwise (fun a b => a.key < b.key) ∧
    ∀ key ∈ state.lastKey, ∀ r ∈ rows, key < r.key := by
  induction rows generalizing state last bytes with
  | nil => simp [bound]
  | cons row rest ih =>
    have room : state.count < maxRows := by
      by_cases h : state.count < maxRows
      · exact h
      · simp [runPushes, BuilderState.push, Nat.le_of_not_gt h, Bind.bind, Except.bind,
          throw] at ok
    have ordered : ∀ key ∈ state.lastKey, key < row.key := by
      intro key member
      have same : state.lastKey = some key := member
      by_cases good : key < row.key
      · exact good
      · rw [runPushes, push_rejects_key room same (UInt64.not_lt.mp good)] at ok
        contradiction
    rw [runPushes, push_ok room ordered] at ok
    let next : BuilderState := ⟨state.count + 1, some row.key⟩
    cases tail : runPushes next rest with
    | error _ =>
      simp only [next] at tail
      simp [Bind.bind, Except.bind, tail] at ok
    | ok pair =>
      obtain ⟨finalState, suffix⟩ := pair
      obtain ⟨fits, restOrdered, later⟩ := ih (by dsimp [next]; omega) tail
      have greater := later row.key rfl
      refine ⟨?_, List.pairwise_cons.mpr ⟨greater, restOrdered⟩, ?_⟩
      · dsimp [next] at fits
        simp only [List.length_cons]
        omega
      · intro key member r atRow
        rcases List.mem_cons.mp atRow with rfl | inside
        · exact ordered key member
        · exact UInt64.lt_trans (ordered key member) (greater r inside)

/-- Successful construction establishes every input premise required by the
reader, even when the caller supplied an unchecked sequence. -/
theorem builder_accepts_only_ordered {rows : List Entry} {last body}
    (ok : runPushes {} rows = .ok (last, body)) :
    rows.length ≤ maxRows ∧ rows.Pairwise (fun a b => a.key < b.key) ∧
    last.header ++ body = encodeImage rows := by
  obtain ⟨bound, sorted, _⟩ := runPushes_ordered (Nat.zero_le _) ok
  simp only [Nat.zero_add] at bound
  obtain ⟨_, encoded, _, image⟩ := builder_constructs_image rows bound sorted
  rw [ok] at encoded
  cases encoded
  exact ⟨bound, sorted, image⟩

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

private theorem push_count {state : BuilderState} {r : Entry} {next bytes}
    (ok : state.push r = .ok (next, bytes)) : next.count = state.count + 1 := by
  by_cases full : maxRows ≤ state.count
  · simp [BuilderState.push, full, Bind.bind, Except.bind, throw] at ok
  · cases h : state.lastKey with
    | none => simp [BuilderState.push, h, full, Pure.pure, Except.pure] at ok
              exact (congrArg BuilderState.count ok.1).symm
    | some k =>
      by_cases bad : r.key ≤ k
      · rw [push_rejects_key (by omega) h bad] at ok; contradiction
      · simp [BuilderState.push, h, full, bad, Pure.pure, Except.pure] at ok
        exact (congrArg BuilderState.count ok.1).symm

private theorem streamRows_eq (rows : List Entry) (state : BuilderState) (room : Nat)
    (remaining : state.count + room = maxRows) (written : ByteArray) :
    (streamRows modelSink modelNext id state room).run ⟨rows, .empty, .empty, written⟩ =
      (do let (last, body) ← runPushes state rows
          pure (last, ⟨[], .empty, .empty, written ++ body⟩) : Except String (BuilderState × BuildState)) := by
  induction rows generalizing state room written with
  | nil =>
    cases room <;> simp [streamRows, modelNext, runPushes, Bind.bind, StateT.bind, Pure.pure,
      StateT.pure, Except.bind, Except.pure, StateT.run]
  | cons row tail ih =>
    cases room with
    | zero =>
      have full : maxRows ≤ state.count := by omega
      simp [streamRows, modelNext, runPushes, BuilderState.push, full, Bind.bind, StateT.bind,
        Pure.pure, StateT.pure, Except.bind, Except.pure, StateT.run, throw]
      rfl
    | succ room =>
      cases pushed : state.push row with
      | error e =>
        simp [streamRows, modelNext, runPushes, pushed, Bind.bind, StateT.bind, Except.bind, StateT.run, throw]
        rfl
      | ok pair =>
        obtain ⟨next, bytes⟩ := pair
        have count := push_count pushed
        have rest := ih next room (by omega) (written ++ bytes)
        simp only [streamRows, modelNext, modelSink, runPushes, pushed, Bind.bind, StateT.bind,
          StateT.run, Except.bind, Pure.pure, Except.pure] at ⊢
        change (streamRows modelSink modelNext id next room).run ⟨tail, .empty, .empty, written ++ bytes⟩ = _
        rw [rest]
        cases r : runPushes next tail with
        | error e => rfl
        | ok out => obtain ⟨last, body⟩ := out; simp [Bind.bind, Except.bind, Pure.pure, Except.pure, ByteArray.append_assoc]

private theorem finish_modelBuild (rows : List Entry) (action : BuildM BuilderState)
    (loop : action.run ⟨rows, .empty, .empty, placeholder⟩ =
      (do let (last, body) ← runPushes {} rows
          pure (last, ⟨[], .empty, .empty, placeholder ++ body⟩) : Except String (BuilderState × BuildState))) :
    (do let (count, file) ← (modelSink.writeTable action).run {rows}
        pure (count, file.left ++ file.right)) =
      (do let (last, body) ← runPushes {} rows
          pure (last.count, last.header ++ body)) := by
  simp only [Sink.writeTable, Bind.bind, StateT.bind, StateT.run, modelSink, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, Pure.pure, StateT.pure, Except.bind, Except.pure, ByteArray.empty_append] at ⊢
  dsimp only [StateT.run] at loop
  rw [loop]
  cases h : runPushes {} rows with
  | error e => rfl
  | ok out =>
    obtain ⟨last, bytes⟩ := out
    have tailBytes : (placeholder ++ bytes).extract last.header.size (placeholder ++ bytes).size = bytes := by
      apply ByteArray.extract_append_eq_right
      · rw [BuilderState.header, encodeHeader_size]; rfl
      · simp
    have unbuffered : ByteArray.empty.isEmpty = true := rfl
    have noTail (i : Nat) : ByteArray.empty.extract i ByteArray.empty.size = ByteArray.empty :=
      ByteArray.extract_eq_empty_iff.mpr (by simp)
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, unbuffered, ↓reduceIte,
      ByteArray.empty_append, noTail, ByteArray.append_empty, tailBytes]

private theorem modelBuild_pushes (rows : List Entry) :
    modelBuild rows = (do
      let (last, body) ← runPushes {} rows
      pure (last.count, last.header ++ body)) :=
  finish_modelBuild rows _ (streamRows_eq rows {} maxRows (by simp) placeholder)

/-- On the fresh, buffered model file, the actual build schedule succeeds
    exactly for ordered inputs within the format limit. Its returned count
    and its flushed bytes are determined by the supplied sequence. -/
theorem modelBuild_ok_iff {rows : List Entry} {count : Nat} {bytes : ByteArray} :
    modelBuild rows = .ok (count, bytes) ↔
    rows.length ≤ maxRows ∧ rows.Pairwise (fun a b => a.key < b.key) ∧
    count = rows.length ∧ bytes = encodeImage rows := by
  rw [modelBuild_pushes]
  constructor
  · intro got
    cases h : runPushes {} rows with
    | error => rw [h] at got; contradiction
    | ok out =>
      obtain ⟨last, body⟩ := out
      rw [h] at got
      cases got
      obtain ⟨fits, sorted, image⟩ := builder_accepts_only_ordered h
      obtain ⟨_, out, count, _⟩ := builder_constructs_image rows fits sorted
      rw [h] at out
      cases out
      exact ⟨fits, sorted, count, image⟩
  · rintro ⟨fits, sorted, rfl, rfl⟩
    obtain ⟨last, h, count, image⟩ := builder_constructs_image rows fits sorted
    rw [h]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, count, image]

end ImmutableSSTable
