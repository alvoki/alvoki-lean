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

end ImmutableSSTable
