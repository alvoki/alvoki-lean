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

end ImmutableSSTable
