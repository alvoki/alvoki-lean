import Alvoki.Experiments.L0.TableRows
import Alvoki.Experiments.L0.CodecProofs
import Alvoki.Experiments.SSTable.Proofs.Builder

namespace ExperimentalL0
open ImmutableSSTable

/-- The builder-side input cursor. The native implementation uses one private
IO reference for the same read and write operations. -/
def rowSupply : StateM Rows (Option Entry) :=
  nextTableRow (fun rows => (rows, rows)) (fun remaining _ => ((), remaining))

/-- Tie a reached read and cursor update to the exact callback result.
The reference's read and write reports are the only primitives. -/
theorem nextTableRow_cons {read : EStateM ε σ Rows}
    {write : Rows → EStateM ε σ Unit}
    (got : read before = .ok (row :: remaining) reached)
    (advanced : write remaining reached = .ok () after) :
    nextTableRow read write before = .ok (some (Entry.encode keyCodec mutationCodec row)) after := by
  simp [nextTableRow, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, got, advanced]

theorem nextTableRow_nil {read : EStateM ε σ Rows}
    {write : Rows → EStateM ε σ Unit}
    (got : read before = .ok [] after) :
    nextTableRow read write before = .ok none after := by
  simp [nextTableRow, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, got]

/-- The actual supplier step, with all encoded rows still to be delivered
at the next cursor. -/
theorem rowSupply_step (rows : Rows) :
    let (out, remaining) := rowSupply.run rows
    rows.map (Entry.encode keyCodec mutationCodec) =
      out.toList ++ remaining.map (Entry.encode keyCodec mutationCodec) ∧
    (out = none → remaining = []) := by
  cases rows
  · exact ⟨rfl, fun _ => rfl⟩
  · exact ⟨rfl, fun absent => nomatch absent⟩

/-- Any sequence of supplier calls, cut off on the first EOF or after the
given budget. The output is a prefix of the actual encoded builder input. -/
def readSupplied : Nat → StateM Rows (List Entry)
  | 0 => pure []
  | n + 1 => do
    match ← rowSupply with
    | none => pure []
    | some row => return row :: (← readSupplied n)

theorem readSupplied_exact (budget : Nat) (rows : Rows) :
    (readSupplied budget).run rows =
      ((rows.map (Entry.encode keyCodec mutationCodec)).take budget, rows.drop budget) := by
  induction budget generalizing rows with
  | zero => rfl
  | succ budget ih =>
    cases rows with
    | nil => rfl
    | cons row remaining =>
      change (let (supplied, tail) := (readSupplied budget).run remaining
        (Entry.encode keyCodec mutationCodec row :: supplied, tail)) = _
      rw [ih]
      rfl

/-- At the builder's full input length the supplier has exactly the input
of the existing SSTable builder theorem, and its next observation is EOF. -/
theorem supplied_builder_input (rows : Rows) :
    let (supplied, remaining) := (readSupplied rows.length).run rows
    rowSupply.run remaining = (none, []) ∧
    modelBuild supplied = modelBuild (rows.map (Entry.encode keyCodec mutationCodec)) := by
  rw [readSupplied_exact]
  have allRows : (rows.map (Entry.encode keyCodec mutationCodec)).take rows.length =
      rows.map (Entry.encode keyCodec mutationCodec) := by
    exact List.take_of_length_le (by simp)
  simp [allRows]
  rfl

end ExperimentalL0
