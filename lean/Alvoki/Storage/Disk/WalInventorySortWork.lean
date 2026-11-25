module
import all Init.Data.List.Sort.Impl
import Init.Data.Nat.Lemmas

namespace Alvoki.Storage

open List.MergeSort.Internal

private noncomputable def mergeWithWork (le : α → α → Bool) : List α → List α → List α → List α × Nat
  | [], right, acc => (acc.reverseAux right, 0)
  | left, [], acc => (acc.reverseAux left, 0)
  | x :: xs, y :: ys, acc =>
    let (sorted, work) := if le x y then mergeWithWork le xs (y :: ys) (x :: acc)
      else mergeWithWork le (x :: xs) ys (y :: acc)
    (sorted, work + 1)

private theorem mergeWithWork_spec (le : α → α → Bool) (left right acc : List α) :
    let result := mergeWithWork le left right acc
    result.1 = mergeTR.go le left right acc ∧ result.1.length = left.length + right.length + acc.length ∧
      result.2 ≤ left.length + right.length := by
  dsimp only
  induction left generalizing right acc with
  | nil => simp [mergeWithWork, mergeTR.go, List.reverseAux_eq, Nat.add_comm]
  | cons x xs ihLeft =>
    induction right generalizing acc with
    | nil => simp [mergeWithWork, mergeTR.go, List.reverseAux_eq, Nat.add_comm]
    | cons y ys ihRight =>
      by_cases compared : le x y = true
      · obtain ⟨same, length, calls⟩ := ihLeft (y :: ys) (x :: acc)
        simp [mergeWithWork, mergeTR.go, compared]
        exact ⟨same, by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using length,
          by simp only [List.length_cons] at calls ⊢; omega⟩
      · obtain ⟨same, length, calls⟩ := ihRight (y :: acc)
        simp [mergeWithWork, mergeTR.go, compared]
        exact ⟨same, by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using length,
          by simp only [List.length_cons] at calls ⊢; omega⟩

private noncomputable def mergeSortBranches (le : α → α → Bool) (left right : List α × Nat) : List α × Nat :=
  let (sorted, merges) := mergeWithWork le left.1 right.1 []
  (sorted, left.2 + right.2 + merges)

-- Both orientations use the same splits and branch order as Lean 4.36's
-- compiled merge sort. The reversed orientation preserves stable tie order.
private noncomputable def sortWithWork (le : α → α → Bool) (reversed : Bool) {n : Nat}
    (input : { names : List α // names.length = n }) : List α × Nat :=
  match n with
  | 0 | 1 => (input.1, 0)
  | n + 2 =>
    if reversed then
      let (left, right) := splitRevInTwo' input
      mergeSortBranches le (sortWithWork le true right) (sortWithWork le false left)
    else
      let (left, right) := splitRevInTwo input
      mergeSortBranches le (sortWithWork le true left) (sortWithWork le false right)
termination_by n
decreasing_by all_goals omega

private theorem mergeSortBranches_spec (le : α → α → Bool) (left right : List α × Nat)
    {n₁ n₂ : Nat} (leftLength : left.1.length = n₁) (rightLength : right.1.length = n₂)
    (leftBound : ∀ levels, n₁ ≤ 2 ^ levels → left.2 ≤ n₁ * levels)
    (rightBound : ∀ levels, n₂ ≤ 2 ^ levels → right.2 ≤ n₂ * levels)
    (balanced : ∀ levels, n₁ + n₂ ≤ 2 ^ (levels + 1) → n₁ ≤ 2 ^ levels ∧ n₂ ≤ 2 ^ levels)
    (split : 2 ≤ n₁ + n₂) :
    let result := mergeSortBranches le left right
    result.1 = mergeTR left.1 right.1 le ∧ result.1.length = n₁ + n₂ ∧
      ∀ levels, n₁ + n₂ ≤ 2 ^ levels → result.2 ≤ (n₁ + n₂) * levels := by
  obtain ⟨same, length, merges⟩ := mergeWithWork_spec le left.1 right.1 []
  dsimp only [mergeSortBranches]
  refine ⟨same, by simpa [leftLength, rightLength] using length, ?_⟩
  intro levels capacity
  cases levels with
  | zero => simp at capacity; omega
  | succ levels =>
    obtain ⟨fitsLeft, fitsRight⟩ := balanced levels capacity
    have mergeBound : (mergeWithWork le left.1 right.1 []).2 ≤ n₁ + n₂ := by simpa [leftLength, rightLength] using merges
    rw [Nat.mul_succ, Nat.add_mul]
    exact Nat.add_le_add (Nat.add_le_add (leftBound levels fitsLeft) (rightBound levels fitsRight)) mergeBound

private theorem halfFits (n levels : Nat) (capacity : n ≤ 2 ^ (levels + 1)) :
    (n + 1) / 2 ≤ 2 ^ levels ∧ n / 2 ≤ 2 ^ levels := by
  rw [Nat.pow_succ] at capacity
  omega

private theorem sortWithWork_spec (le : α → α → Bool) (reversed : Bool) {n : Nat}
    (input : { names : List α // names.length = n }) :
    let result := sortWithWork le reversed input
    result.1 = (if reversed then mergeSortTR₂.run' le input else mergeSortTR₂.run le input) ∧
      result.1.length = n ∧ ∀ levels, n ≤ 2 ^ levels → result.2 ≤ n * levels := by
  match n, input with
  | 0, ⟨[], _⟩ => cases reversed <;> simp [sortWithWork, mergeSortTR₂.run, mergeSortTR₂.run']
  | 1, ⟨[name], _⟩ => cases reversed <;> simp [sortWithWork, mergeSortTR₂.run, mergeSortTR₂.run']
  | n + 2, input =>
    cases reversed with
    | false =>
      let left := (splitRevInTwo input).1
      let right := (splitRevInTwo input).2
      have leftResult := sortWithWork_spec le true left
      have rightResult := sortWithWork_spec le false right
      have halves : (n + 2 + 1) / 2 + (n + 2) / 2 = n + 2 := by omega
      have bounded := mergeSortBranches_spec le _ _ leftResult.2.1 rightResult.2.1 leftResult.2.2 rightResult.2.2
        (fun levels capacity => halfFits (n + 2) levels (halves ▸ capacity)) (by rw [halves]; omega)
      dsimp only at bounded
      rw [halves] at bounded
      simpa [sortWithWork, mergeSortTR₂.run, leftResult.1, rightResult.1] using bounded
    | true =>
      let left := (splitRevInTwo' input).1
      let right := (splitRevInTwo' input).2
      have leftResult := sortWithWork_spec le false left
      have rightResult := sortWithWork_spec le true right
      have halves : (n + 2 + 1) / 2 + (n + 2) / 2 = n + 2 := by omega
      have bounded := mergeSortBranches_spec le _ _ rightResult.2.1 leftResult.2.1 rightResult.2.2 leftResult.2.2
        (fun levels capacity => halfFits (n + 2) levels (halves ▸ capacity)) (by rw [halves]; omega)
      dsimp only at bounded
      rw [halves] at bounded
      simpa [sortWithWork, mergeSortTR₂.run', leftResult.1, rightResult.1] using bounded
termination_by n
decreasing_by all_goals omega

/-- Interpret the pinned runtime's stable merge sort with a count of its
reached comparator calls. Splitting, list allocation and comparator internals
have separate costs. -/
public noncomputable def mergeSortWithComparisonWork (le : α → α → Bool) (names : List α) : List α × Nat :=
  sortWithWork le false ⟨names, rfl⟩

/-- At most one comparison per input entry per merge level. Any power of
two covering the input length supplies a bound on the number of levels. -/
public theorem mergeSortWithComparisonWork_spec (le : α → α → Bool) (names : List α) :
    let result := mergeSortWithComparisonWork le names
    result.1 = names.mergeSort le ∧ result.1.length = names.length ∧
      ∀ levels, names.length ≤ 2 ^ levels → result.2 ≤ names.length * levels := by
  obtain ⟨same, length, limit⟩ := sortWithWork_spec le false ⟨names, rfl⟩
  refine ⟨?_, length, limit⟩
  simpa [mergeSortWithComparisonWork, mergeSort_eq_mergeSortTR₂, mergeSortTR₂] using same

end Alvoki.Storage
