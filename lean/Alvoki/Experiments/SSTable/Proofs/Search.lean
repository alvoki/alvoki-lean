import Alvoki.Experiments.SSTable.Search
import Alvoki.Kernel.BlockContracts

namespace ImmutableSSTable

theorem seekBetween_eq_lowerBound [Monad m] [LawfulMonad m]
    (read : Nat → m Entry) (rows : Nat → Entry) (n : Nat)
    (reads : ∀ i, i < n → read i = pure (rows i))
    (key : ByteArray) (lo hi : Nat) (within : hi ≤ n) :
    seekBetween read key lo hi = pure (Alvoki.lowerBound (fun i => decide ((rows i).key < key)) lo hi) := by
  rw [seekBetween, Alvoki.lowerBound]
  by_cases h : lo < hi
  · let mid := lo + (hi - lo) / 2
    have index : mid < n := by dsimp [mid]; omega
    simp only [h, ite_true, reads (lo + (hi-lo)/2) index, pure_bind]
    by_cases less : (rows mid).key < key
    · simpa [mid, less] using seekBetween_eq_lowerBound read rows n reads key (mid + 1) hi within
    · simpa [mid, less] using seekBetween_eq_lowerBound read rows n reads key lo mid (by omega)
  · simp [h]
termination_by hi - lo
decreasing_by all_goals omega

theorem seekBetween_correct [Monad m] [LawfulMonad m]
    (read : Nat → m Entry) (rows : Nat → Entry) (n : Nat)
    (reads : ∀ i, i < n → read i = pure (rows i))
    (sorted : ∀ i j, i ≤ j → j < n → (rows i).key ≤ (rows j).key)
    (key : ByteArray) :
    ∃ index, seekBetween read key 0 n = pure index ∧
      LowerBound (fun i => (rows i).key) n key index := by
  refine ⟨_, seekBetween_eq_lowerBound read rows n reads key 0 n (Nat.le_refl _), ?_⟩
  have partition := Alvoki.lowerBound_partition (fun i => decide ((rows i).key < key)) n 0 n
    (fun i j hij hj h => decide_eq_true (Std.lt_of_le_of_lt (sorted i j hij hj) (of_decide_eq_true h)))
    (by omega) (by omega) (by omega)
  obtain ⟨bound, left, right⟩ := partition
  exact ⟨bound, fun i hi => of_decide_eq_true (left i hi),
    fun i hi hn => Std.not_lt.mp (of_decide_eq_false (right i hi hn))⟩

/-- Count the positional row probes of the actual search. A range smaller
than 2^bits uses at most bits probes regardless of the keys returned. -/
theorem seekBetween_probes (rows : Nat → Entry) (key : ByteArray) (bits lo hi start : Nat)
    (small : hi - lo < 2 ^ bits) :
    ((seekBetween (m := StateM Nat) (fun i s => (rows i, s + 1)) key lo hi).run start).2 ≤ start + bits := by
  induction bits generalizing lo hi start with
  | zero =>
    have empty : ¬lo < hi := by simp at small; omega
    rw [seekBetween]; simp [empty, StateT.run, pure, StateT.pure]
  | succ bits ih =>
    rw [seekBetween]
    by_cases h : lo < hi
    · simp only [h, ite_true]
      let mid := lo + (hi - lo) / 2
      change ((if (rows mid).key < key then _ else _ : StateM Nat Nat) (start + 1)).2 ≤ _
      rw [Nat.pow_succ] at small
      split
      · exact Nat.le_trans (ih (mid + 1) hi (start + 1) (by dsimp [mid]; omega)) (by omega)
      · exact Nat.le_trans (ih lo mid (start + 1) (by dsimp [mid]; omega)) (by omega)
    · simp [h, StateT.run, pure, StateT.pure]

end ImmutableSSTable
