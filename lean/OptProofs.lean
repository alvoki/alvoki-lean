import PackedView
import Proofs

namespace Alvoki.Opt

theorem searchMachineLoop_eq (readKey : USize → UInt64) (target : UInt64)
    (lo hi : USize) :
    (searchMachineLoop readKey target lo hi).toNat =
      Alvoki.lowerBound (fun i => decide (readKey i.toUSize < target)) lo.toNat hi.toNat := by
  rw [searchMachineLoop, Alvoki.lowerBound]
  by_cases positive : lo < hi
  · have natPositive := USize.lt_iff_toNat_lt.mp positive
    simp only [positive, natPositive, dite_true, ite_true]
    let mid := lo + (hi - lo) / 2
    have midpoint : mid.toNat = lo.toNat + (hi.toNat - lo.toNat) / 2 :=
      midpoint_toNat lo hi positive
    have midBefore : mid.toNat < hi.toNat := by omega
    have successor := addOne mid hi midBefore
    rw [← midpoint]
    simp only [USize.ofNat_toNat]
    split
    next smaller =>
      have hm : readKey mid < target := smaller
      simp only [decide_eq_true hm, ite_true]
      rw [← successor]
      exact searchMachineLoop_eq readKey target (mid + 1) hi
    next larger =>
      have hm : ¬readKey mid < target := larger
      simp only [decide_eq_false hm, Bool.false_eq_true, ite_false]
      exact searchMachineLoop_eq readKey target lo mid
  · have natNegative : ¬lo.toNat < hi.toNat := fun h => positive (USize.lt_iff_toNat_lt.mpr h)
    simp [positive, natNegative]
termination_by hi.toNat - lo.toNat
decreasing_by all_goals (dsimp [mid] at midpoint successor midBefore; omega)

/-- The optimized lower bound inherits the partition guarantee for monotone logical keys. -/
theorem searchMachine_partition (key : USize → UInt64) (target : UInt64) (count : USize)
    (sorted : ∀ i j : Nat, i ≤ j → j < count.toNat → key i.toUSize ≤ key j.toUSize) :
    Partition (fun i => decide (key i.toUSize < target)) count.toNat
      (searchMachine key target count).toNat := by
  rw [searchMachine, searchMachineLoop_eq]
  have zero : (0 : USize).toNat = 0 := USize.toNat_ofNat_of_lt_32 (by decide)
  rw [zero]
  exact search_partition (fun i => key i.toUSize) count.toNat target sorted

#print axioms Alvoki.Opt.searchMachine_partition
#print axioms Alvoki.Opt.wordMachine_eq

end Alvoki.Opt
