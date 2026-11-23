import OptProofs

namespace Alvoki.Opt

/-- Decode by natural-number offsets in the accepted layout. -/
def View.logicalRecord (view : View) (i : Nat) : Record :=
  (word view.bytes (16 + i * view.stride.toNat),
    word view.bytes (view.values.toNat + i * view.stride.toNat))

private theorem wordAt_eq (view : View) (base i : USize)
    (extent : base.toNat + i.toNat * view.stride.toNat + 7 < view.bytes.size) :
    wordMachine view.bytes (base + i * view.stride) =
      word view.bytes (base.toNat + i.toNat * view.stride.toNat) := by
  have fits := view.fits
  have mul : i.toNat * view.stride.toNat < USize.size := by omega
  have add : base.toNat + i.toNat * view.stride.toNat < USize.size := by omega
  have offset : (base + i * view.stride).toNat = base.toNat + i.toNat * view.stride.toNat := by
    rw [USize.toNat_add, USize.toNat_mul, Nat.mod_eq_of_lt mul, Nat.mod_eq_of_lt add]
  rw [wordMachine_eq _ _ fits (by rwa [offset]), offset]

theorem View.key_eq (view : View) {i : USize} (valid : i < view.count) :
    view.keyUnchecked i = (view.logicalRecord i.toNat).1 := by
  have base : (16 : USize).toNat = 16 := USize.toNat_ofNat_of_lt_32 (by decide)
  have index := USize.lt_iff_toNat_lt.mp valid
  have size := view.size_eq
  have extent : (16 : USize).toNat + i.toNat * view.stride.toNat + 7 < view.bytes.size := by
    rcases view.layout with ⟨stride, _⟩ | ⟨stride, _⟩
    all_goals rw [base, stride]; omega
  unfold View.keyUnchecked View.logicalRecord
  simpa only [base] using wordAt_eq view 16 i extent

theorem View.value_eq (view : View) {i : USize} (valid : i < view.count) :
    view.valueUnchecked i = (view.logicalRecord i.toNat).2 := by
  have index := USize.lt_iff_toNat_lt.mp valid
  have size := view.size_eq
  have extent : view.values.toNat + i.toNat * view.stride.toNat + 7 < view.bytes.size := by
    rcases view.layout with ⟨stride, values⟩ | ⟨stride, values⟩
    all_goals rw [stride, values]; omega
  exact wordAt_eq view view.values i extent

theorem View.record?_eq (view : View) (i : USize) :
    view.record? i = if i.toNat < view.count.toNat then some (view.logicalRecord i.toNat) else none := by
  by_cases valid : i < view.count
  · have bound := USize.lt_iff_toNat_lt.mp valid
    simp [View.record?, valid, bound, View.key_eq view valid, View.value_eq view valid]
  · have bound : ¬i.toNat < view.count.toNat := fun lt => valid (USize.lt_iff_toNat_lt.mpr lt)
    simp [View.record?, valid, bound]

theorem parseView_ordered {bytes : ByteArray} {view : View} (accepted : parseView bytes = .ok view) :
    ∀ i j, i < j → j < view.count.toNat →
      (view.logicalRecord i).1 < (view.logicalRecord j).1 := by
  intro i j order bound
  have limit := view.count.toNat_lt_size
  have ie : i.toUSize.toNat = i := USize.toNat_ofNat_of_lt (by omega)
  have je : j.toUSize.toNat = j := USize.toNat_ofNat_of_lt (by omega)
  have ij : i.toUSize < j.toUSize := USize.lt_iff_toNat_lt.mpr (by rwa [ie, je])
  have jc : j.toUSize < view.count := USize.lt_iff_toNat_lt.mpr (by rwa [je])
  have ic : i.toUSize < view.count := USize.lt_trans ij jc
  simpa only [view.key_eq ic, view.key_eq jc, ie, je] using
    view.validate_ordered (parseView_spec accepted).2.2.1 ij jc

theorem parseView_lowerBound {bytes : ByteArray} {view : View} (accepted : parseView bytes = .ok view)
    (target : UInt64) :
    Partition (fun i => decide ((view.logicalRecord i).1 < target)) view.count.toNat
      (view.lowerBound target).toNat := by
  have parsed := (parseView_spec accepted).2.2.1
  have monotone (i j : Nat) (le : i ≤ j) (bound : j < view.count.toNat) :
      view.keyUnchecked i.toUSize ≤ view.keyUnchecked j.toUSize := by
    have limit := view.count.toNat_lt_size
    by_cases same : i = j
    · simp [same]
    · have exact_i : i.toUSize.toNat = i := USize.toNat_ofNat_of_lt (by omega)
      have exact_j : j.toUSize.toNat = j := USize.toNat_ofNat_of_lt (by omega)
      have ij : i.toUSize < j.toUSize := USize.lt_iff_toNat_lt.mpr (by rw [exact_i, exact_j]; omega)
      have jc : j.toUSize < view.count := USize.lt_iff_toNat_lt.mpr (by rwa [exact_j])
      exact UInt64.le_of_lt (view.validate_ordered parsed ij jc)
  have partition := searchMachine_partition view.keyUnchecked target view.count monotone
  have key_eq (i : Nat) (bound : i < view.count.toNat) :
      view.keyUnchecked i.toUSize = (view.logicalRecord i).1 := by
    have ie : i.toUSize.toNat = i := USize.toNat_ofNat_of_lt (Nat.lt_trans bound view.count.toNat_lt_size)
    have ic : i.toUSize < view.count := USize.lt_iff_toNat_lt.mpr (by rwa [ie])
    simpa only [ie] using view.key_eq ic
  refine ⟨partition.1, ?_, ?_⟩
  · intro i before
    change decide ((view.logicalRecord i).1 < target) = true
    rw [← key_eq i (Nat.lt_of_lt_of_le before partition.1)]
    exact partition.2.1 i before
  · intro i after bound
    change decide ((view.logicalRecord i).1 < target) = false
    rw [← key_eq i bound]
    exact partition.2.2 i after bound

#print axioms Alvoki.Opt.parseView_spec
#print axioms Alvoki.Opt.View.record?_eq
#print axioms Alvoki.Opt.parseView_ordered
#print axioms Alvoki.Opt.parseView_lowerBound

end Alvoki.Opt
