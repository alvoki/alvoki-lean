import Alvoki.Codec.PackedRun

namespace Alvoki.Packed
open Alvoki.Opt Alvoki.ScopedBytes MergeModel

private structure Span (view : View) (start : USize) (rival : UInt64) where
  stop : USize
  advances : start.toNat < stop.toNat
  within : stop.toNat ≤ view.count.toNat
  wins : ∀ k : USize, start.toNat ≤ k.toNat → k.toNat < stop.toNat → view.keyOrZero k < rival

private theorem addExact' (a b : USize) (fits : a.toNat + b.toNat < USize.size) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [USize.toNat_add, Nat.mod_eq_of_lt fits]

private theorem View.key_mono (view : View) (sorted : view.validate = true)
    {i j : USize} (order : i.toNat ≤ j.toNat) (bound : j.toNat < view.count.toNat) :
    view.keyOrZero i ≤ view.keyOrZero j := by
  by_cases same : i = j
  · simp [same]
  · have different : i.toNat ≠ j.toNat := fun h => same (USize.toNat.inj h)
    exact UInt64.le_of_lt (view.validate_ordered sorted
      (USize.lt_iff_toNat_lt.mpr (by omega)) (USize.lt_iff_toNat_lt.mpr bound))

private theorem search_prefix (view : View) (sorted : view.validate = true) (rival : UInt64)
    (lo hi : USize) (order : lo.toNat ≤ hi.toNat) (bound : hi.toNat ≤ view.count.toNat)
    (smaller : ∀ k : USize, k.toNat < lo.toNat → view.keyOrZero k < rival) :
    let stop := searchMachineLoop view.keyOrZero rival lo hi
    lo.toNat ≤ stop.toNat ∧ stop.toNat ≤ hi.toNat ∧
      ∀ k : USize, k.toNat < stop.toNat → view.keyOrZero k < rival := by
  dsimp only
  have limit := view.count.toNat_lt_size
  have exactNat (k : Nat) (h : k < view.count.toNat) : k.toUSize.toNat = k :=
    USize.toNat_ofNat_of_lt (by omega)
  let cmp := fun k : Nat => decide (view.keyOrZero k.toUSize < rival)
  have p := lowerBound_partition cmp hi.toNat lo.toNat hi.toNat (by
    intro i j le hit yes
    have h := View.key_mono view sorted (i := i.toUSize) (j := j.toUSize)
      (by rw [exactNat i (by omega), exactNat j (by omega)]; exact le)
      (by rw [exactNat j (by omega)]; omega)
    exact decide_eq_true (UInt64.lt_of_le_of_lt h (of_decide_eq_true yes)))
    ⟨order, Nat.le_refl _⟩ (by
      intro i before
      exact decide_eq_true (smaller i.toUSize (by rw [exactNat i (by omega)]; exact before)))
    (by omega)
  have searchEq := searchMachineLoop_eq view.keyOrZero rival lo hi
  change (searchMachineLoop view.keyOrZero rival lo hi).toNat = lowerBound cmp lo.toNat hi.toNat at searchEq
  rw [searchEq]
  refine ⟨?_, p.1, ?_⟩
  · apply Nat.le_of_not_gt
    intro h
    have miss := p.2.2 (lowerBound cmp lo.toNat hi.toNat) (Nat.le_refl _) (by omega)
    have yes := smaller (lowerBound cmp lo.toNat hi.toNat).toUSize
      (by rw [exactNat _ (by omega)]; omega)
    exact Bool.noConfusion (miss.symm.trans (decide_eq_true yes))
  · intro k hit
    have yes := p.2.1 k.toNat hit
    simpa only [cmp, USize.ofNat_toNat, decide_eq_true_eq] using yes

@[inline] private def chooseSpan (view : @& View) (sorted : view.validate = true)
    (i : USize) (rival : UInt64) (within : i < view.count)
    (headWins : view.keyOrZero i < rival) (probe bounded : Bool) : Span view i rival :=
  have ic := USize.lt_iff_toNat_lt.mp within
  have limit := view.count.toNat_lt_size
  if enough : probe && (8 : USize) ≤ view.count - i && view.keyOrZero (i + 7) < rival then
    have rest := USize.toNat_sub_of_le view.count i (USize.le_of_lt within)
    have seven : (7 : USize).toNat = 7 := USize.toNat_ofNat_of_lt_32 (by decide)
    have eight : (8 : USize).toNat = 8 := USize.toNat_ofNat_of_lt_32 (by decide)
    have width : (256 : USize).toNat = 256 := USize.toNat_ofNat_of_lt_32 (by decide)
    have available : i.toNat + 8 ≤ view.count.toNat := by
      have h : (8 : USize) ≤ view.count - i :=
        of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp enough).1).2
      have hn := USize.le_iff_toNat_le.mp h
      rw [eight, rest] at hn
      omega
    have probeIndex : (i + 7).toNat = i.toNat + 7 := by
      rw [addExact' _ _ (by rw [seven]; omega), seven]
    have loIndex : (i + 8).toNat = i.toNat + 8 := by
      rw [addExact' _ _ (by rw [eight]; omega), eight]
    let hi := if bounded && (256 : USize) ≤ view.count - i then i + 256 else view.count
    have window : i.toNat + 8 ≤ hi.toNat ∧ hi.toNat ≤ view.count.toNat := by
      dsimp [hi]
      split
      next h =>
        have fits : (256 : USize) ≤ view.count - i :=
          of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
        have fitn := USize.le_iff_toNat_le.mp fits
        rw [width, rest] at fitn
        rw [addExact' _ _ (by rw [width]; omega), width]
        omega
      next _ => omega
    if all : bounded && view.keyOrZero (hi - 1) < rival then
      have one : (1 : USize).toNat = 1 := USize.toNat_ofNat_of_lt_32 (by decide)
      have last : (hi - 1).toNat = hi.toNat - 1 := by
        rw [USize.toNat_sub_of_le hi 1 (USize.le_iff_toNat_le.mpr (by rw [one]; omega)), one]
      ⟨hi, by omega, window.2, fun k _ before => UInt64.lt_of_le_of_lt
        (View.key_mono view sorted (by omega) (by omega))
        (of_decide_eq_true (Bool.and_eq_true_iff.mp all).2)⟩
    else
      let stop := searchMachineLoop view.keyOrZero rival (i + 8) hi
      have cert := search_prefix view sorted rival (i + 8) hi (by omega) window.2
        (fun k before => UInt64.lt_of_le_of_lt (View.key_mono view sorted (by omega) (by omega))
          (of_decide_eq_true (Bool.and_eq_true_iff.mp enough).2))
      ⟨stop, by dsimp [stop]; have := cert.1; omega, Nat.le_trans cert.2.1 window.2, fun k _ h => cert.2.2 k h⟩
  else
    have step := addOne i view.count ic
    ⟨i + 1, by omega, by omega, by
      intro k lower upper
      have same : k = i := USize.toNat.inj (by omega)
      simpa [same] using headWins⟩

@[inline] private def appendRows (out : Builder) (view : @& View) (i endIndex : USize) : Builder :=
  out.copyToTail view.bytes (16 + i.toNat * 16) ((endIndex.toNat - i.toNat) * 16)

private theorem append_span (out : Builder) (view : View) (i stop : USize)
    (lo : i.toNat ≤ stop.toNat) :
    (appendRows out view i stop).finish =
      out.finish ++ view.bytes.extract (16 + i.toNat * 16) (16 + stop.toNat * 16) := by
  unfold appendRows
  rw [copyToTail_refines, show 16 + i.toNat * 16 + (stop.toNat - i.toNat) * 16 =
    16 + stop.toNat * 16 by omega]

private theorem append_tail (out : Builder) (view : View) (i : USize) :
    (appendRows out view i view.count).finish = out.finish ++ bytesOf (rowsFrom view i) :=
  copyRows view i out.finish

@[inline] private def advanceStreak (bounded : Bool) (streak trigger : UInt8) : UInt8 :=
  if bounded then 1 else (streak + 1) &&& trigger

/-- The cached heads equal their loads for the current cursors. Head values at an
    exhausted input are ignored, so the cache uses the reader's guarded sentinel. -/
private def emitSpans (left right : @& Run) (bounded : Bool) (trigger : UInt8)
    (i j : USize) (a b : UInt64) (ka : a = left.view.keyOrZero i) (kb : b = right.view.keyOrZero j)
    (ls rs : UInt8) (out : Builder) : Builder :=
  if hi : i < left.count then
    if hj : j < right.count then
      if smaller : a < b then
        let span := chooseSpan left.view left.ordered i b hi (ka ▸ smaller)
          (trigger != 0 && ls == trigger) bounded
        have _advance := span.advances
        emitSpans left right bounded trigger span.stop j (left.view.keyOrZero span.stop) b rfl kb
          (advanceStreak bounded ls trigger) 0 (appendRows out left.view i span.stop)
      else if equal : a == b then
        emitSpans left right bounded trigger (i + 1) (j + 1)
          (left.view.keyOrZero (i + 1)) (right.view.keyOrZero (j + 1)) rfl rfl 0 0
          (out.copyToTail right.view.bytes (16 + j.toNat * 16) 16)
      else
        have wins : b < a := UInt64.lt_of_le_of_ne (UInt64.not_lt.mp smaller)
          (fun e => ‹¬(a == b) = true› (beq_iff_eq.mpr e.symm))
        let span := chooseSpan right.view right.ordered j a hj (kb ▸ wins)
          (trigger != 0 && rs == trigger) bounded
        have _advance := span.advances
        emitSpans left right bounded trigger i span.stop a (right.view.keyOrZero span.stop) ka rfl
          0 (advanceStreak bounded rs trigger) (appendRows out right.view j span.stop)
    else appendRows out left.view i left.count
  else appendRows out right.view j right.count
termination_by (left.count.toNat - i.toNat) + (right.count.toNat - j.toNat)
decreasing_by
  all_goals
    have li := USize.lt_iff_toNat_lt.mp hi
    have rj := USize.lt_iff_toNat_lt.mp hj
    try dsimp [span] at _advance
    first
    | omega
    | have sl := addOne i left.count li
      have sr := addOne j right.count rj
      omega

private theorem emitSpans_refines (left right : Run) (bounded : Bool) (trigger : UInt8)
    (i j : USize) (a b : UInt64) (ka : a = left.view.keyOrZero i) (kb : b = right.view.keyOrZero j)
    (ls rs : UInt8) (out : Builder) :
    (emitSpans left right bounded trigger i j a b ka kb ls rs out).finish =
      out.finish ++ bytesOf (union (rowsFrom left.view i) (rowsFrom right.view j)) := by
  subst a
  subst b
  rw [emitSpans]
  by_cases hi : i < left.count
  · by_cases hj : j < right.count
    · simp only [hi, hj, dite_true]
      by_cases smaller : left.view.keyOrZero i < right.view.keyOrZero j
      · simp only [dite_eq_left smaller]
        let span := chooseSpan left.view left.ordered i (right.view.keyOrZero j) hi smaller
          (trigger != 0 && ls == trigger) bounded
        have progress := span.advances
        obtain ⟨prefixRows, splitRows, copyBytes, wins⟩ :=
          rowsSpan left.view i span.stop (by omega) span.within _ span.wins
        rw [emitSpans_refines, append_span _ _ _ span.stop (by omega), ← copyBytes, ByteArray.append_assoc]
        conv => rhs; rw [splitRows, rowsFrom_cons right.view j hj]
        have win (row : Row) (mem : row ∈ prefixRows) : row.record.1 < (rowAt right.view j hj).record.1 := by
          change row.record.1 < (right.view.logicalRecord j.toNat).1
          rw [← right.view.key_eq hj]
          exact wins row mem
        rw [union_prefixLeft _ _ _ _ win, bytesOf_append, ← rowsFrom_cons right.view j hj]
      · simp only [dite_eq_right smaller]
        by_cases equal : (left.view.keyOrZero i == right.view.keyOrZero j) = true
        · simp only [dite_eq_left equal]
          rw [emitSpans_refines, copyToTail_refines, ByteArray.append_assoc]
          conv => rhs; rw [rowsFrom_cons left.view i hi, rowsFrom_cons right.view j hj, union]
          simp only [rowAt, ← left.view.key_eq hi, ← right.view.key_eq hj,
            ite_eq_right smaller, ite_eq_left equal, bytesOf]
        · simp only [dite_eq_right equal]
          have smaller' : right.view.keyOrZero j < left.view.keyOrZero i :=
            UInt64.lt_of_le_of_ne (UInt64.not_lt.mp smaller)
              (fun e => equal (beq_iff_eq.mpr e.symm))
          let span := chooseSpan right.view right.ordered j (left.view.keyOrZero i) hj smaller'
            (trigger != 0 && rs == trigger) bounded
          have progress := span.advances
          obtain ⟨prefixRows, splitRows, copyBytes, wins⟩ :=
            rowsSpan right.view j span.stop (by omega) span.within _ span.wins
          rw [emitSpans_refines, append_span _ _ _ span.stop (by omega), ← copyBytes, ByteArray.append_assoc]
          conv => rhs; rw [splitRows, rowsFrom_cons left.view i hi]
          have win (row : Row) (mem : row ∈ prefixRows) : row.record.1 < (rowAt left.view i hi).record.1 := by
            change row.record.1 < (left.view.logicalRecord i.toNat).1
            rw [← left.view.key_eq hi]
            exact wins row mem
          rw [union_prefixRight _ _ _ _ win, bytesOf_append, ← rowsFrom_cons left.view i hi]
    · simp only [hi, hj, dite_true, dite_false]
      rw [rowsFrom_cons left.view i hi, rowsFrom_nil right.view j hj, union, ← rowsFrom_cons left.view i hi]
      exact append_tail out left.view i
      all_goals simp
  · simp only [hi, dite_false]
    rw [rowsFrom_nil left.view i hi, union]
    exact append_tail out right.view j
termination_by (left.count.toNat - i.toNat) + (right.count.toNat - j.toNat)
decreasing_by
  all_goals
    have li := USize.lt_iff_toNat_lt.mp hi
    have rj := USize.lt_iff_toNat_lt.mp hj
    try dsimp [span] at progress
    first | omega | (have sl := addOne i left.count li; have sr := addOne j right.count rj; omega)

def mergeSpansWith (left right : @& Run) (bounded : Bool) (trigger : UInt8) : ByteArray :=
  let cap := 16 + (left.count.toNat + right.count.toNat) * 16
  let header := pushWordFast (pushWordFast (ByteArray.emptyWithCapacity cap) 0) 1
  patchCount (emitSpans left right bounded trigger 0 0 (left.view.keyOrZero 0)
    (right.view.keyOrZero 0) rfl rfl 0 0 (Builder.ofPrefix header)).finish

theorem mergeSpansWith_eq (left right : Run) (bounded : Bool) (trigger : UInt8) :
    mergeSpansWith left right bounded trigger = merge left right := by
  unfold mergeSpansWith
  dsimp only
  rw [emitSpans_refines, merge_refines]
  simpa only [Builder.ofPrefix, Builder.finish, mergedRows] using
    patchCountRows (16 + (left.count.toNat + right.count.toNat) * 16) (mergedRows left right)

end Alvoki.Packed
