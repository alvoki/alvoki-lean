import MergeModel

namespace Alvoki.Packed
open Alvoki.Opt

structure Run where
  private mk ::
  view : View
  ordered : view.validate = true
  interleaved : view.stride.toNat = 16 ∧ view.values.toNat = 24

def parseRun (bytes : ByteArray) : Except String Run :=
  if header : bytes.size < 16 || word bytes 8 != 1 then .error "expected version 1"
  else
    match parsed : parseView bytes with
    | .error message => .error message
    | .ok view =>
      have version := (show 16 ≤ bytes.size ∧ word bytes 8 = 1 by simpa using header).2
      have spec := (parseView_spec parsed).2.2
      have layout : view.stride.toNat = 16 ∧ view.values.toNat = 24 := by
        rcases spec.2 with left | right
        · exact left.2
        · simp [version] at right
      .ok ⟨view, spec.1, layout⟩

theorem parseRun_spec {bytes : ByteArray} {run : Run} (accepted : parseRun bytes = .ok run) :
    parseView bytes = .ok run.view ∧ word bytes 8 = 1 := by
  unfold parseRun at accepted
  split at accepted
  · contradiction
  · rename_i header
    have version := (show 16 ≤ bytes.size ∧ word bytes 8 = 1 by simpa using header).2
    split at accepted
    · contradiction
    · cases accepted
      exact ⟨by assumption, version⟩

theorem parseRun_of_view {bytes : ByteArray} {view : View}
    (parsed : parseView bytes = .ok view) (version : word bytes 8 = 1) :
    ∃ run, parseRun bytes = .ok run ∧ run.view = view := by
  have spec := parseView_spec parsed
  have size := view.size_eq
  rw [spec.1] at size
  have good : ¬(bytes.size < 16 || word bytes 8 != 1) = true := by
    have enough : ¬bytes.size < 16 := by omega
    simp [enough, version]
  unfold parseRun
  rw [dite_eq_right good]
  split
  · rename_i h
    rw [parsed] at h
    contradiction
  · refine ⟨_, rfl, ?_⟩
    exact Except.ok.inj ((by assumption : parseView bytes = Except.ok _).symm.trans parsed)

@[inline] def Run.count (run : @& Run) : USize := run.view.count

/-- Check the natural-number index before converting it to a machine offset. -/
@[inline] def Run.record? (run : @& Run) (i : Nat) : Option Record :=
  if i < run.count.toNat then run.view.record? i.toUSize else none

theorem Run.record?_eq (run : Run) (i : Nat) :
    run.record? i = if i < run.count.toNat then some (run.view.logicalRecord i) else none := by
  unfold Run.record?
  split
  next bound =>
    have index : i.toUSize.toNat = i :=
      USize.toNat_ofNat_of_lt (Nat.lt_trans bound run.count.toNat_lt_size)
    rw [View.record?_eq, index]
    exact ite_eq_left bound
  next => rfl

@[inline] def Run.lookup (run : @& Run) (key : UInt64) : Option UInt64 := run.view.lookup key

/-- Checksum over the logical records in the half-open key range. -/
@[inline] def Run.rangeChecksum (run : @& Run) (start stop : UInt64) : UInt64 :=
  run.view.scan (run.view.lowerBound start) (run.view.lowerBound stop)

private def mergeFrom (left right : @& View) (i j : USize)
    (out : ByteArray) : ByteArray :=
  if hi : i < left.count then
    if hj : j < right.count then
      let a := left.keyOrZero i
      let b := right.keyOrZero j
      if a < b then
        mergeFrom left right (i + 1) j
          (left.bytes.copySlice (16 + i.toNat * 16) out out.size 16 false)
      else if a == b then
        mergeFrom left right (i + 1) (j + 1)
          (right.bytes.copySlice (16 + j.toNat * 16) out out.size 16 false)
      else
        mergeFrom left right i (j + 1)
          (right.bytes.copySlice (16 + j.toNat * 16) out out.size 16 false)
    else left.bytes.copySlice (16 + i.toNat * 16) out out.size
      ((left.count.toNat - i.toNat) * 16) false
  else right.bytes.copySlice (16 + j.toNat * 16) out out.size
    ((right.count.toNat - j.toNat) * 16) false
termination_by (left.count.toNat - i.toNat) + (right.count.toNat - j.toNat)
decreasing_by
  all_goals
    try have leftOrder := USize.lt_iff_toNat_lt.mp hi
    try have leftStep := addOne i left.count leftOrder
    try have rightOrder := USize.lt_iff_toNat_lt.mp hj
    try have rightStep := addOne j right.count rightOrder
    omega

private def initialBuffer (left right : @& View) : ByteArray :=
  let capacity := 16 + (left.count.toNat + right.count.toNat) * 16
  pushWordFast (pushWordFast (ByteArray.emptyWithCapacity capacity) 0) 1

def patchCount (merged : ByteArray) : ByteArray :=
  let header := pushWordFast (ByteArray.emptyWithCapacity 8) ((merged.size - 16) / 16).toUInt64
  header.copySlice 0 merged 0 8

private def appendPayload (source : @& View) (out : ByteArray) : ByteArray :=
  source.bytes.copySlice 16 out out.size (source.count.toNat * 16) false

/-- Merge two validated version-1 runs. The right input supplies the value on collision. -/
def merge (a b : @& Run) : ByteArray :=
  let left := a.view
  let right := b.view
  patchCount (mergeFrom left right 0 0 (initialBuffer left right))

open MergeModel

private theorem mergeFrom_refines (left right : View) (i j : USize) (out : ByteArray) :
    mergeFrom left right i j out =
      out ++ MergeModel.bytesOf (MergeModel.union (MergeModel.rowsFrom left i) (MergeModel.rowsFrom right j)) := by
  rw [mergeFrom]
  by_cases hi : i < left.count
  · by_cases hj : j < right.count
    · simp only [hi, hj, dite_true]
      rw [rowsFrom_cons left i hi, rowsFrom_cons right j hj, union]
      simp only [rowAt, ← left.key_eq hi, ← right.key_eq hj]
      by_cases smaller : left.keyOrZero i < right.keyOrZero j
      · rw [ite_eq_left smaller, ite_eq_left smaller, mergeFrom_refines, copyTail, ByteArray.append_assoc,
          rowsFrom_cons right j hj]
        rfl
      · rw [ite_eq_right smaller, ite_eq_right smaller]
        by_cases equal : (left.keyOrZero i == right.keyOrZero j) = true
        · rw [ite_eq_left equal, ite_eq_left equal, mergeFrom_refines, copyTail, ByteArray.append_assoc]
          rfl
        · rw [ite_eq_right equal, ite_eq_right equal, mergeFrom_refines, copyTail, ByteArray.append_assoc,
            rowsFrom_cons left i hi]
          rfl
    · simp only [hi, hj, dite_true, dite_false]
      rw [rowsFrom_cons left i hi, rowsFrom_nil right j hj, union, ← rowsFrom_cons left i hi]
      exact copyRows left i out
      all_goals simp
  · simp only [hi, dite_false]
    rw [rowsFrom_nil left i hi, union]
    exact copyRows right j out
termination_by (left.count.toNat - i.toNat) + (right.count.toNat - j.toNat)
decreasing_by
  all_goals
    have li : i.toNat < left.count.toNat := USize.lt_iff_toNat_lt.mp (by assumption)
    have rj : j.toNat < right.count.toNat := USize.lt_iff_toNat_lt.mp (by assumption)
    have ls := addOne i left.count li
    have rs := addOne j right.count rj
    omega

/-- The logical right-biased union of the two parsed record sequences. -/
def mergedRows (a b : Run) : List MergeModel.Row :=
  MergeModel.union (MergeModel.rowsFrom a.view 0) (MergeModel.rowsFrom b.view 0)

theorem patchCountRows (cap : Nat) (rows : List MergeModel.Row) :
    patchCount (pushWordFast (pushWordFast (ByteArray.emptyWithCapacity cap) 0) 1 ++
      MergeModel.bytesOf rows) =
    pushWordFast (ByteArray.emptyWithCapacity 8) rows.length.toUInt64 ++
      pushWordFast ByteArray.empty 1 ++ MergeModel.bytesOf rows := by
  let placeholder := pushWordFast ByteArray.empty 0
  let version := pushWordFast ByteArray.empty 1
  let payload := MergeModel.bytesOf rows
  have header : pushWordFast (pushWordFast (ByteArray.emptyWithCapacity cap) 0) 1 = placeholder ++ version := rfl
  have placeholder_size : placeholder.size = 8 := rfl
  have version_size : version.size = 8 := rfl
  rw [header, ByteArray.append_assoc]
  change patchCount (placeholder ++ (version ++ payload)) = _
  unfold patchCount
  rw [ByteArray.size_append, placeholder_size, ByteArray.size_append, version_size]
  have length : (8 + (8 + payload.size) - 16) / 16 = (rows).length := by
    rw [show payload.size = 16 * (rows).length from MergeModel.bytesOf_size _]
    omega
  rw [length, ByteArray.copySlice_eq_append]
  let count := pushWordFast (ByteArray.emptyWithCapacity 8) (rows).length.toUInt64
  have count_size : count.size = 8 := rfl
  change (placeholder ++ (version ++ payload)).extract 0 0 ++ count.extract 0 8 ++ _ =
    count ++ version ++ payload
  rw [show (placeholder ++ (version ++ payload)).extract 0 0 = ByteArray.empty by simp,
      ByteArray.empty_append, show count.extract 0 8 = count by
        rw [← count_size, ByteArray.extract_zero_size]]
  change count ++ (placeholder ++ (version ++ payload)).extract (0 + min 8 (count.size - 0))
    (placeholder ++ (version ++ payload)).size = count ++ version ++ payload
  simp only [count_size, Nat.sub_zero, Nat.min_self, Nat.zero_add]
  rw [ByteArray.extract_append_eq_right (a := placeholder) (b := version ++ payload)
    placeholder_size.symm ByteArray.size_append, ByteArray.append_assoc]

/-- The stock per-record merge serializes exactly the right-biased union. -/
theorem merge_refines (a b : Run) :
    merge a b = pushWordFast (ByteArray.emptyWithCapacity 8) (mergedRows a b).length.toUInt64 ++
      pushWordFast ByteArray.empty 1 ++ MergeModel.bytesOf (mergedRows a b) := by
  unfold merge
  dsimp only
  rw [mergeFrom_refines]
  exact patchCountRows _ (mergedRows a b)

/-- Use contiguous copies when the two key ranges are disjoint. -/
def mergeDisjointFast (a b : @& Run) : ByteArray :=
  let left := a.view
  let right := b.view
  if left.count == 0 then right.bytes
  else if right.count == 0 then left.bytes
  else if left.keyOrZero (left.count - 1) < right.keyOrZero 0 then
    patchCount (appendPayload right (appendPayload left (initialBuffer left right)))
  else if right.keyOrZero (right.count - 1) < left.keyOrZero 0 then
    patchCount (appendPayload left (appendPayload right (initialBuffer left right)))
  else merge a b

private def scanFrom (left right : @& View) (i j : USize) (sum : UInt64) : UInt64 :=
  if hi : i < left.count then
    if hj : j < right.count then
      let a := left.keyOrZero i
      let b := right.keyOrZero j
      if a < b then
        scanFrom left right (i + 1) j (sum + (a ^^^ left.valueOrZero i))
      else if a == b then
        scanFrom left right (i + 1) (j + 1) (sum + (b ^^^ right.valueOrZero j))
      else
        scanFrom left right i (j + 1) (sum + (b ^^^ right.valueOrZero j))
    else sum + left.scan i left.count
  else sum + right.scan j right.count
termination_by (left.count.toNat - i.toNat) + (right.count.toNat - j.toNat)
decreasing_by
  all_goals
    have li := USize.lt_iff_toNat_lt.mp hi
    have rj := USize.lt_iff_toNat_lt.mp hj
    have ls := addOne i left.count li
    have rs := addOne j right.count rj
    omega

/-- Consume the right-biased union into a wrapping XOR-and-sum checksum. -/
def scanMerged (a b : @& Run) : UInt64 :=
  scanFrom a.view b.view 0 0 0

private theorem scanFrom_refines (left right : View) (i j : USize) (sum : UInt64) :
    scanFrom left right i j sum =
      (MergeModel.union (MergeModel.rowsFrom left i) (MergeModel.rowsFrom right j)).foldl
        MergeModel.consume sum := by
  rw [scanFrom]
  by_cases hi : i < left.count
  · by_cases hj : j < right.count
    · simp only [hi, hj, dite_true]
      rw [rowsFrom_cons left i hi, rowsFrom_cons right j hj, union]
      simp only [rowAt, ← left.key_eq hi, ← right.key_eq hj]
      by_cases smaller : left.keyOrZero i < right.keyOrZero j
      · rw [ite_eq_left smaller, ite_eq_left smaller, scanFrom_refines, rowsFrom_cons right j hj]
        simp only [List.foldl_cons, consume, rowAt, ← left.key_eq hi, ← left.value_eq hi]
      · rw [ite_eq_right smaller, ite_eq_right smaller]
        by_cases equal : (left.keyOrZero i == right.keyOrZero j) = true
        · rw [ite_eq_left equal, ite_eq_left equal, scanFrom_refines]
          simp only [List.foldl_cons, consume, ← right.key_eq hj, ← right.value_eq hj]
        · rw [ite_eq_right equal, ite_eq_right equal, scanFrom_refines, rowsFrom_cons left i hi]
          simp only [List.foldl_cons, consume, rowAt, ← right.key_eq hj, ← right.value_eq hj]
    · simp only [hi, hj, dite_true, dite_false]
      rw [rowsFrom_cons left i hi, rowsFrom_nil right j hj, union, ← rowsFrom_cons left i hi]
      exact scanTail left i sum
      all_goals simp
  · simp only [hi, dite_false]
    rw [rowsFrom_nil left i hi, union]
    exact scanTail right j sum
termination_by (left.count.toNat - i.toNat) + (right.count.toNat - j.toNat)
decreasing_by
  all_goals
    have li : i.toNat < left.count.toNat := USize.lt_iff_toNat_lt.mp (by assumption)
    have rj : j.toNat < right.count.toNat := USize.lt_iff_toNat_lt.mp (by assumption)
    have ls := addOne i left.count li
    have rs := addOne j right.count rj
    omega

/-- The direct scan folds over the same logical union as the stock per-record merge. -/
theorem scanMerged_refines (a b : Run) :
    scanMerged a b = (mergedRows a b).foldl MergeModel.consume 0 :=
  scanFrom_refines a.view b.view 0 0 0

end Alvoki.Packed
