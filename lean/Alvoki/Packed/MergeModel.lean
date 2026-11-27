import Alvoki.Proofs.Packed.PackedViewProofs
import Alvoki.Kernel.ScopedBytes

namespace Alvoki.Packed.MergeModel
open Alvoki.Opt Alvoki.ScopedBytes

/-- Logical value and original version-1 payload bytes for a single record. -/
structure Row where
  record : Record
  bytes : ByteArray
  width : bytes.size = 16

def rowAt (view : View) (i : USize) (bound : i < view.count) : Row :=
  let offset := 16 + i.toNat * 16
  ⟨view.logicalRecord i.toNat, view.bytes.extract offset (offset + 16), by
    have index := USize.lt_iff_toNat_lt.mp bound
    have size := view.size_eq
    rw [ByteArray.size_extract, Nat.min_eq_left (by omega)]
    omega⟩

def rowsFrom (view : View) (i : USize) : List Row :=
  if bound : i < view.count then rowAt view i bound :: rowsFrom view (i + 1) else []
termination_by view.count.toNat - i.toNat
decreasing_by
  have index := USize.lt_iff_toNat_lt.mp bound
  have step := addOne i view.count index
  omega

theorem rowsFrom_cons (view : View) (i : USize) (bound : i < view.count) :
    rowsFrom view i = rowAt view i bound :: rowsFrom view (i + 1) := by
  rw [rowsFrom, dite_eq_left bound]

theorem rowsFrom_nil (view : View) (i : USize) (exhausted : ¬i < view.count) :
    rowsFrom view i = [] := by
  rw [rowsFrom, dite_eq_right exhausted]

/-- Merge two strictly ordered sequences, preferring the right row on equal keys. -/
def union (left right : List Row) : List Row :=
  match left, right with
  | [], _ => right
  | _, [] => left
  | a :: as, b :: bs =>
    if a.record.1 < b.record.1 then a :: union as (b :: bs)
    else if a.record.1 == b.record.1 then b :: union as bs
    else b :: union (a :: as) bs
termination_by left.length + right.length

theorem union_nil_right (left : List Row) : union left [] = left := by
  cases left <;> rw [union] <;> simp

def bytesOf : List Row → ByteArray
  | [] => ByteArray.empty
  | row :: rest => row.bytes ++ bytesOf rest

theorem bytesOf_size (rows : List Row) : (bytesOf rows).size = 16 * rows.length := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [bytesOf, ByteArray.size_append, row.width, ih, List.length_cons]
    omega

def consume (sum : UInt64) (row : Row) : UInt64 := sum + (row.record.1 ^^^ row.record.2)

private theorem foldl_consume (rows : List Row) (sum : UInt64) :
    rows.foldl consume sum = sum + rows.foldl consume 0 := by
  induction rows generalizing sum with
  | nil => simp
  | cons row rest ih =>
    simp only [List.foldl_cons, consume, UInt64.zero_add]
    rw [ih (sum + (row.record.1 ^^^ row.record.2)), ih (row.record.1 ^^^ row.record.2)]
    exact UInt64.add_assoc ..

theorem scanRows (view : View) (i : USize) (sum : UInt64) :
    view.scanFrom i view.count sum = (rowsFrom view i).foldl consume sum := by
  rw [View.scanFrom, rowsFrom]
  by_cases bound : i < view.count
  · simp only [bound, dite_true, List.foldl_cons, consume, rowAt]
    rw [view.key_eq bound, view.value_eq bound]
    exact scanRows view (i + 1) _
  · simp [bound]
termination_by view.count.toNat - i.toNat
decreasing_by
  have index : i.toNat < view.count.toNat := USize.lt_iff_toNat_lt.mp (by assumption)
  have step := addOne i view.count index
  omega

theorem scanTail (view : View) (i : USize) (sum : UInt64) :
    sum + view.scan i view.count = (rowsFrom view i).foldl consume sum := by
  unfold View.scan
  rw [USize.min_def, ite_eq_left (USize.le_refl _), scanRows, foldl_consume (rowsFrom view i) sum]

theorem copyTail (out src : ByteArray) (offset length : Nat) :
    src.copySlice offset out out.size length false = out ++ src.extract offset (offset + length) :=
  copyToTail_refines (Builder.ofPrefix out) src offset length

private theorem bytesOf_rowsFrom (view : View) (i : USize) :
    bytesOf (rowsFrom view i) = view.bytes.extract (16 + i.toNat * 16) view.bytes.size := by
  rw [rowsFrom]
  by_cases bound : i < view.count
  · simp only [bound, dite_true, bytesOf, rowAt]
    rw [bytesOf_rowsFrom view (i + 1)]
    have index := USize.lt_iff_toNat_lt.mp bound
    have size := view.size_eq
    rw [addOne i view.count index]
    have step : 16 + (i.toNat + 1) * 16 = 16 + i.toNat * 16 + 16 := by omega
    rw [step]
    exact (ByteArray.extract_eq_extract_append_extract _ (by omega) (by omega)).symm
  · simp only [bound, dite_false, bytesOf]
    symm
    rw [ByteArray.extract_eq_empty_iff]
    have size := view.size_eq
    simp only [USize.lt_iff_toNat_lt] at bound
    omega
termination_by view.count.toNat - i.toNat
decreasing_by
  have index : i.toNat < view.count.toNat := USize.lt_iff_toNat_lt.mp (by assumption)
  have step := addOne i view.count index
  omega

theorem copyRows (view : View) (i : USize) (out : ByteArray) :
    view.bytes.copySlice (16 + i.toNat * 16) out out.size ((view.count.toNat - i.toNat) * 16) false =
      out ++ bytesOf (rowsFrom view i) := by
  rw [copyTail, bytesOf_rowsFrom]
  have size := view.size_eq
  by_cases valid : i.toNat ≤ view.count.toNat
  · have stop : 16 + i.toNat * 16 + (view.count.toNat - i.toNat) * 16 = view.bytes.size := by omega
    rw [stop]
  · rw [show view.count.toNat - i.toNat = 0 by omega]
    have empty : view.bytes.extract (16 + i.toNat * 16) view.bytes.size = ByteArray.empty := by
      rw [ByteArray.extract_eq_empty_iff]
      omega
    simp [empty]

/-- Rows in a winning span, with their exact byte extent and the remaining suffix. -/
theorem rowsSpan (view : View) (i stop : USize) (lo : i.toNat ≤ stop.toNat)
    (hi : stop.toNat ≤ view.count.toNat) (rival : UInt64)
    (wins : ∀ k : USize, i.toNat ≤ k.toNat → k.toNat < stop.toNat → view.keyOrZero k < rival) :
    ∃ rows, rowsFrom view i = rows ++ rowsFrom view stop ∧
      bytesOf rows = view.bytes.extract (16 + i.toNat * 16) (16 + stop.toNat * 16) ∧
      ∀ row ∈ rows, row.record.1 < rival := by
  by_cases done : i = stop
  · subst stop
    exact ⟨[], rfl, (ByteArray.extract_eq_empty_iff.mpr (Nat.min_le_left ..)).symm, by simp⟩
  · have ne : i.toNat ≠ stop.toNat := fun e => done (USize.toNat.inj e)
    have hit : i < view.count := USize.lt_iff_toNat_lt.mpr (by omega)
    have step := addOne i view.count (USize.lt_iff_toNat_lt.mp hit)
    obtain ⟨rows, tail, bytes, smaller⟩ := rowsSpan view (i + 1) stop (by omega) hi rival
      (fun k h1 h2 => wins k (by omega) h2)
    refine ⟨rowAt view i hit :: rows, ?_, ?_, ?_⟩
    · rw [rowsFrom_cons view i hit, tail, List.cons_append]
    · rw [bytesOf, bytes]
      simp only [rowAt, step]
      have next : 16 + (i.toNat + 1) * 16 = 16 + i.toNat * 16 + 16 := by omega
      rw [next]
      exact (ByteArray.extract_eq_extract_append_extract _ (by omega) (by omega)).symm
    · intro row mem
      rcases List.mem_cons.mp mem with e | rest
      · subst row
        exact (view.key_eq hit) ▸ wins i (Nat.le_refl _) (by omega)
      · exact smaller row rest
termination_by stop.toNat - i.toNat
decreasing_by omega

theorem union_prefixLeft (prefixRows left : List Row) (b : Row) (right : List Row)
    (wins : ∀ row ∈ prefixRows, row.record.1 < b.record.1) :
    union (prefixRows ++ left) (b :: right) = prefixRows ++ union left (b :: right) := by
  induction prefixRows with
  | nil => rfl
  | cons a rest ih =>
    rw [List.cons_append, union, ite_eq_left (wins a (by simp)),
      ih (fun row mem => wins row (by simp [mem]))]
    rfl

theorem union_prefixRight (prefixRows right : List Row) (a : Row) (left : List Row)
    (wins : ∀ row ∈ prefixRows, row.record.1 < a.record.1) :
    union (a :: left) (prefixRows ++ right) = prefixRows ++ union (a :: left) right := by
  induction prefixRows with
  | nil => rfl
  | cons b rest ih =>
    have smaller := wins b (by simp)
    have notLess : ¬ a.record.1 < b.record.1 := UInt64.not_lt.mpr (UInt64.le_of_lt smaller)
    have notEqual : ¬ (a.record.1 == b.record.1) = true := by
      simp only [beq_iff_eq]
      exact fun e => UInt64.lt_irrefl _ (e ▸ smaller)
    rw [List.cons_append, union, ite_eq_right notLess, ite_eq_right notEqual,
      ih (fun row mem => wins row (by simp [mem]))]
    rfl

theorem bytesOf_append (a b : List Row) : bytesOf (a ++ b) = bytesOf a ++ bytesOf b := by
  induction a with
  | nil => simp [bytesOf]
  | cons row rest ih =>
    simp only [List.cons_append, bytesOf, ih, ByteArray.append_assoc]

end Alvoki.Packed.MergeModel
