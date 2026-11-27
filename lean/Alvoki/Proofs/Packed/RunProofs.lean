import Alvoki.Codec.BlockCodec

namespace Alvoki.Packed
open Alvoki.Opt

/-- V1 acceptance in terms of the bytes and the natural-offset key order. -/
def ValidV1 (bytes : ByteArray) : Prop :=
  let count := (word bytes 0).toNat
  bytes.size < USize.size ∧ word bytes 8 = 1 ∧ bytes.size = 16 + 16 * count ∧
    ∀ i j : Nat, i < j → j < count → word bytes (16 + i * 16) < word bytes (16 + j * 16)

theorem parseRun_iff (bytes : ByteArray) : (∃ run, parseRun bytes = .ok run) ↔ ValidV1 bytes := by
  constructor
  · rintro ⟨run, h⟩
    have ⟨parsed, version⟩ := parseRun_spec h
    have ⟨source, count, _⟩ := parseView_spec parsed
    refine ⟨source ▸ run.view.fits, version, ?_, ?_⟩
    · rw [count, ← source]
      exact run.view.size_eq
    · intro i j less bound
      have ordered := run.view.logical_ordered run.ordered i j less (count ▸ bound)
      simpa [View.logicalRecord, source, run.interleaved.1] using ordered
  · rintro ⟨fits, version, size, order⟩
    obtain ⟨view, parsed, _⟩ := parseView_v1_complete bytes _ size fits version rfl
      (fun view source count stride _ => view.validate_complete fun i j ij jHit => by
        rw [view.key_eq (USize.lt_trans ij jHit), view.key_eq jHit]
        simp only [View.logicalRecord, source, stride]
        exact order _ _ (USize.lt_iff_toNat_lt.mp ij) (count ▸ USize.lt_iff_toNat_lt.mp jHit))
    obtain ⟨run, h, _⟩ := parseRun_of_view parsed version
    exact ⟨run, h⟩

theorem parseRun_rejects_version {bytes : ByteArray} (wrong : word bytes 8 ≠ 1) :
    ¬ ∃ run, parseRun bytes = .ok run :=
  fun accepted => wrong ((parseRun_iff bytes).mp accepted).2.1

theorem parseRun_rejects_length {bytes : ByteArray}
    (wrong : bytes.size ≠ 16 + 16 * (word bytes 0).toNat) :
    ¬ ∃ run, parseRun bytes = .ok run :=
  fun accepted => wrong ((parseRun_iff bytes).mp accepted).2.2.1

theorem parseRun_rejects_short {bytes : ByteArray} (short : bytes.size < 16) :
    ¬ ∃ run, parseRun bytes = .ok run :=
  parseRun_rejects_length (by omega)

theorem parseRun_rejects_keys {bytes : ByteArray} {i j : Nat} (order : i < j)
    (within : j < (word bytes 0).toNat)
    (wrong : ¬ word bytes (16 + i * 16) < word bytes (16 + j * 16)) :
    ¬ ∃ run, parseRun bytes = .ok run :=
  fun accepted => wrong (((parseRun_iff bytes).mp accepted).2.2.2 i j order within)

def EncodableV1 (rows : Array Record) : Prop :=
  16 + 16 * rows.size < USize.size ∧ rows.size < UInt64.size ∧
    ∀ i j : Nat, (less : i < j) → (hit : j < rows.size) →
      (rows[i]'(by omega)).1 < rows[j].1

theorem encodeV1_injective {left right : Array Record} (leftValid : EncodableV1 left)
    (rightValid : EncodableV1 right) (same : encodeV1 left = encodeV1 right) : left = right := by
  obtain ⟨a, pa, da⟩ := encodeV1_roundtrip left leftValid.1 leftValid.2.1 leftValid.2.2
  obtain ⟨b, pb, db⟩ := encodeV1_roundtrip right rightValid.1 rightValid.2.1 rightValid.2.2
  rw [same, pb] at pa
  have eq : b = a := Except.ok.inj pa
  exact da.symm.trans (eq ▸ db)

@[simp] theorem Run.decodeV1_size (run : Run) : run.decodeV1.size = run.count.toNat := by
  simp [Run.decodeV1]

@[simp] theorem Run.decodeV1_get (run : Run) (i : Nat) (within : i < run.decodeV1.size) :
    run.decodeV1[i] = run.view.logicalRecord i := by
  simp [Run.decodeV1]

private theorem Run.lookup_position (run : Run) (target : UInt64) {index : Nat}
    (hit : index < run.count.toNat) (found : (run.view.logicalRecord index).1 = target) :
    (run.view.lowerBound target).toNat = index := by
  have ⟨_, before, after⟩ := run.view.lowerBound_partition run.ordered target
  apply Nat.le_antisymm
  · by_cases late : index < (run.view.lowerBound target).toNat
    · exfalso
      simpa [found] using before index late
    · omega
  · by_cases early : (run.view.lowerBound target).toNat < index
    · have atBoundary := run.view.logical_ordered run.ordered _ index early hit
      have hb : (run.view.lowerBound target).toNat < run.view.count.toNat := Nat.lt_trans early hit
      have missing := after (run.view.lowerBound target).toNat (Nat.le_refl _) hb
      rw [found] at atBoundary
      simp [atBoundary] at missing
    · omega

/-- Lookup returns exactly a row with the queried key and returned value. -/
theorem Run.lookup_some_iff (run : Run) (target value : UInt64) :
    run.lookup target = some value ↔
      ∃ i : Nat, ∃ hit : i < run.decodeV1.size, run.decodeV1[i] = (target, value) := by
  unfold Run.lookup View.lookup
  let i := run.view.lowerBound target
  change (if i < run.view.count && run.view.keyOrZero i == target then
    some (run.view.valueOrZero i) else none) = some value ↔ _
  constructor
  · intro found
    split at found
    next h =>
      have ⟨within, key⟩ := Bool.and_eq_true_iff.mp h
      have hit : i < run.view.count := of_decide_eq_true within
      have hv := Option.some.inj found
      refine ⟨i.toNat, by simpa [Run.count] using USize.lt_iff_toNat_lt.mp hit, ?_⟩
      rw [Run.decodeV1_get]
      exact Prod.ext ((run.view.key_eq hit).symm.trans (beq_iff_eq.mp key))
        ((run.view.value_eq hit).symm.trans hv)
    next => contradiction
  · rintro ⟨j, hit, row⟩
    rw [Run.decodeV1_get] at row
    have cardinal : j < run.count.toNat := by simpa using hit
    have position : i.toNat = j := run.lookup_position target cardinal (congrArg Prod.fst row)
    have within : i < run.view.count := USize.lt_iff_toNat_lt.mpr (by rwa [position])
    rw [run.view.key_eq within, run.view.value_eq within, position, row]
    simp [within]

theorem Run.lookup_none_iff (run : Run) (target : UInt64) :
    run.lookup target = none ↔ ∀ i : Nat, ∀ hit : i < run.decodeV1.size,
      run.decodeV1[i].1 ≠ target := by
  constructor
  · intro absent i hit key
    have found := (run.lookup_some_iff target run.decodeV1[i].2).mpr
      ⟨i, hit, Prod.ext key rfl⟩
    simp [absent] at found
  · intro absent
    cases h : run.lookup target with
    | none => rfl
    | some value =>
      obtain ⟨i, hit, found⟩ := (run.lookup_some_iff target value).mp h
      exact (absent i hit (congrArg Prod.fst found)).elim

/-- Exact decoded rows in the half-open interval, in their original key order. -/
def Run.rangeRows (run : Run) (start stop : UInt64) : List Record :=
  run.decodeV1.toList.filter fun row => start ≤ row.1 && row.1 < stop

private theorem decodedRows (run : Run) :
    run.decodeV1.toList = (List.range run.count.toNat).map run.view.logicalRecord := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp

theorem Run.rangeRows_eq (run : Run) (start stop : UInt64) :
    run.rangeRows start stop =
      (List.range' (run.view.lowerBound start).toNat
        ((run.view.lowerBound stop).toNat - (run.view.lowerBound start).toNat)).map
        run.view.logicalRecord := by
  have ⟨_, beforeLo, afterLo⟩ := run.view.lowerBound_partition run.ordered start
  have ⟨hi, beforeHi, afterHi⟩ := run.view.lowerBound_partition run.ordered stop
  rw [Run.rangeRows, decodedRows, List.filter_map]
  apply congrArg (List.map run.view.logicalRecord)
  apply filterIndexRange _ _ _ _ hi
  intro i within
  have lower : start ≤ (run.view.logicalRecord i).1 ↔ (run.view.lowerBound start).toNat ≤ i := by
    constructor
    · intro h
      by_cases early : i < (run.view.lowerBound start).toNat
      · have lt := of_decide_eq_true (beforeLo i early)
        exact False.elim (UInt64.not_lt.mpr h lt)
      · omega
    · intro ge
      exact UInt64.not_lt.mp (of_decide_eq_false (afterLo i ge within))
  have upper : (run.view.logicalRecord i).1 < stop ↔ i < (run.view.lowerBound stop).toNat := by
    constructor
    · intro h
      by_cases late : (run.view.lowerBound stop).toNat ≤ i
      · exact False.elim (of_decide_eq_false (afterHi i late within) h)
      · omega
    · intro early
      exact of_decide_eq_true (beforeHi i early)
  simp [lower, upper]

private theorem scanFrom_fold (view : View) (i j : USize) (endBound : j ≤ view.count)
    (initial : UInt64) :
    view.scanFrom i j initial =
      ((List.range' i.toNat (j.toNat - i.toNat)).map view.logicalRecord).foldl
        (fun sum row => sum + (row.1 ^^^ row.2)) initial := by
  rw [View.scanFrom]
  by_cases hit : i < j
  · rw [dite_eq_left hit]
    have within := USize.lt_of_lt_of_le hit endBound
    have order := USize.lt_iff_toNat_lt.mp hit
    have step := addOne i j order
    have remaining : j.toNat - i.toNat = (j.toNat - (i + 1).toNat) + 1 := by omega
    rw [remaining, List.range'_succ, List.map_cons, List.foldl_cons, view.key_eq within,
      view.value_eq within, ← step]
    exact scanFrom_fold view (i + 1) j endBound _
  · have n : j.toNat - i.toNat = 0 := by
      rw [USize.lt_iff_toNat_lt] at hit
      omega
    simp [hit, n]
termination_by j.toNat - i.toNat
decreasing_by omega

theorem Run.rangeChecksum_eq (run : Run) (start stop : UInt64) :
    run.rangeChecksum start stop =
      (run.rangeRows start stop).foldl (fun sum row => sum + (row.1 ^^^ row.2)) 0 := by
  have h := (run.view.lowerBound_partition run.ordered stop).1
  have le : run.view.lowerBound stop ≤ run.view.count := USize.le_iff_toNat_le.mpr h
  rw [Run.rangeChecksum, View.scan, USize.min_def, ite_eq_left le, run.rangeRows_eq]
  exact scanFrom_fold _ _ _ le _

theorem Run.rangeChecksum_empty (run : Run) {start stop : UInt64} (reversed : stop ≤ start) :
    run.rangeChecksum start stop = 0 := by
  rw [run.rangeChecksum_eq, Run.rangeRows, List.filter_eq_nil_iff.mpr]
  · rfl
  · intro row _ included
    have h : start ≤ row.1 ∧ row.1 < stop := by simpa using included
    exact UInt64.not_lt.mpr (UInt64.le_trans reversed h.1) h.2

end Alvoki.Packed
