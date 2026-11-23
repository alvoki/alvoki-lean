import Block

namespace Alvoki

/-- A lower bound separates the true prefix from the false suffix. -/
def Partition (less : Nat → Bool) (n boundary : Nat) : Prop :=
  boundary ≤ n ∧
    (∀ i, i < boundary → less i = true) ∧
    (∀ i, boundary ≤ i → i < n → less i = false)

theorem lowerBound_partition (less : Nat → Bool) (n lo hi : Nat)
    (monotone : ∀ i j, i ≤ j → j < n → less j = true → less i = true)
    (bounds : lo ≤ hi ∧ hi ≤ n)
    (left : ∀ i, i < lo → less i = true)
    (right : ∀ i, hi ≤ i → i < n → less i = false) :
    Partition less n (lowerBound less lo hi) := by
  rw [lowerBound]
  split
  next h =>
    dsimp only
    split
    next hm =>
      apply lowerBound_partition less n _ _ monotone
      · omega
      · intro i hlt
        apply monotone i (lo + (hi - lo) / 2) <;> first | omega | exact hm
      · exact right
    next hm =>
      apply lowerBound_partition less n _ _ monotone
      · omega
      · exact left
      · intro i hge hin
        cases he : less i
        · rfl
        · exact False.elim (hm (monotone _ _ hge hin he))
  next h =>
    exact ⟨by omega, left, fun i hge hin => right i (by omega) hin⟩
termination_by hi - lo
decreasing_by all_goals omega

theorem search_partition (key : Nat → UInt64) (n : Nat) (target : UInt64)
    (sorted : ∀ i j, i ≤ j → j < n → key i ≤ key j) :
    Partition (fun i => decide (key i < target)) n
      (lowerBound (fun i => decide (key i < target)) 0 n) := by
  apply lowerBound_partition
  · intro i j hij hj h
    exact decide_eq_true (UInt64.lt_of_le_of_lt (sorted i j hij hj) (of_decide_eq_true h))
  · omega
  · intro i h
    omega
  · intro i h hi
    omega

theorem point_complete (key : Nat → UInt64) (n : Nat) (target : UInt64)
    (strict : ∀ i j, i < j → j < n → key i < key j)
    (index : Nat) (within : index < n) (hit : key index = target) :
    lowerBound (fun i => decide (key i < target)) 0 n = index := by
  have sorted : ∀ i j, i ≤ j → j < n → key i ≤ key j := by
    intro i j hij hj
    rcases Nat.eq_or_lt_of_le hij with rfl | h
    · exact UInt64.le_refl _
    · exact UInt64.le_of_lt (strict _ _ h hj)
  let boundary := lowerBound (fun i => decide (key i < target)) 0 n
  have ⟨_, before, after⟩ := search_partition key n target sorted
  change boundary = index
  apply Nat.le_antisymm
  · by_cases goal : boundary ≤ index
    · exact goal
    have h := Nat.lt_of_not_ge goal
    have impossible := of_decide_eq_true (before index h)
    rw [hit] at impossible
    exact False.elim (UInt64.lt_irrefl _ impossible)
  · by_cases goal : index ≤ boundary
    · exact goal
    have h := Nat.lt_of_not_ge goal
    have hlt := strict boundary index h within
    rw [hit] at hlt
    have hfalse := after boundary (Nat.le_refl _) (Nat.lt_trans h within)
    change decide (key boundary < target) = false at hfalse
    rw [decide_eq_true hlt] at hfalse
    contradiction

theorem range_exact (key : Nat → UInt64) (n : Nat) (start stop : UInt64)
    (sorted : ∀ i j, i ≤ j → j < n → key i ≤ key j)
    (i : Nat) (within : i < n) :
    (lowerBound (fun j => decide (key j < start)) 0 n ≤ i ∧
      i < lowerBound (fun j => decide (key j < stop)) 0 n) ↔
      start ≤ key i ∧ key i < stop := by
  have partition_iff (target : UInt64) :
      i < lowerBound (fun j => decide (key j < target)) 0 n ↔ key i < target := by
    have ⟨_, before, after⟩ := search_partition key n target sorted
    constructor
    · intro h
      exact of_decide_eq_true (before i h)
    · intro h
      by_cases goal : i < lowerBound (fun j => decide (key j < target)) 0 n
      · exact goal
      have hge := Nat.le_of_not_lt goal
      have hf := after i hge within
      change decide (key i < target) = false at hf
      rw [decide_eq_true h] at hf
      contradiction
  rw [← Nat.not_lt, partition_iff start, partition_iff stop, UInt64.not_lt]

/-- The scalar little-endian encoder and decoder are inverses. -/
theorem word_roundtrip (value : UInt64) :
    joinBytes (fun i => (splitByte value i).toUInt64) = value := by
  unfold joinBytes splitByte
  change (value >>> 0).toUInt8.toUInt64 |||
    ((value >>> 8).toUInt8.toUInt64 <<< 8) |||
    ((value >>> 16).toUInt8.toUInt64 <<< 16) |||
    ((value >>> 24).toUInt8.toUInt64 <<< 24) |||
    ((value >>> 32).toUInt8.toUInt64 <<< 32) |||
    ((value >>> 40).toUInt8.toUInt64 <<< 40) |||
    ((value >>> 48).toUInt8.toUInt64 <<< 48) |||
    ((value >>> 56).toUInt8.toUInt64 <<< 56) = value
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft', BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth,
    show (UInt64.toBitVec 0 % 64).toNat = 0 by rfl,
    show (UInt64.toBitVec 8 % 64).toNat = 8 by rfl,
    show (UInt64.toBitVec 16 % 64).toNat = 16 by rfl,
    show (UInt64.toBitVec 24 % 64).toNat = 24 by rfl,
    show (UInt64.toBitVec 32 % 64).toNat = 32 by rfl,
    show (UInt64.toBitVec 40 % 64).toNat = 40 by rfl,
    show (UInt64.toBitVec 48 % 64).toNat = 48 by rfl,
    show (UInt64.toBitVec 56 % 64).toNat = 56 by rfl]
  have lane : i < 8 ∨ 8 ≤ i ∧ i < 16 ∨ 16 ≤ i ∧ i < 24 ∨ 24 ≤ i ∧ i < 32 ∨
      32 ≤ i ∧ i < 40 ∨ 40 ≤ i ∧ i < 48 ∨ 48 ≤ i ∧ i < 56 ∨ 56 ≤ i := by omega
  rcases lane with h | h | h | h | h | h | h | h <;>
    simp (discharger := omega) only [decide_eq_true, decide_eq_false, Bool.true_and,
      Bool.false_and, Bool.not_true, Bool.not_false, Bool.false_or, Bool.or_false,
      Nat.zero_add, Nat.add_sub_of_le]

theorem wordFast_eq_word (bytes : ByteArray) (offset : Nat) :
    wordFast bytes offset = word bytes offset := by
  unfold wordFast word joinBytes
  split
  · simp [ByteArray.get!, ByteArray.get, getElem!_pos, show offset < bytes.size by omega,
      show offset + 1 < bytes.size by omega, show offset + 2 < bytes.size by omega,
      show offset + 3 < bytes.size by omega, show offset + 4 < bytes.size by omega,
      show offset + 5 < bytes.size by omega, show offset + 6 < bytes.size by omega,
      show offset + 7 < bytes.size by omega]
  · rfl

theorem lookup_sound (block : Block) (target value : UInt64)
    (hit : block.lookup target = some value) :
    let i := block.lowerBound target
    i < block.count ∧ block.record i = (target, value) := by
  unfold Block.lookup at hit
  dsimp only at hit ⊢
  split at hit
  next h =>
    have ⟨within, keyEq⟩ := Bool.and_eq_true_iff.mp h
    exact ⟨of_decide_eq_true within, Prod.ext (LawfulBEq.eq_of_beq keyEq) (Option.some.inj hit)⟩
  next _ => contradiction

theorem range_ordered (key : Nat → UInt64) (n i j lo hi : Nat)
    (strict : ∀ a b, a < b → b < n → key a < key b)
    (endBound : hi ≤ n) (order : lo ≤ i ∧ i < j ∧ j < hi) :
    key i < key j := strict _ _ order.2.1 (by omega)

theorem getBang_eq_index (bytes : ByteArray) (i : Nat) :
    bytes.get! i = bytes[i]! := by
  by_cases h : i < bytes.size
  · rw [getElem!_pos bytes i h]
    unfold ByteArray.get!
    change bytes.data[i]! = bytes[i]
    rw [getElem!_pos bytes.data i h]
    rfl
  · simp [ByteArray.get!, getElem!_neg, h]

theorem pushWordFast_roundtrip (bytes : ByteArray) (value : UInt64) :
    word (pushWordFast bytes value) bytes.size = value := by
  calc
    _ = joinBytes (fun i => (splitByte value i).toUInt64) := by
      simp only [word, joinBytes, pushWordFast, getBang_eq_index, ByteArray.getElem!_push,
        ByteArray.size_push, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd, Nat.add_left_cancel_iff,
        ite_true]
      simp
    _ = value := word_roundtrip value

set_option maxHeartbeats 1200000 in
/-- Each byte lane can be recovered from the little-endian word. -/
theorem splitByte_joinBytes (byte : Nat → UInt8) (lane : Nat) (bound : lane < 8) :
    splitByte (joinBytes fun i => (byte i).toUInt64) lane = byte lane := by
  have lanes : lane = 0 ∨ lane = 1 ∨ lane = 2 ∨ lane = 3 ∨
      lane = 4 ∨ lane = 5 ∨ lane = 6 ∨ lane = 7 := by omega
  rcases lanes with h | h | h | h | h | h | h | h <;>
    subst lane <;> apply UInt8.toBitVec_inj.mp <;> apply BitVec.eq_of_getLsbD_eq <;>
    intro i hi <;>
    simp only [joinBytes, splitByte, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft,
      UInt64.toBitVec_shiftRight, UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft', BitVec.ushiftRight_eq',
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
      show (UInt64.toBitVec ((8 * 0 : Nat).toUInt64) % 64).toNat = 0 by rfl,
      show (UInt64.toBitVec 8 % 64).toNat = 8 by rfl,
      show (UInt64.toBitVec ((8 * 1 : Nat).toUInt64) % 64).toNat = 8 by rfl,
      show (UInt64.toBitVec 16 % 64).toNat = 16 by rfl,
      show (UInt64.toBitVec ((8 * 2 : Nat).toUInt64) % 64).toNat = 16 by rfl,
      show (UInt64.toBitVec 24 % 64).toNat = 24 by rfl,
      show (UInt64.toBitVec ((8 * 3 : Nat).toUInt64) % 64).toNat = 24 by rfl,
      show (UInt64.toBitVec 32 % 64).toNat = 32 by rfl,
      show (UInt64.toBitVec ((8 * 4 : Nat).toUInt64) % 64).toNat = 32 by rfl,
      show (UInt64.toBitVec 40 % 64).toNat = 40 by rfl,
      show (UInt64.toBitVec ((8 * 5 : Nat).toUInt64) % 64).toNat = 40 by rfl,
      show (UInt64.toBitVec 48 % 64).toNat = 48 by rfl,
      show (UInt64.toBitVec ((8 * 6 : Nat).toUInt64) % 64).toNat = 48 by rfl,
      show (UInt64.toBitVec 56 % 64).toNat = 56 by rfl,
      show (UInt64.toBitVec ((8 * 7 : Nat).toUInt64) % 64).toNat = 56 by rfl] <;>
    simp (discharger := omega) only [decide_eq_true, decide_eq_false,
      Bool.true_and, Bool.false_and, Bool.not_true, Bool.not_false,
      Bool.false_or, Bool.or_false, BitVec.getLsbD_of_ge, Nat.zero_add,
      Nat.add_sub_cancel_left]

private theorem mem_indices {i start n : Nat} :
    i ∈ List.range' start n ↔ start ≤ i ∧ i < start + n := by
  simp only [List.mem_range', Nat.one_mul]
  refine ⟨fun ⟨k, hk, eq⟩ => by omega, fun ⟨ge, lt⟩ => ⟨i - start, by omega, by omega⟩⟩

theorem filterIndexRange (p : Nat → Bool) (lower upper n : Nat)
    (hi : upper ≤ n) (exactly : ∀ i, i < n → (p i = true ↔ lower ≤ i ∧ i < upper)) :
    (List.range n).filter p = List.range' lower (upper - lower) := by
  by_cases valid : lower ≤ upper
  · have left : List.range' 0 lower ++ List.range' lower (upper - lower) = List.range' 0 upper := by
      simpa [Nat.add_sub_of_le valid] using
        (List.range'_append_1 (s := 0) (m := lower) (n := upper - lower))
    have right : List.range' 0 upper ++ List.range' upper (n - upper) = List.range n := by
      rw [List.range_eq_range']
      simpa [Nat.add_sub_of_le hi] using
        (List.range'_append_1 (s := 0) (m := upper) (n := n - upper))
    rw [← right, ← left, List.filter_append, List.filter_append]
    have emptyLeft : (List.range' 0 lower).filter p = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro i mem holds
      have h := mem_indices.mp mem
      have h' := (exactly i (by omega)).mp holds
      omega
    have emptyRight : (List.range' upper (n - upper)).filter p = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro i mem holds
      have h := mem_indices.mp mem
      have h' := (exactly i (by omega)).mp holds
      omega
    have allMiddle : (List.range' lower (upper - lower)).filter p =
        List.range' lower (upper - lower) := by
      apply List.filter_eq_self.mpr
      intro i mem
      have h := mem_indices.mp mem
      exact (exactly i (by omega)).mpr ⟨h.1, by omega⟩
    simp [emptyLeft, emptyRight, allMiddle]
  · rw [show upper - lower = 0 by omega, List.range'_zero]
    apply List.filter_eq_nil_iff.mpr
    intro i mem holds
    have h := (exactly i (List.mem_range.mp mem)).mp holds
    omega

end Alvoki
