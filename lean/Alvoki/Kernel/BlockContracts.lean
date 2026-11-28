import Alvoki.Codec.Block

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

end Alvoki
