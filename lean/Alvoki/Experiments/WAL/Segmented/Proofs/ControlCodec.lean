import Alvoki.Experiments.WAL.Segmented.ControlCodec
import Init.Data.List.SplitOn.Lemmas

namespace WalRecoverySlice.Segmented.ControlCodec

private theorem digit_val (n : Nat) : (digit n).toNat = 48 + n % 10 := by
  simp [digit, Nat.toUInt8, Nat.mod_eq_of_lt (show 48 + n % 10 < 256 by omega)]

private theorem decimal_read (n : Nat) : readDecimal (decimal n) = n := by
  induction n using decimal.induct with
  | case1 n h =>
    rw [decimal, ite_eq_left h]
    simp [readDecimal, digit_val, Nat.mod_eq_of_lt h]
  | case2 n h ih =>
    rw [decimal, ite_eq_right h]
    simp only [readDecimal, List.foldl_append, List.foldl_cons, List.foldl_nil, digit_val] at *
    omega

private theorem decimal_space (n : Nat) : (32 : UInt8) ∉ decimal n := by
  have neq (k : Nat) : (32 : UInt8) ≠ digit k := by
    intro heq
    have := congrArg UInt8.toNat heq
    rw [digit_val] at this
    change 32 = _ at this
    omega
  induction n using decimal.induct with
  | case1 n h => simp [decimal, h, neq]
  | case2 n h ih => rw [decimal, ite_eq_right h]; simp [ih, neq]

/-- Every control with representable position fields survives the native wire
codec, including the checksum and strict canonical-format comparison. -/
theorem decode_encode (c : Control) (active : c.active ≤ wordMax)
    (discarded : c.discarded ≤ wordMax) : decode (encode c) = some c := by
  have spaces : ∀ f ∈ fields c, (32 : UInt8) ∉ f := by
    cases c with
    | mk p cap last base =>
      cases p <;> simp [fields, decimal_space] <;> decide +revert
  let body := [32].intercalate (fields c)
  have raw : (encode c).data.toList = body ++ checksumBytes body := by simp [encode, body]
  unfold decode
  rw [raw]
  simp only [List.length_append, checksumBytes_length, Nat.add_sub_cancel, List.take_left]
  rw [List.splitOn_intercalate 32 spaces (by simp [fields])]
  cases c with
  | mk p cap last base =>
    have distinct : modeBytes .boundary ≠ modeBytes .logOnly := by decide
    cases p <;> simp_all [fields, decimal_read]

/-- A successful read always validates the complete canonical record. -/
theorem canonical_of_decode {bytes : ByteArray} {c : Control}
    (parsed : decode bytes = some c) : bytes = encode c := by
  simp only [decode] at parsed
  split at parsed
  · split at parsed <;> simp_all
  · contradiction

private theorem decimal_length (k n : Nat) (positive : 0 < k) (fits : n < 10^k) :
    (decimal n).length ≤ k := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    rw [decimal]
    split
    · simp
    · have bound : n / 10 < 10^k := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        simpa [Nat.pow_succ] using fits
      have pos : 0 < k := by
        cases k <;> simp_all
      have := ih (n / 10) pos bound
      simp_all

/-- Every control of a supported segment capacity fits the native metadata read cap. -/
theorem encoded_size (c : Control) (capacity : c.capacity ≤ 255)
    (active : c.active ≤ wordMax) (discarded : c.discarded ≤ wordMax) :
    (encode c).size ≤ 80 := by
  have ncap := decimal_length 3 c.capacity (by decide) (by omega)
  have nlast := decimal_length 20 c.active (by decide) (by unfold wordMax Contract.maxPosition at active; omega)
  have nbase := decimal_length 20 c.discarded (by decide) (by unfold wordMax Contract.maxPosition at discarded; omega)
  have vlen : version.length = 5 := by decide
  have mlen : (modeBytes c.policy).length ≤ 8 := by cases c.policy <;> decide
  change (([32].intercalate (fields c) ++ checksumBytes _).toArray).size ≤ 80
  simp [fields, List.intercalate_cons_cons, vlen]
  omega

end WalRecoverySlice.Segmented.ControlCodec
