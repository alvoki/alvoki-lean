import Alvoki.Experiments.WAL.Proofs.Scan

namespace WalRecoverySlice

private theorem boundaryLoop_end {fuel pos seq : Nat} {rest : Bytes}
    {acc : List Bytes} {d : Decoded}
    (success : scan.loop .boundary fuel pos seq rest acc = .ok d) :
    d.cursor.endPos = pos + rest.length := by
  induction fuel generalizing pos seq rest acc with
  | zero => simp [scan.loop.eq_def] at success
  | succ fuel ih =>
    rw [scan.loop.eq_def] at success
    dsimp only at success
    repeat' first | split at success | contradiction | simp_all only [Except.pure, pure]
    all_goals try {cases success; simp_all}
    all_goals
      rename_i rest magic gen seqByte lenByte headerCheck tail h1 h2 h3 trailer check remaining heq h4
      have endEq := ih success
      have lenEq := congrArg List.length heq
      simp only [List.splitAt_eq, List.length_drop, List.length_cons] at lenEq
      simp only [List.length_cons] at ⊢
      change d.cursor.endPos = pos + (_ + 6) + _ at endEq
      omega

private theorem loop_repair {policy : Policy} {fuel pos seq : Nat} {rest : Bytes}
    {acc : List Bytes} {d : Decoded}
    (success : scan.loop policy fuel pos seq rest acc = .ok d) :
    pos ≤ d.cursor.endPos ∧ d.cursor.endPos ≤ pos + rest.length ∧
      ∀ fuel', d.cursor.endPos - pos < fuel' →
        scan.loop policy fuel' pos seq (rest.take (d.cursor.endPos - pos)) acc = .ok d := by
  induction fuel generalizing pos seq rest acc with
  | zero => simp [scan.loop.eq_def] at success
  | succ fuel ih =>
    rw [scan.loop.eq_def] at success
    dsimp only at success
    repeat' first | split at success | contradiction | simp_all only [Except.pure, pure]
    all_goals try {
      cases success
      simp only [Nat.le_refl, Nat.le_add_right, Nat.sub_self, List.take_zero, true_and]
      intro fuel' hf
      cases fuel' with
      | zero => omega
      | succ k => rw [scan.loop.eq_def]; rfl
    }
    all_goals
      rename_i rest magic gen seqByte lenByte headerCheck tail h1 h2 h3 trailer check remaining heq h4
      have recResult := ih success
      change pos + (lenByte.toNat + 6) ≤ d.cursor.endPos ∧ d.cursor.endPos ≤ pos + (lenByte.toNat + 6) + remaining.length ∧ _ at recResult
      have dropEq : tail.drop lenByte.toNat = check :: remaining := by simpa [List.splitAt_eq] using heq
      have lenEq := congrArg List.length dropEq
      simp only [List.length_drop, List.length_cons] at lenEq
      have tailEq : tail = tail.take lenByte.toNat ++ check :: remaining := by
        have t := List.take_append_drop lenByte.toNat tail
        rw [dropEq] at t
        exact t.symm
      have takeLen : (tail.take lenByte.toNat).length = lenByte.toNat := by
        simp only [List.length_take]
        omega
      constructor
      · omega
      constructor
      · simp only [List.length_cons]
        omega
      · intro fuel' enough
        cases fuel' with
        | zero => omega
        | succ k =>
          let n := d.cursor.endPos - (pos + (lenByte.toNat + 6))
          have diff : d.cursor.endPos - pos = 5 + lenByte.toNat + 1 + n := by dsimp [n]; omega
          have pref : (magic :: gen :: seqByte :: lenByte :: headerCheck :: tail).take (d.cursor.endPos - pos) =
              [magic, gen, seqByte, lenByte, headerCheck] ++ tail.take lenByte.toNat ++ [check] ++ remaining.take n := by
            rw [diff, tailEq]
            have form : 5 + lenByte.toNat + 1 + n = Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (lenByte.toNat + 1 + n))))) := by omega
            rw [form]
            simp only [List.take_succ_cons]
            simp only [List.take_append, takeLen]
            rw [List.take_of_length_le (by rw [takeLen]; omega)]
            simp [List.take_take, Nat.add_assoc, Nat.add_comm 1 n]
          rw [pref, scan.loop.eq_def]
          simp only [List.cons_append, List.nil_append]
          simp only [h1, h2, h3, ite_false]
          simp only [List.splitAt_eq] at h4 recResult
          have nh : n < k := by omega
          have checkRec := recResult.2.2 k (by change n < k; exact nh)
          change scan.loop policy k (pos + (lenByte.toNat + 6)) (seq + 1) (remaining.take n) (tail.take lenByte.toNat :: acc) = .ok d at checkRec
          simp [List.splitAt_eq, takeLen, h1, h2, h3] at *
          simp only [h4, ite_eq_left]
          change scan.loop policy k (pos + (lenByte.toNat + 6)) (seq + 1) (remaining.take n) (tail.take lenByte.toNat :: acc) = .ok d
          exact checkRec

theorem scan_repair_stable {bytes : Bytes} {limit : Nat} {policy : Policy} {decoded : Decoded}
    (success : scan bytes limit policy = .ok decoded) :
    scan (bytes.take decoded.cursor.endPos) decoded.cursor.endPos policy = .ok decoded := by
  simp only [scan] at success ⊢
  split at success
  · contradiction
  · rename_i fits
    simp only [bne_iff_ne] at fits
    have info := loop_repair success
    have bound : decoded.cursor.endPos ≤ limit := by omega
    have lengthBound : decoded.cursor.endPos ≤ bytes.length := by
      rw [List.length_take] at fits
      omega
    have lengthEq : (bytes.take decoded.cursor.endPos).length = decoded.cursor.endPos := by
      simp [List.length_take, Nat.min_eq_left lengthBound]
    simp only [lengthEq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.take_take,
      Nat.min_self]
    have result := info.2.2 (decoded.cursor.endPos + 1) (by simp)
    simpa [List.take_take, Nat.min_eq_left bound] using result

theorem scan_boundary_end {bytes : Bytes} {limit : Nat} {decoded : Decoded}
    (success : scan bytes limit .boundary = .ok decoded) : decoded.cursor.endPos = limit := by
  simp only [scan] at success
  split at success
  · contradiction
  · rename_i fits
    have h := boundaryLoop_end success
    simp only [bne_iff_ne] at fits
    omega

theorem scan_boundary_repair_stable {bytes : Bytes} {limit : Nat} {decoded : Decoded}
    (success : scan bytes limit .boundary = .ok decoded) :
    scan (bytes.take decoded.cursor.endPos) decoded.cursor.endPos .boundary = .ok decoded := by
  have endEq := scan_boundary_end success
  rw [endEq]
  simpa [scan, List.take_take] using success

end WalRecoverySlice
