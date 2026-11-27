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
      rename_i rest magic gen seqByte lenByte tail h1 h2 h3 h4
      have endEq := ih success
      simp only [bne_iff_ne] at h4
      have heq := Classical.not_not.mp h4
      have hlen := congrArg List.length heq
      simp only [List.length_take, checksumBytes_length, List.splitAt_eq, List.length_drop] at hlen
      change d.cursor.endPos = pos + (lenByte.toNat + 20) + _ at endEq
      simp only [List.splitAt_eq, List.length_drop] at endEq
      simp only [List.length_cons] at ⊢
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
      rename_i rest magic gen seqByte lenByte tail h1 h2 h3 h4
      have recResult := ih success
      change pos + (lenByte.toNat + 20) ≤ d.cursor.endPos ∧ d.cursor.endPos ≤ pos + (lenByte.toNat + 20) + _ ∧ _ at recResult
      simp only [bne_iff_ne] at h4
      have checkEq := Classical.not_not.mp h4
      have checkLength := congrArg List.length checkEq
      simp only [List.length_take, checksumBytes_length, List.splitAt_eq, List.length_drop] at checkLength
      let payload := (tail.drop 8).take lenByte.toNat
      let check := ((tail.drop 8).drop lenByte.toNat).take 8
      let remaining := ((tail.drop 8).drop lenByte.toNat).drop 8
      have headLen : (tail.take 8).length = 8 := by simp only [List.length_take]; omega
      have payloadLen : payload.length = lenByte.toNat := by dsimp [payload]; simp only [List.length_take, List.length_drop]; omega
      have checkLen : check.length = 8 := by dsimp [check]; simp only [List.length_take, List.length_drop]; omega
      have tailEq : tail = tail.take 8 ++ payload ++ check ++ remaining := by
        have a := List.take_append_drop 8 tail
        have b := List.take_append_drop lenByte.toNat (tail.drop 8)
        have c := List.take_append_drop 8 ((tail.drop 8).drop lenByte.toNat)
        dsimp [payload, check, remaining]
        rw [← c] at b
        rw [← b] at a
        simpa [List.append_assoc] using a.symm
      constructor
      · omega
      constructor
      · simp only [List.length_cons, List.splitAt_eq, List.length_drop] at recResult ⊢
        omega
      · intro fuel' enough
        cases fuel' with
        | zero => omega
        | succ k =>
          let n := d.cursor.endPos - (pos + (lenByte.toNat + 20))
          have diff : d.cursor.endPos - pos = 4 + 8 + lenByte.toNat + 8 + n := by dsimp [n]; omega
          have pref : (magic :: gen :: seqByte :: lenByte :: tail).take (d.cursor.endPos - pos) =
              [magic, gen, seqByte, lenByte] ++ tail.take 8 ++ payload ++ check ++ remaining.take n := by
            rw [diff, tailEq]
            have form : 4 + 8 + lenByte.toNat + 8 + n = Nat.succ (Nat.succ (Nat.succ (Nat.succ (8 + lenByte.toNat + 8 + n)))) := by omega
            rw [form]
            simp only [List.take_succ_cons]
            simp [List.take_append, headLen, payloadLen, checkLen, List.take_of_length_le, Nat.add_assoc]
          rw [pref, scan.loop.eq_def]
          simp only [List.cons_append, List.nil_append]
          have headTake : (tail.take 8).take 8 = tail.take 8 := by apply List.take_of_length_le; omega
          have headDrop : (tail.take 8).drop 8 = [] := by apply List.drop_eq_nil_iff.mpr; omega
          have payloadTake : payload.take lenByte.toNat = payload := by rw [← payloadLen]; exact List.take_length
          have payloadDrop : payload.drop lenByte.toNat = [] := by rw [← payloadLen]; exact List.drop_length
          have checkTake : check.take 8 = check := by rw [← checkLen]; exact List.take_length
          have checkDrop : check.drop 8 = [] := by rw [← checkLen]; exact List.drop_length
          simp only [List.splitAt_eq] at checkEq recResult
          have cEq : check = checksumBytes ([magic, gen, seqByte, lenByte] ++ payload) := by
            simpa [check, payload] using checkEq
          have nh : n < k := by omega
          have checkRec := recResult.2.2 k (by change n < k; exact nh)
          change scan.loop policy k (pos + (lenByte.toNat + 20)) (seq + 1) (remaining.take n) (payload :: acc) = .ok d at checkRec
          simp [List.splitAt_eq, headLen, payloadLen, checkLen,
            headTake, headDrop, payloadTake, payloadDrop, checkTake, checkDrop, h1, h2, h3] at *
          simp only [cEq, ite_eq_left]
          change scan.loop policy k (pos + (lenByte.toNat + 20)) (seq + 1) (remaining.take n) (payload :: acc) = .ok d
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
