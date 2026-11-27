import Alvoki.Experiments.WAL.Recovery

namespace WalRecoverySlice

/-- Consecutively numbered frames, beginning at the given sequence number. -/
def encodeFrames (first : Nat) : List Bytes → Bytes
  | [] => []
  | payload :: rest => frame first payload ++ encodeFrames (first + 1) rest

theorem frame_length (seq : Nat) (payload : Bytes) :
    (frame seq payload).length = payload.length + 6 := by
  simp [frame]

private theorem step_frame (policy : Policy) (fuel pos seq : Nat) (payload rest : Bytes)
    (acc : List Bytes) (fits : seq ≤ 255) (bounded : payload.length ≤ 32) :
    scan.loop policy (fuel + 1) pos seq (frame seq payload ++ rest) acc =
      scan.loop policy fuel (pos + (frame seq payload).length) (seq + 1) rest (payload :: acc) := by
  have seqByte : seq.toUInt8.toNat = seq := Nat.mod_eq_of_lt (by omega : seq < 256)
  have lenByte : payload.length.toUInt8.toNat = payload.length :=
    Nat.mod_eq_of_lt (by omega : payload.length < 256)
  rw [frame_length, scan.loop.eq_def]
  simp [frame, List.append_assoc, seqByte, lenByte, List.splitAt_eq]
  split <;> rename_i h
  · change 32 < payload.length at h
    omega
  · rfl

private theorem scanLoop_prefix {policy : Policy} {fuel pos seq : Nat} {rest : Bytes}
    {acc : List Bytes} {d : Decoded} (success : scan.loop policy fuel pos seq rest acc = .ok d) :
    acc.reverse <+: d.batches := by
  induction fuel generalizing pos seq rest acc with
  | zero => simp [scan.loop.eq_def] at success
  | succ fuel ih =>
    rw [scan.loop.eq_def] at success
    dsimp only at success
    repeat' first | split at success | contradiction | simp_all only [Except.pure, pure]
    all_goals first
      | cases success; exact List.prefix_refl _
      | have h := ih success; exact List.IsPrefix.trans (by simp) h

theorem encodeFrames_snoc (first : Nat) (batches : List Bytes) (p : Bytes) :
    encodeFrames first (batches ++ [p]) =
      encodeFrames first batches ++ frame (first + batches.length) p := by
  induction batches generalizing first with
  | nil => simp [encodeFrames]
  | cons head tail ih =>
    simp [encodeFrames, ih, List.append_assoc, Nat.add_assoc, Nat.add_comm 1]

private theorem count_le_encoded (first : Nat) (batches : List Bytes) :
    batches.length ≤ (encodeFrames first batches).length := by
  induction batches generalizing first with
  | nil => simp
  | cons head tail ih =>
    simp only [encodeFrames, List.length_append, frame_length, List.length_cons]
    have := ih (first + 1)
    omega

private theorem consume_frames (policy : Policy) (batches : List Bytes) (suffix : Bytes)
    (pos seq fuel : Nat) (acc : List Bytes) (fits : seq + batches.length ≤ 256)
    (bounded : ∀ p ∈ batches, p.length ≤ 32) :
    scan.loop policy (fuel + batches.length) pos seq (encodeFrames seq batches ++ suffix) acc =
      scan.loop policy fuel (pos + (encodeFrames seq batches).length)
        (seq + batches.length) suffix (batches.reverse ++ acc) := by
  induction batches generalizing pos seq acc with
  | nil => simp [encodeFrames]
  | cons p rest ih =>
    simp only [List.length_cons, Nat.add_succ, encodeFrames, List.append_assoc]
    rw [step_frame _ _ _ _ _ _ _ (by simp at fits; omega) (bounded p (by simp))]
    rw [ih _ _ _ (by simp at fits; omega) (by intro q h; exact bounded q (by simp [h]))]
    simp [List.append_assoc, Nat.add_assoc, Nat.add_comm 1]

/-- A bounded read ending at the last committed frame ignores any following bytes. -/
theorem scan_encodeFrames_append {batches : List Bytes} (suffix : Bytes) (policy : Policy)
    (bounded : ∀ p ∈ batches, p.length ≤ 32) (fits : batches.length ≤ 255) :
    scan (encodeFrames 1 batches ++ suffix) (encodeFrames 1 batches).length policy =
      .ok ⟨batches, ⟨(encodeFrames 1 batches).length, 1 + batches.length⟩⟩ := by
  simp [scan]
  have enough := count_le_encoded 1 batches
  generalize h : (encodeFrames 1 batches).length = n
  have fuel : n + 1 = ((n - batches.length) + 1) + batches.length := by omega
  rw [fuel]
  conv => lhs; arg 5; rw [← List.append_nil (encodeFrames 1 batches)]
  rw [consume_frames _ _ _ _ _ _ _ (by omega) bounded]
  simp [scan.loop.eq_def, h, pure, Except.pure]

theorem scan_encodeFrames {batches : List Bytes} (policy : Policy)
    (bounded : ∀ p ∈ batches, p.length ≤ 32) (fits : batches.length ≤ 255) :
    scan (encodeFrames 1 batches) (encodeFrames 1 batches).length policy =
      .ok ⟨batches, ⟨(encodeFrames 1 batches).length, 1 + batches.length⟩⟩ := by
  simpa using scan_encodeFrames_append [] policy bounded fits

/-- A successful scan cannot remove or reorder any acknowledged batch while
its selected bytes still contain those exact frames. -/
theorem scan_preserves_encoded_prefix {batches : List Bytes} {bytes suffix : Bytes}
    {limit : Nat} {policy : Policy} {decoded : Decoded}
    (bounded : ∀ p ∈ batches, p.length ≤ 32) (fits : batches.length ≤ 255)
    (selected : bytes.take limit = encodeFrames 1 batches ++ suffix)
    (success : scan bytes limit policy = .ok decoded) : batches <+: decoded.batches := by
  simp only [scan] at success
  split at success
  · contradiction
  · rw [selected] at success
    have enough := count_le_encoded 1 batches
    have avail := List.length_take_le limit bytes
    rw [selected, List.length_append] at avail
    have fuel : limit + 1 = (limit + 1 - batches.length) + batches.length := by omega
    rw [fuel, consume_frames _ _ _ _ _ _ _ (by omega) bounded] at success
    simpa using scanLoop_prefix success

private theorem torn_frame (fuel pos seq : Nat) (p : Bytes) (acc : List Bytes)
    (cut : Nat) (short : cut < (frame seq p).length) (fits : seq ≤ 255)
    (bounded : p.length ≤ 32) :
    scan.loop .logOnly (fuel + 1) pos seq ((frame seq p).take cut) acc =
      .ok ⟨acc.reverse, ⟨pos, seq⟩⟩ := by
  have seqByte : seq.toUInt8.toNat = seq := Nat.mod_eq_of_lt (by omega : seq < 256)
  have lenByte : p.length.toUInt8.toNat = p.length :=
    Nat.mod_eq_of_lt (by omega : p.length < 256)
  rw [scan.loop.eq_def]
  match cut with
  | 0 | 1 | 2 | 3 | 4 => rfl
  | k + 5 =>
    rw [frame_length] at short
    have within : k ≤ p.length := by omega
    have tail (trailer : UInt8) : (p ++ [trailer]).take k = p.take k := by
      simp [List.take_append, Nat.sub_eq_zero_of_le within]
    have dropped : (p.take k).drop p.length = [] := List.drop_eq_nil_iff.mpr (by simp; omega)
    simp [frame, tail, seqByte, lenByte, dropped, Nat.min_eq_left within]
    split <;> rename_i h
    · change 32 < p.length at h
      omega
    · split
      · rfl
      · rename_i h
        simp at h
        have impossible := h rfl
        change p.length + 6 < k + 1 + 1 + 1 + 1 + 1 at impossible
        omega

/-- Every proper byte prefix of the next genuine frame can be discarded on a
log-only reopen, even after the entire header and payload reached the disk. -/
theorem scan_torn_encodeFrames {batches : List Bytes} (p : Bytes) (cut : Nat)
    (bounded : ∀ q ∈ batches, q.length ≤ 32) (fits : batches.length < 255)
    (nextBounded : p.length ≤ 32) (short : cut < (frame (1 + batches.length) p).length) :
    let bytes := encodeFrames 1 batches ++ (frame (1 + batches.length) p).take cut
    scan bytes bytes.length .logOnly =
      .ok ⟨batches, ⟨(encodeFrames 1 batches).length, 1 + batches.length⟩⟩ := by
  dsimp only
  simp only [scan, List.take_length]
  simp
  have enough := count_le_encoded 1 batches
  generalize h : (encodeFrames 1 batches).length +
    min cut (frame (1 + batches.length) p).length = n
  have fuel : n + 1 = ((n - batches.length) + 1) + batches.length := by omega
  rw [fuel, consume_frames _ _ _ _ _ _ _ (by omega) bounded]
  rw [torn_frame _ _ _ _ _ _ short (by omega) nextBounded]
  simp

end WalRecoverySlice
