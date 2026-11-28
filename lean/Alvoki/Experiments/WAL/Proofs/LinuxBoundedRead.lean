import Alvoki.Experiments.WAL.SingleFile
import Alvoki.Experiments.WAL.Proofs.BoundedRead

namespace WalRecoverySlice.SingleFile

/-- An errored fread may consume bytes before reporting an error. The report
carries the primary error and the amount consumed on the same description. -/
abbrev ReadReports (ε : Type) := Bytes → Nat → Option (ε × Nat)

def chunkModel (reports : ReadReports ε) (n : Nat) : EStateM ε Bytes ByteArray :=
  fun remaining =>
    match reports remaining n with
    | some (error, consumed) => .error error (remaining.drop consumed)
    | none => .ok ⟨(remaining.take n).toArray⟩ (remaining.drop n)

/-- A short success ends at EOF. Full reads can advance to a later error. -/
inductive DrainError (reports : ReadReports ε) (error : ε) (after : Bytes) : Bytes → Prop
  | here : reports remaining drainChunk = some (error, consumed) →
      after = remaining.drop consumed → DrainError reports error after remaining
  | later : reports remaining drainChunk = none → drainChunk ≤ remaining.length →
      DrainError reports error after (remaining.drop drainChunk) →
      DrainError reports error after remaining

private theorem drain_model (reports : ReadReports ε) (exhausted : ε) (fuel : Nat)
    (remaining : Bytes) (fits : remaining.length < fuel * drainChunk) :
    match drainWith exhausted (chunkModel reports) fuel remaining with
    | .ok () after => after = []
    | .error error after => DrainError reports error after remaining := by
  induction fuel generalizing remaining with
  | zero => simp at fits
  | succ fuel ih =>
    cases report : reports remaining drainChunk with
    | some pair =>
      obtain ⟨error, consumed⟩ := pair
      simpa only [drainWith, chunkModel, report, Bind.bind, EStateM.bind] using
        (DrainError.here report rfl : DrainError reports error (remaining.drop consumed) remaining)
    | none =>
      by_cases full : drainChunk ≤ remaining.length
      · have nextFits : (remaining.drop drainChunk).length < fuel * drainChunk := by
          rw [List.length_drop]
          rw [Nat.succ_mul] at fits
          omega
        simpa [drainWith, chunkModel, report, Bind.bind, EStateM.bind, ByteArray.size,
          Nat.min_eq_left full, Pure.pure, EStateM.pure] using
          (show match drainWith exhausted (chunkModel reports) fuel (remaining.drop drainChunk) with
            | .ok () after => after = []
            | .error error after => DrainError reports error after remaining from by
              have walked := ih (remaining.drop drainChunk) nextFits
              cases ran : drainWith exhausted (chunkModel reports) fuel (remaining.drop drainChunk) with
              | ok done after => simpa [ran] using walked
              | error error after =>
                rw [ran] at walked
                exact DrainError.later report full walked)
      · have tail : remaining.drop drainChunk = [] := List.drop_eq_nil_iff.mpr (by omega)
        have short : remaining.length ≠ drainChunk := by omega
        simp [drainWith, chunkModel, report, Bind.bind, EStateM.bind, ByteArray.size,
          Nat.min_eq_right (by omega : remaining.length ≤ drainChunk), short, tail, Pure.pure, EStateM.pure]

/-- This runs the executable prefix/drain schedule. Local chunk reports are
the only read premise. A failure may come from any drain read, and leaves
the reached remainder. A success returns the bounded prefix and reached EOF. -/
theorem readPrefixWith_model (reports : ReadReports ε) (exhausted : ε)
    (bytes start : Bytes) (limit fuel : Nat)
    (fits : bytes.length < fuel * drainChunk) :
    let rewind : EStateM ε Bytes Unit := fun _ => .ok () bytes
    match readPrefixWith exhausted rewind (chunkModel reports) limit fuel start with
    | .ok observed after => observed = bytes.take limit ∧ after = []
    | .error error after =>
      (∃ consumed, reports bytes limit = some (error, consumed) ∧ after = bytes.drop consumed) ∨
        (reports bytes limit = none ∧ limit ≤ bytes.length ∧
          DrainError reports error after (bytes.drop limit)) := by
  dsimp only
  cases report : reports bytes limit with
  | some pair =>
    obtain ⟨error, consumed⟩ := pair
    simp [readPrefixWith, chunkModel, report, Bind.bind, EStateM.bind]
  | none =>
    by_cases full : limit ≤ bytes.length
    · have nextFits : (bytes.drop limit).length < fuel * drainChunk := by
        rw [List.length_drop]
        omega
      have walked := drain_model reports exhausted fuel (bytes.drop limit) nextFits
      cases ran : drainWith exhausted (chunkModel reports) fuel (bytes.drop limit) with
      | ok done after =>
        cases done
        rw [ran] at walked
        simpa [readPrefixWith, chunkModel, report, Bind.bind, EStateM.bind, ByteArray.size,
          Nat.min_eq_left full, ran, Pure.pure, EStateM.pure] using walked
      | error error after =>
        rw [ran] at walked
        simpa [readPrefixWith, chunkModel, report, Bind.bind, EStateM.bind, ByteArray.size,
          Nat.min_eq_left full, ran, Pure.pure, EStateM.pure] using
          (show limit ≤ bytes.length ∧ DrainError reports error after (bytes.drop limit) from ⟨full, walked⟩)
    · have tail : bytes.drop limit = [] := List.drop_eq_nil_iff.mpr (by omega)
      have short : bytes.length ≠ limit := by omega
      simp [readPrefixWith, chunkModel, report, Bind.bind, EStateM.bind, ByteArray.size,
        Nat.min_eq_right (by omega : bytes.length ≤ limit), short, tail, Pure.pure, EStateM.pure]

theorem linuxDrainExtent {bytes : Bytes} (extent : bytes.length < 2^63) :
    bytes.length < drainFuel * drainChunk := by
  unfold drainFuel drainChunk
  omega

theorem readPrefixWith_rewind_error (read : Nat → EStateM ε σ ByteArray)
    (rewind : EStateM ε σ Unit) (failure : rewind start = .error error after)
    (exhausted : ε) (limit fuel : Nat) :
    readPrefixWith exhausted rewind read limit fuel start = .error error after := by
  simp [readPrefixWith, Bind.bind, EStateM.bind, failure]

end WalRecoverySlice.SingleFile

namespace WalRecoverySlice.SingleFile

private theorem prefix_of_return
    (reports : ReadReports ε) (exhausted : ε) (bytes start : Bytes) (limit : Nat)
    (extent : bytes.length < 2^63)
    (ran : readPrefixWith exhausted (fun _ => .ok () bytes)
      (chunkModel reports) limit drainFuel start = .ok observed after) :
    observed = bytes.take limit ∧ after = [] := by
  have facts := readPrefixWith_model reports exhausted bytes start limit drainFuel (linuxDrainExtent extent)
  dsimp only at facts
  rw [ran] at facts
  exact facts

theorem marker_after_checked_read
    (reports : ReadReports ε) (exhausted : ε) (bytes start : Bytes) (slot : Nat)
    (extent : bytes.length < 2^63)
    (ran : readPrefixWith exhausted (fun _ => .ok () bytes) (chunkModel reports)
      (markerSize + 1) drainFuel start = .ok observed after) :
    decodeMarker slot observed = decodeMarker slot bytes := by
  rw [(prefix_of_return reports exhausted bytes start _ extent ran).1, boundedMarker_decode]

theorem boundary_after_checked_read
    (reports : ReadReports ε) (exhausted : ε) (bytes start : Bytes) (limit pos : Nat)
    (extent : bytes.length < 2^63) (selected : limit ≤ 65535) (cursor : pos ≤ 65535)
    (ran : readPrefixWith exhausted (fun _ => .ok () bytes) (chunkModel reports)
      65536 drainFuel start = .ok observed after) :
    WalRecoverySlice.scan observed limit .boundary = WalRecoverySlice.scan bytes limit .boundary ∧
      (pos < observed.length ↔ pos < bytes.length) := by
  rw [(prefix_of_return reports exhausted bytes start _ extent ran).1]
  exact ⟨boundedData_scan bytes limit .boundary selected, boundedData_needsRepair bytes pos cursor⟩

theorem logOnly_after_checked_read
    (reports : ReadReports ε) (exhausted : ε) (start : Bytes)
    (dirty : Persistence.Dirty .logOnly known pending image)
    (ran : readPrefixWith exhausted (fun _ => .ok () image.data.live) (chunkModel reports)
      65536 drainFuel start = .ok observed after) :
    observed = image.data.live := by
  have fits := dirty.logOnly_liveFits
  rw [(prefix_of_return reports exhausted image.data.live start _ (by omega) ran).1,
    List.take_of_length_le fits]

end WalRecoverySlice.SingleFile

namespace WalRecoverySlice

private theorem logLoop_inputBound {fuel pos seq : Nat} {rest : Bytes}
    {acc : List Bytes} {decoded : Decoded}
    (success : scan.loop .logOnly fuel pos seq rest acc = .ok decoded) :
    rest.length ≤ (256 - seq) * 52 + 52 := by
  induction fuel generalizing pos seq rest acc with
  | zero => simp [scan.loop.eq_def] at success
  | succ fuel ih =>
    rw [scan.loop.eq_def] at success
    dsimp only at success
    simp only [show (Policy.logOnly == .logOnly) = true by rfl, Bool.true_and] at success
    repeat' first | split at success | contradiction | simp_all only [Except.pure, pure]
    case h_1 => simp
    case h_2.isTrue.isTrue =>
      rename_i rest magic gen seqByte lenByte tail checksum short
      have bounded : (magic :: gen :: seqByte :: lenByte :: tail).length ≤ 52 :=
        of_decide_eq_true short
      omega
    case h_2.isFalse.isFalse.isFalse.isTrue.isTrue =>
      rename_i rest magic gen seqByte lenByte tail header fields size checksum short
      have bounded : (magic :: gen :: seqByte :: lenByte :: tail).length ≤ lenByte.toNat + 20 :=
        of_decide_eq_true short
      change ¬lenByte.toNat > 32 at size
      omega
    case h_2.isFalse.isFalse.isFalse.isFalse =>
      rename_i rest magic gen seqByte lenByte tail header fields size checksum
      have remaining := ih success
      simp only [bne_iff_ne, Bool.or_eq_true, not_or] at fields
      have sequence : seqByte.toNat = seq := Classical.not_not.mp fields.2
      have ordinal : seqByte.toNat < 256 := UInt8.toNat_lt seqByte
      change ¬lenByte.toNat > 32 at size
      simp only [List.length_cons, List.splitAt_eq, List.length_drop] at remaining ⊢
      omega
    case h_3.isTrue =>
      rename_i other nonempty noheader short
      have bounded : rest.length ≤ 20 := of_decide_eq_true short
      omega

theorem oversizedLogCannotOpen {bytes : Bytes} (oversized : 65536 ≤ bytes.length) (decoded : Decoded) :
    scan bytes bytes.length .logOnly ≠ .ok decoded := by
  intro success
  simp only [scan, List.take_length, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at success
  have bounded := logLoop_inputBound success
  omega

/-- Even outside the admitted crash model, a large log-only file and its
bounded observation both fail parsing. Neither can trigger repair. -/
theorem oversizedLog_bothReject {bytes : Bytes} (oversized : 65536 ≤ bytes.length) (decoded : Decoded) :
    scan bytes bytes.length .logOnly ≠ .ok decoded ∧
    scan (bytes.take 65536) (bytes.take 65536).length .logOnly ≠ .ok decoded := by
  refine ⟨oversizedLogCannotOpen oversized decoded, oversizedLogCannotOpen ?_ decoded⟩
  simp [List.length_take, Nat.min_eq_left oversized]

end WalRecoverySlice

namespace WalRecoverySlice.SingleFile

theorem oversizedLog_after_checked_read
    (reports : ReadReports ε) (exhausted : ε) (bytes start : Bytes)
    (extent : bytes.length < 2^63) (oversized : 65536 ≤ bytes.length)
    (ran : readPrefixWith exhausted (fun _ => .ok () bytes) (chunkModel reports)
      65536 drainFuel start = .ok observed after) (decoded : Decoded) :
    WalRecoverySlice.scan bytes bytes.length .logOnly ≠ .ok decoded ∧
    WalRecoverySlice.scan observed observed.length .logOnly ≠ .ok decoded := by
  rw [(prefix_of_return reports exhausted bytes start _ extent ran).1]
  exact oversizedLog_bothReject oversized decoded

end WalRecoverySlice.SingleFile
