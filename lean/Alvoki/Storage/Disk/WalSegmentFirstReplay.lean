import Alvoki.Storage.Disk.WalSegmentMarkerRead

namespace Alvoki.Storage

open WAL (frameSize)

private theorem WalSegment.Chain.start_le {history : List WAL.Write} {first : Nat}
    {segments : List WalSegment} (chain : Chain history first segments) : first ≤ history.length := by
  induction chain with
  | endOfHistory => exact Nat.le_refl _
  | cons step _ _ _ tail => exact Nat.le_trans step tail

theorem WalSegment.Chain.startsWithin {history : List WAL.Write} {first : Nat}
    {segments : List WalSegment} (chain : Chain history first segments) :
    ∀ segment ∈ segments, segment.first ≤ history.length := by
  induction chain with
  | endOfHistory => simp
  | cons step _ _ rest ih =>
    intro segment member
    rcases List.mem_cons.mp member with rfl | later
    · exact Nat.le_trans step rest.start_le
    · exact ih segment later

private theorem payloadBytes_of_chain (sealed : List WalSegment) (keeper : WalSegment) (tail : ByteArray) :
    walSegmentPayloadBytes (sealed.map (fun segment => (segment.first, segment.bytes)) ++
      [(keeper.first, keeper.bytes ++ tail)]) = WalSegment.concatenate (sealed ++ [keeper]) ++ tail := by
  induction sealed with
  | nil => simp [walSegmentPayloadBytes, WalSegment.concatenate]
  | cons head rest ih =>
    change head.bytes ++ walSegmentPayloadBytes _ = (head.bytes ++ WalSegment.concatenate _) ++ tail
    rw [ByteArray.append_assoc]
    exact congrArg (head.bytes ++ ·) ih

theorem WalSegment.Chain.keeperBytes {history : List WAL.Write} {first : Nat}
    {sealed : List WalSegment} {keeper : WalSegment}
    (chain : Chain history first (sealed ++ [keeper])) :
    keeper.bytes = WAL.encode (history.drop keeper.first) := by
  have reaches {start : Nat} (empty : Chain history start []) : start = history.length := by
    cases empty
    rfl
  induction sealed generalizing first with
  | nil =>
    cases chain with
    | cons _ _ bytes done =>
      rw [bytes, reaches done, List.take_of_length_le (by simp)]
  | cons earlier later ih =>
    cases chain with
    | cons _ _ _ remaining => exact ih remaining

/-- Each observed sealed file supplies its exact canonical span and the
keeper can carry an arbitrary unselected tail. The executable per-file
reader's replay therefore agrees with replay on the complete history. -/
theorem WalSegment.Chain.replaysMarked {history : List WAL.Write} {first : Nat}
    {sealed : List WalSegment} {keeper : WalSegment} {base table : PackedTable} {count : UInt64}
    (chain : Chain history first (sealed ++ [keeper])) (tail : ByteArray)
    (absolute : count.toNat = history.length * frameSize)
    (covers : first ≤ base.committed.toNat) (ordered : WAL.OrdinalsFrom 1 history)
    (fullReplay : recoverSelected base (WAL.encode history) = .ok table) :
    recoverMarkedWalSegments base count
      (sealed.map (fun segment => (segment.first, segment.bytes)) ++ [(keeper.first, keeper.bytes ++ tail)]) =
        .ok (WAL.encode (history.drop first), table) := by
  let files := sealed.map (fun segment => (segment.first, segment.bytes)) ++ [(keeper.first, keeper.bytes ++ tail)]
  have through : count.toNat / frameSize = history.length := by
    rw [absolute, Nat.mul_div_cancel _ (by decide : 0 < frameSize)]
  have aligned : count.toNat % frameSize = 0 := by rw [absolute, Nat.mul_mod_left]
  have span : checkWalSegmentSpans history.length files = true :=
    chain.checkReadSpans chain.start_le (Nat.le_refl _)
  have keeperWithin := chain.startsWithin keeper (List.mem_append_right _ (by simp))
  have checked : checkSelectedWalSegmentSpans history.length files = true := by
    rw [checkSelectedWalSegmentSpans, Bool.and_eq_true]
    refine ⟨List.all_eq_true.mpr ?_, span⟩
    intro file member
    rcases List.mem_append.mp member with earlier | last
    · obtain ⟨segment, sealedMember, rfl⟩ := List.mem_map.mp earlier
      exact decide_eq_true (chain.startsWithin segment (List.mem_append_left _ sealedMember))
    · obtain rfl := List.mem_singleton.mp last
      exact decide_eq_true keeperWithin
  obtain ⟨bytes, rest, firstFile⟩ : ∃ bytes rest, files = (first, bytes) :: rest := by
    cases sealed with
    | nil => cases chain; exact ⟨_, [], rfl⟩
    | cons segment later => cases chain; exact ⟨_, _, rfl⟩
  have readBytes := (payloadBytes_of_chain sealed keeper tail).trans
    (congrArg (· ++ tail) chain.concatenate_eq)
  have route : recoverMarkedWalSegments base count files =
      WAL.Boundary.recoverRetainedMarked base first count (WAL.encode (history.drop first) ++ tail) := by
    have selection := recoverMarkedWalSegments_eq_retained base count first bytes rest ByteArray.empty aligned
      (by rw [← firstFile, through]; exact checked)
    rw [ByteArray.append_empty, ← firstFile, readBytes] at selection
    exact selection
  rw [show recoverMarkedWalSegments base count _ = _ from route]
  have byteCount : (WAL.encode history).size = count.toNat := by rw [absolute, WAL.encode_size, Nat.mul_comm]
  have countExact : count = (WAL.encode history).size.toUInt64 := by
    rw [byteCount]
    exact UInt64.ofNat_toNat.symm
  have chooses := WAL.Boundary.select_encoded history tail (byteCount ▸ count.toNat_lt_size)
  have exactFull : WAL.Boundary.recoverMarked base count (WAL.encode history ++ tail) =
      .ok (WAL.encode history, table) := by
    unfold WAL.Boundary.recoverMarked
    rw [← countExact] at chooses
    simp [chooses, fullReplay, Bind.bind, Except.bind, Pure.pure, Except.pure]
  let retired := history.take first
  have retiredLength : retired.length = first := by simp [retired, Nat.min_eq_left chain.start_le]
  have split : retired ++ history.drop first = history := List.take_append_drop ..
  obtain ⟨_, canonical⟩ := SnapshotWalReplay.fromEmpty history ordered
  obtain ⟨_, retiredReplay, _⟩ := (split.symm ▸ canonical).split
  have recovered := WAL.Boundary.recoverRetainedMarked_eq_recoverMarked base count
    (WAL.encode (history.drop first) ++ tail) (WAL.decodeOrdinals_encode retired retiredReplay.ordinals)
    (by simp) (retiredLength.symm ▸ covers) (by
      rw [WAL.encode_size, retiredLength, absolute, Nat.mul_comm frameSize]
      exact Nat.mul_le_mul_right _ chain.start_le)
  rw [retiredLength, ← ByteArray.append_assoc, ← WAL.encode_append, split, exactFull] at recovered
  cases resultEq : WAL.Boundary.recoverRetainedMarked base first count (WAL.encode (history.drop first) ++ tail) with
  | error error => rw [resultEq] at recovered; contradiction
  | ok result =>
    obtain ⟨selected, replayed⟩ := result
    rw [resultEq] at recovered
    have joined : (WAL.encode history, table) = (WAL.encode retired ++ selected, replayed) :=
      Except.ok.inj recovered
    have sameTable := congrArg Prod.snd joined
    have sameBytes := (ByteArray.append_right_inj _).mp
      ((congrArg Prod.fst joined).symm.trans (by rw [← WAL.encode_append, split]))
    exact congrArg Except.ok (Prod.ext sameBytes sameTable.symm)

end Alvoki.Storage
