import Alvoki.Storage.Disk.Proofs.WAL.WalSegmentMarkerRead
import Alvoki.Storage.Disk.Proofs.WAL.WalSegmentRepairEffects

namespace Alvoki.Storage

open WAL (frameSize)

private theorem WalSegmentSpans.replaceKeeperBytes {through keeper : Nat} {before after : ByteArray}
    (sealed : List (Nat × ByteArray)) (enough : (through - keeper) * frameSize ≤ after.size)
    (spans : WalSegmentSpans through (sealed ++ [(keeper, before)])) :
    WalSegmentSpans through (sealed ++ [(keeper, after)]) := by
  induction sealed with
  | nil => exact .active enough
  | cons file rest ih =>
    rcases file with ⟨first, bytes⟩
    cases rest with
    | nil =>
      cases spans with
      | sealed forward size old => exact .sealed forward size (.active enough)
    | cons file rest =>
      rcases file with ⟨next, nextBytes⟩
      cases spans with
      | sealed forward size old => exact .sealed forward size (ih old)

private theorem checkSelectedWalSegmentSpans_replaceKeeperBytes {through keeper : Nat} {before after : ByteArray}
    (sealed : List (Nat × ByteArray)) (enough : (through - keeper) * frameSize ≤ after.size)
    (checked : checkSelectedWalSegmentSpans through (sealed ++ [(keeper, before)]) = true) :
    checkSelectedWalSegmentSpans through (sealed ++ [(keeper, after)]) = true := by
  rw [checkSelectedWalSegmentSpans, Bool.and_eq_true] at checked
  obtain ⟨addresses, sizes⟩ := checked
  have sameAddresses : (sealed ++ [(keeper, after)]).all (fun file => decide (file.1 ≤ through)) = true := by
    simpa only [List.all_append, List.all_cons, List.all_nil] using addresses
  change (sealed ++ [(keeper, after)]).all (fun file => decide (file.1 ≤ through)) &&
    checkWalSegmentSpans through (sealed ++ [(keeper, after)]) = true
  rw [Bool.and_eq_true]
  refine ⟨sameAddresses, (checkWalSegmentSpans_iff ..).mpr ⟨?_, ?_⟩⟩
  · cases sealed with
    | nil =>
      exact ⟨_, _, rfl, by simpa using sameAddresses⟩
    | cons first rest =>
      exact ⟨_, _, rfl, decide_eq_true_eq.mp (List.all_eq_true.mp sameAddresses _ (List.mem_cons_self ..))⟩
  · exact ((checkWalSegmentSpans_iff ..).mp sizes).2.replaceKeeperBytes sealed enough

private theorem walSegmentPayloadBytes_appendKeeperTail (sealed : List (Nat × ByteArray))
    (keeper : Nat) (trimmed tail : ByteArray) :
    walSegmentPayloadBytes (sealed ++ [(keeper, trimmed ++ tail)]) =
      walSegmentPayloadBytes (sealed ++ [(keeper, trimmed)]) ++ tail := by
  induction sealed with
  | nil => simp [walSegmentPayloadBytes]
  | cons first rest ih =>
    change first.2 ++ walSegmentPayloadBytes (rest ++ [(keeper, trimmed ++ tail)]) =
      (first.2 ++ walSegmentPayloadBytes (rest ++ [(keeper, trimmed)])) ++ tail
    rw [ih, ByteArray.append_assoc]

private theorem recoverMarkedWalSegments_checked (base : PackedTable) (length : UInt64)
    (files : List (Nat × ByteArray)) (later : ByteArray) (alignment : length.toNat % frameSize = 0)
    (checked : checkSelectedWalSegmentSpans (length.toNat / frameSize) files = true) :
    recoverMarkedWalSegments base length files =
      WAL.Boundary.recoverRetainedMarked base ((files.head?.map Prod.fst).getD 0) length
        (walSegmentPayloadBytes files ++ later) := by
  cases files with
  | nil => simp [checkSelectedWalSegmentSpans, checkWalSegmentSpans] at checked
  | cons file rest =>
    exact recoverMarkedWalSegments_eq_retained base length file.1 file.2 rest later alignment checked

/-- The selected recovery bytes and table are identical after removing any
unchecked keeper tail. The same earlier files still pass the exact span
checks with the shortened keeper. -/
theorem recoverMarkedWalSegments_removeKeeperTail (base : PackedTable) (length : UInt64)
    (sealed : List (Nat × ByteArray)) (keeper : Nat) (trimmed tail : ByteArray)
    (alignment : length.toNat % frameSize = 0)
    (enough : (length.toNat / frameSize - keeper) * frameSize ≤ trimmed.size)
    (checked : checkSelectedWalSegmentSpans (length.toNat / frameSize) (sealed ++ [(keeper, trimmed ++ tail)]) = true) :
    recoverMarkedWalSegments base length (sealed ++ [(keeper, trimmed ++ tail)]) =
      recoverMarkedWalSegments base length (sealed ++ [(keeper, trimmed)]) := by
  have shorter := checkSelectedWalSegmentSpans_replaceKeeperBytes sealed enough checked
  rw [recoverMarkedWalSegments_checked _ _ _ ByteArray.empty alignment checked,
    recoverMarkedWalSegments_checked _ _ _ tail alignment shorter, ByteArray.append_empty,
    walSegmentPayloadBytes_appendKeeperTail]
  cases sealed <;> rfl

namespace WalSegmentRepair

/-- The strict replay gets exactly the same kept bytes and table on every
admitted keeper survivor. The selected checkpoint base and ordered
preceding reads are the same; later names supply no replay bytes. -/
theorem EffectTrace.replayUnchanged {target : Target} {initial after : FileImage} {plan : Plan}
    (trace : EffectTrace target initial after) (prepared : Prepared initial target plan)
    (base : PackedTable) (sealed : List (Nat × ByteArray))
    (sealedRead : ∀ file ∈ sealed, initial.kept file.1 = some file.2)
    {marker : ByteArray} {length : UInt64} (markerRead : target.pair.walBoundary = some marker)
    (decoded : WAL.Boundary.decode marker = .ok length)
    (checked : checkSelectedWalSegmentSpans (length.toNat / frameSize)
      (sealed ++ [(target.first, plan.keeperBytes)]) = true)
    {bytes : ByteArray} (survives : some bytes ∈ after.keeper.active :: after.keeper.crashImages) :
    recoverMarkedWalSegments base length (sealed ++ [(target.first, bytes)]) =
      recoverMarkedWalSegments base length (sealed ++ [(target.first, plan.keeperBytes)]) ∧
    ∀ file ∈ sealed, after.kept file.1 = some file.2 := by
  obtain ⟨_, _, stored, count, storedRead, storedDecoded, absolute⟩ :=
    DirectoryPublication.Bindings.walRange_accounting target.decoded
  have sameMarker := Option.some.inj (storedRead.symm.trans markerRead)
  subst stored
  have sameCount := Except.ok.inj (storedDecoded.symm.trans decoded)
  subst count
  have aligned : length.toNat % frameSize = 0 := by rw [absolute, Nat.mul_mod_left]
  have through : length.toNat / frameSize = target.range.through := by
    rw [absolute, Nat.mul_div_cancel _ (by decide : 0 < frameSize)]
  have enough : (length.toNat / frameSize - target.first) * frameSize ≤ target.trimmed.size := by
    simp [through, target.trimmedSize]
  obtain ⟨_, retained, ⟨newTail, exactBytes⟩, _⟩ :=
    trace.recoveryInputs prepared.pair prepared.keeperPrefix prepared.newer survives
  have oldRead := prepared.keeperPrefix.activeValid
  rw [prepared.keeperRead] at oldRead
  obtain ⟨oldTail, oldKeeper⟩ := oldRead
  have newKeeper := Option.some.inj exactBytes
  have oldKeeper := Option.some.inj oldKeeper
  have checkedLater : checkSelectedWalSegmentSpans (length.toNat / frameSize) (sealed ++ [(target.first, bytes)]) =
      true :=
    checkSelectedWalSegmentSpans_replaceKeeperBytes sealed
      (by rw [newKeeper, ByteArray.size_append]; exact Nat.le_trans enough (Nat.le_add_right ..)) checked
  rw [oldKeeper] at checked ⊢
  rw [newKeeper] at checkedLater ⊢
  refine ⟨?_, fun file listed => retained.symm ▸ sealedRead file listed⟩
  rw [recoverMarkedWalSegments_removeKeeperTail base length sealed target.first target.trimmed newTail aligned enough
    checkedLater, recoverMarkedWalSegments_removeKeeperTail base length sealed target.first target.trimmed oldTail
    aligned enough checked]

end WalSegmentRepair

end Alvoki.Storage
