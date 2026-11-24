import Alvoki.Storage.Disk.RetainedWalReplay
import Alvoki.Storage.Disk.RetainedWalSuffix

namespace Alvoki.WAL.Boundary

private theorem retainedCountToNat (length : UInt64) (removedThrough : Nat) :
    (length.toNat - removedThrough * frameSize).toUInt64.toNat =
      length.toNat - removedThrough * frameSize :=
  UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (Nat.sub_le ..) length.toNat_lt_size)

/-- When the marker covers the removed bytes, physical selection is the
same as full-WAL selection with that prefix accounted for. This includes
the original alignment and short-file errors. -/
theorem selectRetained_eq_select {removedThrough : Nat} {removed : ByteArray}
    (length : UInt64) (retained : ByteArray)
    (complete : removed.size = removedThrough * frameSize)
    (covers : removed.size ≤ length.toNat) :
    select length (removed ++ retained) =
      (selectRetained removedThrough length retained).map (removed ++ ·) := by
  let count := length.toNat - removedThrough * frameSize
  have start : removedThrough * frameSize ≤ length.toNat := complete ▸ covers
  have shifted : length.toNat = removed.size + count := by
    dsimp [count]
    omega
  have aligned : length.toNat % frameSize = count % frameSize := by
    rw [shifted, complete, Nat.add_comm, Nat.add_mul_mod_self_right]
  have short : (removed ++ retained).size < length.toNat ↔ retained.size < count := by
    rw [ByteArray.size_append, shifted]
    omega
  have whole : (removed ++ retained).size = length.toNat ↔ retained.size = count := by
    rw [ByteArray.size_append, shifted]
    omega
  have removedExtract : removed.extract 0 length.toNat = removed := by
    simpa only [Nat.max_eq_left covers] using
      (ByteArray.extract_zero_max_size (a := removed) (i := length.toNat))
  have extracted : (removed ++ retained).extract 0 length.toNat =
      removed ++ retained.extract 0 count := by
    rw [ByteArray.extract_append, removedExtract, Nat.zero_sub, shifted, Nat.add_sub_cancel_left]
  unfold selectRetained select
  simp only [Nat.not_lt.mpr start, ↓reduceIte, retainedCountToNat, aligned, short, whole]
  by_cases isAligned : count % frameSize = 0
  · by_cases tooShort : retained.size < count
    · simp [count, isAligned, tooShort, Except.map]
    · by_cases exactSize : retained.size = count
      · simp [count, isAligned, exactSize, Except.map]
      · simp [count, isAligned, tooShort, exactSize, extracted, Except.map]
  · simp [count, isAligned, Except.map]

theorem selectRetained_absoluteSize {removedThrough : Nat} {length : UInt64} {retained selected : ByteArray}
    (accepted : selectRetained removedThrough length retained = .ok selected) :
    removedThrough * frameSize + selected.size = length.toNat := by
  by_cases beforeCutoff : length.toNat < removedThrough * frameSize
  · simp [selectRetained, beforeCutoff] at accepted
  · have chosen : select (length.toNat - removedThrough * frameSize).toUInt64 retained = .ok selected := by
      simpa [selectRetained, beforeCutoff] using accepted
    have size := select_size chosen
    rw [retainedCountToNat] at size
    omega

/-- Repair through one physical cut keeps all decisions by an earlier
absolute marker. This includes markers rejected for preceding the retained
bytes as well as markers inside them. -/
theorem selectRetained_shorter_after_trim {removedThrough : Nat} {shorter length : UInt64}
    {retained trimmed : ByteArray}
    (trim : selectRetained removedThrough length retained = .ok trimmed)
    (bounded : shorter.toNat ≤ length.toNat) :
    selectRetained removedThrough shorter trimmed = selectRetained removedThrough shorter retained := by
  by_cases beforeCutoff : shorter.toNat < removedThrough * frameSize
  · simp [selectRetained, beforeCutoff]
  · have longerCovers : ¬ length.toNat < removedThrough * frameSize := by omega
    simp only [selectRetained, beforeCutoff, longerCovers, ↓reduceIte] at trim ⊢
    apply select_shorter_after_trim trim
    rw [retainedCountToNat, retainedCountToNat]
    exact Nat.sub_le_sub_right bounded _

/-- With a known validated removed prefix, the retained recovery worker
makes the same selection and table decision as the full marked worker.
On success the physical repair bytes are exactly the retained part of the
old worker's selected bytes. The marker must cover the retired prefix. -/
theorem recoverRetainedMarked_eq_recoverMarked (base : Storage.PackedTable)
    {removed : List Write} {retired : ByteArray} (length : UInt64) (retained : ByteArray)
    (validated : decodeOrdinals retired = .ok removed)
    (aligned : retired.size % frameSize = 0) (covered : removed.length ≤ base.committed.toNat)
    (markerCovers : retired.size ≤ length.toNat) :
    recoverMarked base length (retired ++ retained) =
      (recoverRetainedMarked base removed.length length retained).map
        (fun (selected, table) => (retired ++ selected, table)) := by
  have whole : retired.size / frameSize * frameSize = retired.size := by
    have bytes := Nat.mod_add_div retired.size frameSize
    simpa [aligned, Nat.mul_comm] using bytes
  have prefixExact := decodeOrdinals_reencode validated
  rw [whole, ByteArray.extract_zero_size] at prefixExact
  have complete : retired.size = removed.length * frameSize := by
    rw [← prefixExact, WAL.encode_size]
    exact Nat.mul_comm ..
  unfold recoverMarked recoverRetainedMarked
  rw [selectRetained_eq_select length retained complete markerCovers]
  cases selected : selectRetained removed.length length retained with
  | error => rfl
  | ok bytes =>
    have replayed := Storage.recoverRetainedFrom_eq_recoverSelected base bytes validated aligned covered
    change (do
      let table ← Storage.recoverSelected base (retired ++ bytes)
      return (retired ++ bytes, table)) =
      (do
        let table ← Storage.recoverRetainedFrom base removed.length bytes
        pure (bytes, table)).map (fun (selected, table) => (retired ++ selected, table))
    rw [← replayed]
    cases Storage.recoverRetainedFrom base removed.length bytes <;> rfl

end Alvoki.WAL.Boundary
