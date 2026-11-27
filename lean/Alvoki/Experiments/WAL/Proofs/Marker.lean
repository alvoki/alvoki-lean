import Alvoki.Experiments.WAL.Recovery

namespace WalRecoverySlice

/-- The bounded cursor fields round-trip through the seven on-disk bytes. -/
theorem decodeMarker_encode (offset seq : Nat) (hs : seq < 256) (ho : offset < 65536)
    (empty : seq = 0 ↔ offset = 0) :
    decodeMarker (seq % 2) (encodeMarker offset seq) = .ok (some ⟨offset, seq⟩) := by
  have seqByte : seq.toUInt8.toNat = seq := by simp; omega
  have high : (offset / 256).toUInt8.toNat = offset / 256 := by simp; omega
  have low : (offset % 256).toUInt8.toNat = offset % 256 := by simp
  have combine : offset / 256 * 256 + offset % 256 = offset := by omega
  by_cases hz : seq = 0
  · have h := empty.mp hz
    simp [decodeMarker, encodeMarker, markerSize, hz, h] <;> rfl
  · have hp : offset > 0 := by omega
    simp [decodeMarker, encodeMarker, markerSize, seqByte, high, low, combine, hp, Nat.pos_of_ne_zero hz] <;> rfl

/-- An in-place partial overwrite may leave all seven bytes readable. A bad
check byte still excludes this slot, independently of the six field values. -/
theorem decodeMarker_bad_check (slot : Nat) (magic format gen seq hi lo check : UInt8)
    (bad : check ≠ (checksum [magic, format, gen, seq, hi, lo]).toUInt8) :
    decodeMarker slot [magic, format, gen, seq, hi, lo, check] = .ok none := by
  simp [decodeMarker, markerSize, bad] <;> rfl

/-- A detectable incomplete overwrite of the other slot preserves the valid cursor. -/
theorem selectMarker_one {a b : Bytes} {m : Marker}
    (reads : (decodeMarker 0 a = .ok (some m) ∧ decodeMarker 1 b = .ok none) ∨
             (decodeMarker 0 a = .ok none ∧ decodeMarker 1 b = .ok (some m))) :
    selectMarker a b = .ok m := by
  rcases reads with ⟨h, k⟩ | ⟨h, k⟩ <;> simp [selectMarker, h, k] <;> rfl

theorem selectMarker_both {a b : Bytes} {left right : Marker}
    (ha : decodeMarker 0 a = .ok (some left)) (hb : decodeMarker 1 b = .ok (some right)) :
    selectMarker a b = .ok (if left.lastSeq > right.lastSeq then left else right) := by
  simp [selectMarker, ha, hb] <;> rfl

end WalRecoverySlice
