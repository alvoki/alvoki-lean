import Alvoki.Storage.Disk.ManifestIntegrity

namespace Alvoki.Manifest

private def fnvStep (hash : UInt64) (byte : UInt8) : UInt64 :=
  (hash ^^^ byte.toUInt64) * 1099511628211

private theorem multiplyPrime_injective {left right : UInt64}
    (same : left * 1099511628211 = right * 1099511628211) : left = right := by
  -- The odd FNV multiplier has this inverse modulo 2^64.
  have inverse : (1099511628211 : UInt64) * 14886173955864302971 = 1 := by decide
  have restored := congrArg (fun hash : UInt64 => hash * 14886173955864302971) same
  simpa only [UInt64.mul_assoc, inverse, UInt64.mul_one] using restored

private theorem fnvStep_hash_injective {left right : UInt64} {byte : UInt8}
    (same : fnvStep left byte = fnvStep right byte) : left = right :=
  (UInt64.xor_left_inj byte.toUInt64).mp (multiplyPrime_injective same)

private theorem fnvStep_byte_injective {hash : UInt64} {left right : UInt8}
    (same : fnvStep hash left = fnvStep hash right) : left = right :=
  UInt8.toUInt64_inj.mp ((UInt64.xor_right_inj hash).mp (multiplyPrime_injective same))

private theorem fnvSuffix_injective (suffix : List UInt8) {left right : UInt64}
    (same : suffix.foldl fnvStep left = suffix.foldl fnvStep right) : left = right := by
  induction suffix generalizing left right with
  | nil => exact same
  | cons byte suffix ih => exact fnvStep_hash_injective (byte := byte) (ih same)

private theorem checksumRun_listFold (bytes : ByteArray) :
    checksumRun bytes = bytes.data.toList.foldl fnvStep 14695981039346656037 := by
  rw [Array.foldl_toList]
  let step : UInt64 → UInt8 → Id UInt64 := fun hash byte => pure (fnvStep hash byte)
  have loops (fuel index : Nat) (hash : UInt64) :
      ByteArray.foldlM.loop step bytes bytes.size (Nat.le_refl _) fuel index hash =
        Array.foldlM.loop step bytes.data bytes.size
          (by simpa only [ByteArray.size_data] using Nat.le_refl bytes.size) fuel index hash := by
    induction fuel generalizing index hash with
    | zero =>
      rw [ByteArray.foldlM.loop.eq_1, Array.foldlM.loop.eq_1]
    | succ fuel ih =>
      rw [ByteArray.foldlM.loop.eq_1, Array.foldlM.loop.eq_1]
      by_cases inBounds : index < bytes.size
      · simp only [dite_eq_left inBounds, ByteArray.getElem_eq_getElem_data]
        exact ih _ _
      · simp only [dite_eq_right inBounds]
  change bytes.foldl fnvStep 14695981039346656037 = bytes.data.foldl fnvStep 14695981039346656037
  unfold ByteArray.foldl Array.foldl ByteArray.foldlM Array.foldlM
  simp only [dite_eq_left (Nat.le_refl _), Nat.sub_zero]
  exact congrArg Id.run
    (by simpa only [step, ByteArray.size_data] using loops bytes.size 0 14695981039346656037)

/-- Substituting a different byte with the same prefix and suffix changes
the FNV-1a checksum. This includes a single flipped bit. -/
theorem checksumRun_ne_single_byte (head tail : ByteArray) {original changed : UInt8}
    (different : original ≠ changed) :
    checksumRun (head.push original ++ tail) ≠ checksumRun (head.push changed ++ tail) := by
  intro same
  simp only [checksumRun_listFold, ByteArray.data_append, ByteArray.data_push,
    Array.toList_append, Array.toList_push, List.foldl_append, List.foldl_cons, List.foldl_nil] at same
  exact different (fnvStep_byte_injective (fnvSuffix_injective tail.data.toList same))

/-- Replacing an in-bounds byte by a different value changes the checksum. -/
theorem checksumRun_ne_set {bytes : ByteArray} {index : Nat} (inBounds : index < bytes.size)
    {changed : UInt8} (different : bytes[index] ≠ changed) :
    checksumRun bytes ≠ checksumRun (bytes.set index changed inBounds) := by
  let original := bytes.data.toList
  have within : index < original.length := by simpa [original, ByteArray.size_data] using inBounds
  have headByte : original[index] = bytes[index] := by
    rw [ByteArray.getElem_eq_getElem_data]
    exact Array.getElem_toList within
  have split : original.take index ++ (bytes[index] :: original.drop (index + 1)) = original := by
    rw [← headByte, List.getElem_cons_drop within, List.take_append_drop]
  intro same
  simp only [checksumRun_listFold] at same
  change original.foldl fnvStep 14695981039346656037 =
    (bytes.data.set index changed (by simpa only [ByteArray.size_data] using inBounds)).toList.foldl
      fnvStep 14695981039346656037 at same
  rw [Array.toList_set, List.set_eq_take_append_cons_drop, ite_eq_left within] at same
  have folded := (congrArg (fun values => values.foldl fnvStep 14695981039346656037) split).trans same
  simp only [List.foldl_append, List.foldl_cons] at folded
  exact different (fnvStep_byte_injective (fnvSuffix_injective _ folded))

/-- Flipping any nonempty set of bits within one byte changes the checksum. -/
theorem checksumRun_ne_xor_byte {bytes : ByteArray} {index : Nat} (inBounds : index < bytes.size)
    {mask : UInt8} (nonzero : mask ≠ 0) :
    checksumRun bytes ≠ checksumRun (bytes.set index (bytes[index] ^^^ mask) inBounds) := by
  apply checksumRun_ne_set inBounds
  intro same
  have masks := (UInt8.xor_right_inj bytes[index]).mp (by simpa only [UInt8.xor_zero] using same :
    bytes[index] ^^^ (0 : UInt8) = bytes[index] ^^^ mask)
  exact nonzero masks.symm

/-- A run modified at just one byte fails validation against the integrity
manifest produced for its original bytes at the same index. -/
theorem IntegrityCheckpoint.rejects_single_byte {header : Checkpoint} {original observed : List ByteArray}
    {index : Nat} {head tail : ByteArray} {oldByte newByte : UInt8}
    (originalAt : original[index]? = some (head.push oldByte ++ tail))
    (observedAt : observed[index]? = some (head.push newByte ++ tail))
    (fits : (head.push oldByte ++ tail).size < UInt64.size) (different : oldByte ≠ newByte) :
    (IntegrityCheckpoint.fromRuns header original).validateRuns observed = false :=
  IntegrityCheckpoint.rejects_changed_run originalAt observedAt fits
    (Or.inr ((checksumRun_ne_single_byte head tail different).symm))

end Alvoki.Manifest
