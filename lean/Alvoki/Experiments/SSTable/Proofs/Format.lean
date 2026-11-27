import Alvoki.Experiments.SSTable.Core
import Alvoki.Codec.ByteWords

namespace ImmutableSSTable

open Alvoki Alvoki.ByteWords

private theorem offset_toNat {n : Nat} (fits : n ≤ maxFileSize) :
    n.toUInt64.toNat = n := by
  apply UInt64.toNat_ofNat_of_lt'
  exact Nat.lt_of_le_of_lt fits (by decide)

private theorem extract_append_left {a b : ByteArray} {i j : Nat} (within : j ≤ a.size) :
    (a ++ b).extract i j = a.extract i j := by
  rw [ByteArray.extract_append]
  have empty : b.extract (i - a.size) (j - a.size) = ByteArray.empty := by
    simp [Nat.sub_eq_zero_of_le within]
  rw [empty, ByteArray.append_empty]

def rowPosition (start : Nat) (rows : List Entry) (index : Nat) : Nat :=
  start + (encodeRows (rows.take index)).size

@[simp] theorem encodeRows_cons (row : Entry) (rest : List Entry) :
    encodeRows (row :: rest) = encodeEntry row ++ encodeRows rest := rfl

@[simp] theorem rowPosition_zero (start : Nat) (rows : List Entry) :
    rowPosition start rows 0 = start := by
  simp [rowPosition, encodeRows]

private theorem rowPosition_cons (start : Nat) (row : Entry) (rest : List Entry) (index : Nat) :
    rowPosition start (row :: rest) (index + 1) =
      rowPosition (start + (encodeEntry row).size) rest index := by
  simp [rowPosition, Nat.add_assoc]

theorem rowPosition_succ (rows : List Entry) (within : i < rows.length) :
    rowPosition start rows (i + 1) = rowPosition start rows i + (encodeEntry rows[i]).size := by
  induction rows generalizing start i with
  | nil => simp at within
  | cons row rest ih =>
    cases i with
    | zero => simp [rowPosition_cons]
    | succ i =>
      rw [rowPosition_cons, rowPosition_cons]
      exact ih (by simpa using within)

private theorem rowPosition_le (start : Nat) (rows : List Entry) (index : Nat) :
    rowPosition start rows index ≤ start + (encodeRows rows).size := by
  induction rows generalizing start index with
  | nil => simp [rowPosition, encodeRows]
  | cons row rest ih =>
    cases index with
    | zero => simp
    | succ i =>
      rw [rowPosition_cons, encodeRows_cons, ByteArray.size_append, ← Nat.add_assoc]
      exact ih _ i

theorem rowPosition_bound (rows : List Entry) (index : Nat) :
    rowPosition 0 rows index ≤ (encodeRows rows).size := by
  simpa using rowPosition_le 0 rows index

private theorem encodeRows_extract (rows : List Entry) (within : i < rows.length) :
    (encodeRows rows).extract (rowPosition 0 rows i) (rowPosition 0 rows (i + 1)) =
      encodeEntry rows[i] := by
  induction rows generalizing i with
  | nil => simp at within
  | cons row rest ih =>
    cases i with
    | zero =>
      rw [rowPosition_zero, rowPosition_cons, rowPosition_zero, Nat.zero_add, encodeRows_cons]
      exact ByteArray.extract_append_eq_left rfl
    | succ i =>
      rw [encodeRows_cons, rowPosition_cons, rowPosition_cons, Nat.zero_add]
      simp only [rowPosition, Nat.zero_add] at ih ⊢
      rw [ByteArray.extract_append_size_add]
      exact ih (by simpa using within)

theorem encodeImage_extract_row (rows : List Entry) (within : i < rows.length) :
    (encodeImage rows).extract (rowPosition 0 rows i) (rowPosition 0 rows (i + 1)) =
      encodeEntry rows[i] := by
  unfold encodeImage
  rw [ByteArray.append_assoc, extract_append_left (rowPosition_bound rows _)]
  exact encodeRows_extract rows within

@[simp] theorem encodeOffset_size (n : Nat) : (encodeOffset n).size = 8 := by
  simp [encodeOffset, pushWordFast_size]

@[simp] theorem encodeEntry_size (row : Entry) : (encodeEntry row).size = entrySize row := by
  simp [encodeEntry, entrySize, pushWordFast_size, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem encodeEntry_min (row : Entry) : 16 ≤ (encodeEntry row).size := by
  simp [entrySize]

@[simp] theorem decodeEntry_encodeEntry (row : Entry) (fits : (encodeEntry row).size ≤ maxRowSize) :
    decodeEntry (encodeEntry row) = .ok row := by
  let payload := encodeOffset row.key.size ++ row.key ++ row.value
  have payloadSize : payload.size = 8 + row.key.size + row.value.size := by simp [payload]
  have rowSize : (encodeEntry row).size = payload.size + 8 := pushWordFast_size _ _
  have endPayload : (encodeEntry row).size - 8 = payload.size := by omega
  have keyFits : row.key.size ≤ maxFileSize := by
    unfold maxRowSize at fits
    unfold maxFileSize
    omega
  have keyWord : word (encodeEntry row) 0 = row.key.size.toUInt64 := by
    change word (pushWordFast payload (checksum payload)) 0 = _
    rw [word_preserved _ _ _ (by omega)]
    unfold payload
    rw [word_left _ _ _ (by simp; omega), word_left _ _ _ (by simp)]
    exact pushWordFast_roundtrip ByteArray.empty row.key.size.toUInt64
  have checkWord : word (encodeEntry row) payload.size = checksum payload :=
    pushWordFast_roundtrip _ _
  have payloadBytes : (encodeEntry row).extract 0 payload.size = payload := by
    change (pushWordFast payload (checksum payload)).extract 0 payload.size = payload
    rw [pushWordFast_append]
    exact ByteArray.extract_append_eq_left rfl
  have keyBytes : (encodeEntry row).extract 8 (8 + row.key.size) = row.key := by
    change (pushWordFast payload (checksum payload)).extract 8 (8 + row.key.size) = _
    rw [pushWordFast_append, extract_append_left (by omega)]
    unfold payload
    rw [extract_append_left (by simp)]
    exact ByteArray.extract_append_eq_right (by simp) (by simp)
  have valueBytes : (encodeEntry row).extract (8 + row.key.size) payload.size = row.value := by
    change (pushWordFast payload (checksum payload)).extract (8 + row.key.size) payload.size = _
    rw [pushWordFast_append, extract_append_left (by omega)]
    conv => lhs; unfold payload
    exact ByteArray.extract_append_eq_right (by simp) (by simp [ByteArray.size_append])
  have keyWithin : row.key.size ≤ (encodeEntry row).size - 16 := by omega
  have sizeWithin : 16 ≤ (encodeEntry row).size ∧ (encodeEntry row).size ≤ maxRowSize :=
    ⟨encodeEntry_min row, fits⟩
  simp only [decodeEntry, sizeWithin, ↓reduceIte, keyWord, offset_toNat keyFits, keyWithin,
    endPayload, checkWord, payloadBytes, keyBytes, valueBytes, Pure.pure,
    Except.pure]
  cases row <;> rfl

/-- Once its framing is valid, a row with a mismatched checksum is rejected. -/
theorem decodeEntry_rejects_checksum {bytes : ByteArray}
    (size : 16 ≤ bytes.size ∧ bytes.size ≤ maxRowSize)
    (keySize : (word bytes 0).toNat ≤ bytes.size - 16)
    (mismatch : word bytes (bytes.size - 8) ≠ checksum (bytes.extract 0 (bytes.size - 8))) :
    decodeEntry bytes = .error "invalid SSTable row checksum" := by
  simp [decodeEntry, size, keySize, mismatch]
  rfl

@[simp] theorem magic_size : magic.size = 8 := rfl

@[simp] theorem encodeFooter_size (count start : Nat) :
    (encodeFooter count start).size = footerSize := by
  simp [encodeFooter, footerSize, pushWordFast_size]

@[simp] theorem decodeFooter_encodeFooter {count start : Nat}
    (countFits : count ≤ maxFileSize) (startFits : start ≤ maxFileSize) :
    decodeFooter (encodeFooter count start) = .ok (count, start) := by
  let prefixBytes := pushWordFast magic count.toUInt64
  have prefixSize : prefixBytes.size = 16 := by simp [prefixBytes, pushWordFast_size]
  have magicBytes : (encodeFooter count start).extract 0 8 = magic := by
    unfold encodeFooter
    rw [pushWordFast_append, extract_append_left (by simp [pushWordFast_size]),
        pushWordFast_append]
    exact ByteArray.extract_append_eq_left magic_size.symm
  have countWord : word (encodeFooter count start) 8 = count.toUInt64 := by
    change word (pushWordFast prefixBytes start.toUInt64) 8 = _
    rw [word_preserved _ _ _ (by omega)]
    exact pushWordFast_roundtrip magic count.toUInt64
  have startWord : word (encodeFooter count start) 16 = start.toUInt64 := by
    change word (pushWordFast prefixBytes start.toUInt64) 16 = _
    rw [← prefixSize]
    exact pushWordFast_roundtrip _ _
  simp [decodeFooter, magicBytes, countWord, startWord, offset_toNat countFits,
    offset_toNat startFits, Pure.pure, Except.pure]

@[simp] theorem encodeOffsets_size (start : Nat) (rows : List Entry) :
    (encodeOffsets start rows).size = 8 * (rows.length + 1) := by
  induction rows generalizing start with
  | nil => simp [encodeOffsets]
  | cons row rest ih =>
    simp only [encodeOffsets, ByteArray.size_append, encodeOffset_size, ih, List.length_cons]
    omega

@[simp] theorem encodeImage_size (rows : List Entry) :
    (encodeImage rows).size = (encodeRows rows).size + 8 * (rows.length + 1) + footerSize := by
  simp [encodeImage]

theorem encodeImage_extract_footer (rows : List Entry) :
    (encodeImage rows).extract ((encodeImage rows).size - footerSize) (encodeImage rows).size =
      encodeFooter rows.length (encodeRows rows).size := by
  unfold encodeImage
  apply ByteArray.extract_append_eq_right
  · simp
  · simp only [ByteArray.size_append]

private theorem encodeOffsets_extract_pair (start : Nat) (rows : List Entry)
    (within : i < rows.length) :
    (encodeOffsets start rows).extract (8 * i) (8 * i + 16) =
      encodeOffset (rowPosition start rows i) ++ encodeOffset (rowPosition start rows (i + 1)) := by
  induction rows generalizing start i with
  | nil => simp at within
  | cons row rest ih =>
    cases i with
    | zero =>
      cases rest <;>
        simp only [Nat.mul_zero, Nat.zero_add, rowPosition_zero, rowPosition_cons, encodeOffsets]
      · have size : (encodeOffset start ++ encodeOffset (start + (encodeEntry row).size)).size = 16 := by simp
        rw [← size]
        exact ByteArray.extract_zero_size
      · rw [← ByteArray.append_assoc]
        exact ByteArray.extract_append_eq_left (by simp)
    | succ i =>
      have index : 8 * (i + 1) = (encodeOffset start).size + 8 * i := by
        simp [Nat.mul_succ, Nat.add_comm]
      rw [encodeOffsets, index, Nat.add_assoc, ByteArray.extract_append_size_add,
        rowPosition_cons, rowPosition_cons]
      exact ih _ (by simpa using within)

private theorem decodeOffsetPair_encode {a b : Nat} (ha : a ≤ maxFileSize) (hb : b ≤ maxFileSize) :
    decodeOffsetPair (encodeOffset a ++ encodeOffset b) = .ok (a, b) := by
  have leftWord : word (encodeOffset a ++ encodeOffset b) 0 = a.toUInt64 := by
    rw [word_left _ _ _ (by simp), encodeOffset]
    exact pushWordFast_roundtrip ByteArray.empty a.toUInt64
  have rightWord : word (encodeOffset a ++ encodeOffset b) 8 = b.toUInt64 := by
    calc
      _ = word (encodeOffset b) 0 := by
        simpa only [encodeOffset_size, Nat.add_zero] using
          word_right (encodeOffset a) (encodeOffset b) 0 (by simp)
      _ = _ := pushWordFast_roundtrip ByteArray.empty b.toUInt64
  simp [decodeOffsetPair, leftWord, rightWord, offset_toNat ha, offset_toNat hb,
    Pure.pure, Except.pure]

theorem decodeImage_offsets (rows : List Entry) (fits : Fits rows) (within : i < rows.length) :
    decodeOffsetPair ((encodeImage rows).extract ((encodeRows rows).size + 8 * i)
      ((encodeRows rows).size + 8 * i + 16)) =
      .ok (rowPosition 0 rows i, rowPosition 0 rows (i + 1)) := by
  have dataFits : (encodeRows rows).size ≤ maxFileSize := by
    have := fits.2
    omega
  have offsetFits : 8 * i + 16 ≤ (encodeOffsets 0 rows).size := by
    simp only [encodeOffsets_size]
    omega
  unfold encodeImage
  rw [ByteArray.append_assoc, Nat.add_assoc, ByteArray.extract_append_size_add,
    extract_append_left offsetFits, encodeOffsets_extract_pair 0 rows within]
  exact decodeOffsetPair_encode (Nat.le_trans (rowPosition_bound rows _) dataFits)
    (Nat.le_trans (rowPosition_bound rows _) dataFits)

end ImmutableSSTable
