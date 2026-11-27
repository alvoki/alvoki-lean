import Alvoki.Experiments.SSTable.Core
import Alvoki.Codec.ByteWords

namespace ImmutableSSTable

open Alvoki Alvoki.ByteWords

@[simp] theorem magic_size : magic.size = 8 := rfl

@[simp] theorem encodeHeader_size (rows : Nat) : (encodeHeader rows).size = headerSize := by
  simp [encodeHeader, pushWordFast_size, headerSize]

@[simp] theorem encodeEntry_size (row : Entry) : (encodeEntry row).size = rowSize := by
  simp [encodeEntry, pushWordFast_size, rowSize]
  rfl

/-- The format fits native signed offsets, including the final exclusive byte end. -/
theorem fileSize_bound (fits : count ≤ maxRows) : fileSize count < 2 ^ 63 := by
  unfold maxRows headerSize rowSize at fits
  unfold fileSize headerSize rowSize
  omega

theorem rowSpan (within : index < count) : rowOffset index + rowSize ≤ fileSize count := by
  unfold rowOffset fileSize headerSize rowSize
  omega

@[simp] theorem decodeHeader_encodeHeader (fits : count ≤ maxRows) :
    decodeHeader (encodeHeader count) = .ok count := by
  have magicBytes : (encodeHeader count).extract 0 8 = magic := by
    rw [encodeHeader, pushWordFast_append]
    apply ByteArray.extract_append_eq_left
    rfl
  have countWord : word (encodeHeader count) 8 = count.toUInt64 :=
    pushWordFast_roundtrip magic count.toUInt64
  have countNat : count.toUInt64.toNat = count := by
    change (UInt64.ofNat count).toNat = _
    apply UInt64.toNat_ofNat_of_lt'
    unfold maxRows headerSize rowSize at fits
    change count < 2 ^ 64
    omega
  simp [decodeHeader, magicBytes, countWord, countNat, fits, Pure.pure, Except.pure]

@[simp] theorem decodeEntry_encodeEntry (row : Entry) : decodeEntry (encodeEntry row) = .ok row := by
  let first := pushWordFast (ByteArray.emptyWithCapacity rowSize) row.key
  have firstSize : first.size = 8 := by
    simp [first, pushWordFast_size]
    rfl
  have key : word (encodeEntry row) 0 = row.key := by
    change word (pushWordFast first row.value) 0 = row.key
    rw [word_preserved _ _ _ (by omega)]
    exact pushWordFast_roundtrip _ _
  have value : word (encodeEntry row) 8 = row.value := by
    change word (pushWordFast first row.value) 8 = row.value
    rw [← firstSize]
    exact pushWordFast_roundtrip _ _
  simp [decodeEntry, key, value, Pure.pure, Except.pure]

@[simp] theorem encodeRows_cons (row : Entry) (rest : List Entry) :
    encodeRows (row :: rest) = encodeEntry row ++ encodeRows rest := by
  simp only [encodeRows, List.flatMap_cons, List.toByteArray_append]
  congr 1

@[simp] theorem encodeRows_size (rows : List Entry) : (encodeRows rows).size = rowSize * rows.length := by
  induction rows with
  | nil => simp [encodeRows]
  | cons row rest ih => simp [ih, Nat.mul_succ, Nat.add_comm]

@[simp] theorem encodeImage_size (rows : List Entry) : (encodeImage rows).size = fileSize rows.length := by
  simp [encodeImage, fileSize]

@[simp] theorem encodeImage_extract_header (rows : List Entry) :
    (encodeImage rows).extract 0 headerSize = encodeHeader rows.length := by
  unfold encodeImage
  apply ByteArray.extract_append_eq_left
  simp

private theorem encodeRows_extract (rows : List Entry) (index : Nat) (within : index < rows.length) :
    (encodeRows rows).extract (rowSize * index) (rowSize * index + rowSize) = encodeEntry rows[index] := by
  induction rows generalizing index with
  | nil => simp at within
  | cons row rest ih =>
    cases index with
    | zero =>
      rw [encodeRows_cons]
      simpa using (ByteArray.extract_append_eq_left (a := encodeEntry row) (b := encodeRows rest)
        (i := rowSize) (by simp : rowSize = (encodeEntry row).size))
    | succ index =>
      rw [encodeRows_cons]
      have start : rowSize * (index + 1) = (encodeEntry row).size + rowSize * index := by
        simp [Nat.mul_succ, Nat.add_comm]
      rw [start, Nat.add_assoc, ByteArray.extract_append_size_add]
      exact ih index (by simpa using within)

theorem encodeImage_extract_row (rows : List Entry) (index : Nat) (within : index < rows.length) :
    (encodeImage rows).extract (rowOffset index) (rowOffset index + rowSize) = encodeEntry rows[index] := by
  unfold encodeImage rowOffset fileSize
  rw [Nat.add_assoc, ByteArray.extract_append_size_add' (by simp : headerSize = (encodeHeader rows.length).size)]
  exact encodeRows_extract rows index within

end ImmutableSSTable
