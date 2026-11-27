import Alvoki.Experiments.SSTable.FixedFormat
import Alvoki.Codec.ByteWords

namespace ImmutableSSTable.Fixed

open Alvoki Alvoki.ByteWords

theorem Layout.blockReadSize_le (layout : Layout) (valid : layout.Valid) (rowCount block : Nat) :
    layout.blockReadSize rowCount block ≤ maxRowSize := by
  apply Nat.le_trans _ valid.2.2
  unfold Layout.blockReadSize Layout.blockSize
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.min_le_left _ _)) _

@[simp] theorem encodeRow_size (layout : Layout) (row : Entry) (fits : layout.RowFits row) :
    (encodeRow row).size = layout.rowWidth := by
  simp [encodeRow, Layout.rowWidth, fits.1, fits.2]

@[simp] theorem encodePayload_nil : encodePayload [] = ByteArray.empty := rfl

@[simp] theorem encodePayload_cons (row : Entry) (rows : List Entry) :
    encodePayload (row :: rows) = encodeRow row ++ encodePayload rows := rfl

@[simp] theorem encodePayload_append (left right : List Entry) :
    encodePayload (left ++ right) = encodePayload left ++ encodePayload right := by
  induction left with
  | nil => simp
  | cons row rest ih => simp [ih, ByteArray.append_assoc]

theorem encodePayload_size {layout : Layout} (rows : List Entry) (fits : ∀ row ∈ rows, layout.RowFits row) :
    (encodePayload rows).size = rows.length * layout.rowWidth := by
  induction rows with
  | nil => simp
  | cons row rest ih =>
    have rowFits := fits row (by simp)
    have restFits : ∀ r ∈ rest, layout.RowFits r := fun r hr => fits r (List.mem_cons_of_mem _ hr)
    simp [encodeRow_size layout row rowFits, ih restFits, Nat.succ_mul, Nat.add_comm]

private theorem extract_append_left {a b : ByteArray} {i j : Nat} (within : j ≤ a.size) :
    (a ++ b).extract i j = a.extract i j := by
  rw [ByteArray.extract_append]
  have empty : b.extract (i - a.size) (j - a.size) = ByteArray.empty := by
    simp [Nat.sub_eq_zero_of_le within]
  rw [empty, ByteArray.append_empty]

theorem readRow_encodePayload {layout : Layout} (rows : List Entry) (fits : ∀ row ∈ rows, layout.RowFits row)
    (within : i < rows.length) :
    readRow layout (encodePayload rows) i = rows[i] := by
  induction rows generalizing i with
  | nil => simp at within
  | cons row rest ih =>
    have rowFits := fits row (by simp)
    have width := encodeRow_size layout row rowFits
    cases i with
    | zero =>
      simp only [readRow, encodePayload_cons, Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
      have key : (encodeRow row ++ encodePayload rest).extract 0 layout.keyWidth = row.key := by
        rw [extract_append_left (by rw [width]; exact Nat.le_add_right _ _), encodeRow]
        exact ByteArray.extract_append_eq_left rowFits.1.symm
      have value : (encodeRow row ++ encodePayload rest).extract layout.keyWidth layout.rowWidth =
          row.value := by
        rw [extract_append_left (Nat.le_of_eq width.symm), encodeRow]
        exact ByteArray.extract_append_eq_right rowFits.1.symm (by simp [Layout.rowWidth, rowFits.1, rowFits.2])
      rw [key, value]
    | succ i =>
      have restFits : ∀ r ∈ rest, layout.RowFits r := fun r hr => fits r (List.mem_cons_of_mem _ hr)
      have index : (i + 1) * layout.rowWidth = (encodeRow row).size + i * layout.rowWidth := by
        rw [width, Nat.succ_mul, Nat.add_comm]
      simpa only [readRow, encodePayload_cons, index, Nat.add_assoc, ByteArray.extract_append_size_add,
        List.getElem_cons_succ] using ih restFits (by simpa using within)

@[simp] theorem encodeBlock_size (layout : Layout) (block : Nat) (payload : ByteArray) :
    (encodeBlock layout block payload).size = payload.size + 8 :=
  pushWordFast_size _ _

@[simp] theorem decodeBlock_encodeBlock (layout : Layout) (block rows : Nat) (payload : ByteArray)
    (size : payload.size = rows * layout.rowWidth) :
    decodeBlock layout block rows (encodeBlock layout block payload) = .ok payload := by
  have extracted : (encodeBlock layout block payload).extract 0 payload.size = payload := by
    rw [encodeBlock, pushWordFast_append]
    exact ByteArray.extract_append_eq_left rfl
  have check : word (encodeBlock layout block payload) payload.size =
      blockChecksum layout block payload :=
    pushWordFast_roundtrip _ _
  simp [decodeBlock, ← size, extracted, check, Pure.pure, Except.pure]

theorem decodeBlock_rejects_checksum (layout : Layout) (block rows : Nat) (bytes : ByteArray)
    (size : bytes.size = rows * layout.rowWidth + 8)
    (mismatch : word bytes (rows * layout.rowWidth) ≠
      blockChecksum layout block (bytes.extract 0 (rows * layout.rowWidth))) :
    decodeBlock layout block rows bytes = .error "invalid SSTable block checksum" := by
  simp [decodeBlock, size, mismatch]
  rfl

private theorem magic_size : magic.size = 8 := rfl

private def footerFields (layout : Layout) (rowCount : Nat) : List UInt64 :=
  [rowCount.toUInt64, layout.keyWidth.toUInt64, layout.valueWidth.toUInt64,
    layout.rowsPerBlock.toUInt64, layout.tableId]

private theorem footerFields_length (layout : Layout) (rowCount : Nat) :
    (footerFields layout rowCount).length = 5 := rfl

private theorem append_encodeWords (prefixBytes : ByteArray) (words : List UInt64) :
    prefixBytes ++ encodeWords words = words.foldl pushWordFast prefixBytes := by
  induction words generalizing prefixBytes with
  | nil => simp [encodeWords]
  | cons field rest ih =>
    rw [encodeWords, ← ByteArray.append_assoc, ← pushWordFast_append, List.foldl_cons, ih]

private theorem encodeFooter_metadata (layout : Layout) (rowCount : Nat) :
    encodeFooter layout rowCount =
      let metadata := magic ++ encodeWords (footerFields layout rowCount)
      pushWordFast metadata (checksum metadata) := by
  rw [append_encodeWords]
  rfl

@[simp] theorem encodeFooter_size (layout : Layout) (rowCount : Nat) :
    (encodeFooter layout rowCount).size = footerSize := by
  rw [encodeFooter_metadata]
  simp [footerSize, pushWordFast_size, magic_size, footerFields_length]

private theorem toNat_word {n : Nat} (bound : n ≤ maxFileSize) : n.toUInt64.toNat = n :=
  UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt bound (by decide))

@[simp] theorem decodeFooter_encodeFooter (layout : Layout) (rowCount : Nat)
    (fits : layout.Fits rowCount) :
    decodeFooter (encodeFooter layout rowCount) = .ok (layout, rowCount) := by
  let metadata := magic ++ encodeWords (footerFields layout rowCount)
  have metadataSize : metadata.size = 48 := by
    simp [metadata, magic_size, footerFields_length]
  have encoded : encodeFooter layout rowCount = pushWordFast metadata (checksum metadata) :=
    encodeFooter_metadata layout rowCount
  have magicBytes : (encodeFooter layout rowCount).extract 0 8 = magic := by
    rw [encoded, pushWordFast_append, extract_append_left (by rw [metadataSize]; decide)]
    exact ByteArray.extract_append_eq_left magic_size.symm
  have metadataBytes : (encodeFooter layout rowCount).extract 0 48 = metadata := by
    rw [encoded, pushWordFast_append]
    exact ByteArray.extract_append_eq_left metadataSize.symm
  have check : word (encodeFooter layout rowCount) 48 = checksum metadata := by
    rw [encoded, ← metadataSize]
    exact pushWordFast_roundtrip _ _
  have field (i : Nat) (within : i < 5) :
      word (encodeFooter layout rowCount) (8 + 8 * i) =
        (footerFields layout rowCount)[i]'(by rwa [footerFields_length]) := by
    rw [encoded, word_preserved _ _ _ (by rw [metadataSize]; omega)]
    unfold metadata
    have position : 8 + 8 * i = magic.size + 8 * i := by rw [magic_size]
    rw [position, word_right _ _ _ (by simp [footerFields_length]; omega)]
    exact word_encodeWords _ _ _
  have keyWord : word (encodeFooter layout rowCount) 16 = layout.keyWidth.toUInt64 := field 1 (by decide)
  have valueWord : word (encodeFooter layout rowCount) 24 = layout.valueWidth.toUInt64 := field 2 (by decide)
  have rowsWord : word (encodeFooter layout rowCount) 32 = layout.rowsPerBlock.toUInt64 := field 3 (by decide)
  have idWord : word (encodeFooter layout rowCount) 40 = layout.tableId := field 4 (by decide)
  have countWord : word (encodeFooter layout rowCount) 8 = rowCount.toUInt64 := field 0 (by decide)
  have widthBound : layout.rowWidth ≤ maxRowSize := by
    have width := Nat.le_mul_of_pos_left layout.rowWidth fits.1.1
    have block := fits.1.2.2
    unfold Layout.blockSize at block
    omega
  have sizeBound : maxRowSize ≤ maxFileSize := by decide
  have keyNat := toNat_word (Nat.le_trans (Nat.le_add_right layout.keyWidth layout.valueWidth)
    (Nat.le_trans widthBound sizeBound))
  have valueNat := toNat_word (Nat.le_trans (Nat.le_add_left layout.valueWidth layout.keyWidth)
    (Nat.le_trans widthBound sizeBound))
  have rowsNat := toNat_word (Nat.le_trans fits.1.2.1 sizeBound)
  have rebuilt : Layout.mk layout.keyWidth layout.valueWidth layout.rowsPerBlock layout.tableId =
      layout := by cases layout; rfl
  simp [decodeFooter, magicBytes, check, metadataBytes, countWord, keyWord, valueWord, rowsWord,
    idWord, toNat_word fits.2.1, keyNat, valueNat, rowsNat, rebuilt, fits, Pure.pure, Except.pure]

theorem decodeFooter_rejects_checksum (bytes : ByteArray) (size : bytes.size = footerSize)
    (hasMagic : bytes.extract 0 8 = magic)
    (mismatch : word bytes 48 ≠ checksum (bytes.extract 0 48)) :
    decodeFooter bytes = .error "invalid SSTable fixed footer checksum" := by
  simp [decodeFooter, size, hasMagic, mismatch]
  rfl

end ImmutableSSTable.Fixed
