import Alvoki.Experiments.SSTable.UnifiedFormat
import Alvoki.Experiments.SSTable.UnifiedIntegrity
import Alvoki.Codec.ByteWords

namespace ImmutableSSTable.Unified

open Alvoki Alvoki.ByteWords

@[simp] private theorem encodeOffset_size (n : Nat) : (encodeOffset n).size = 8 := by
  simp [encodeOffset, pushWordFast_size]

private theorem checksumFragment_size (n : Nat) :
    ((encodeOffset n).extract 0 checksumSize).size = checksumSize := by
  simp [checksumSize]

@[simp] theorem encodePacket_size (crc : Checksum) (tableId kind : UInt64) (offset : Nat)
    (bytes : ByteArray) : (encodePacket crc tableId kind offset bytes).size = bytes.size + checksumSize := by
  simp [encodePacket, checksumSize]

@[simp] theorem decodePacket_encodePacket (crc : Checksum) (tableId kind : UInt64) (offset : Nat)
    (bytes : ByteArray) : decodePacket crc tableId kind offset (encodePacket crc tableId kind offset bytes) =
      .ok bytes := by
  have payload : (encodePacket crc tableId kind offset bytes).extract 0 bytes.size = bytes := by
    unfold encodePacket
    exact ByteArray.extract_append_eq_left rfl
  unfold decodePacket
  simp only [encodePacket_size, Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel, payload]
  have suffix (n : Nat) :
      (bytes ++ (encodeOffset n).extract 0 checksumSize).extract bytes.size
        (bytes.size + checksumSize) = (encodeOffset n).extract 0 checksumSize :=
    ByteArray.extract_append_eq_right rfl (by rw [checksumFragment_size])
  simp [encodePacket, suffix, Pure.pure, Except.pure]

private theorem appendWords (initial : ByteArray) (words : List UInt64) :
    initial ++ encodeWords words = words.foldl pushWordFast initial := by
  induction words generalizing initial with
  | nil => simp [encodeWords]
  | cons field rest ih =>
    rw [encodeWords, ← ByteArray.append_assoc, ← pushWordFast_append, List.foldl_cons, ih]

private theorem extract_append_left {a b : ByteArray} {i j : Nat} (within : j ≤ a.size) :
    (a ++ b).extract i j = a.extract i j := by
  rw [ByteArray.extract_append]
  have empty : b.extract (i - a.size) (j - a.size) = ByteArray.empty := by
    exact ByteArray.extract_eq_empty_iff.mpr (by simp [Nat.sub_eq_zero_of_le within])
  rw [empty, ByteArray.append_empty]

private theorem toNat_word {n : Nat} (bound : n ≤ maxFileSize) : n.toUInt64.toNat = n :=
  UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt bound (by decide))

private theorem wordAppended (initial : ByteArray) (words : List UInt64) (i : Nat)
    (within : i < words.length) :
    word (initial ++ encodeWords words) (initial.size + 8 * i) = words[i] := by
  rw [word_right _ _ _ (by simp; omega)]
  exact word_encodeWords words i within

private def footerWords (footer : Footer) : List UInt64 :=
  [encodeWidth footer.layout.keyWidth, encodeWidth footer.layout.valueWidth,
    footer.layout.tableId, footer.count.toUInt64, footer.rootOffset.toUInt64, footer.rootSize.toUInt64]

private theorem encodeFooterBody_as_words (footer : Footer) :
    encodeFooterBody footer = magic ++ encodeWords (footerWords footer) := by
  rw [appendWords]
  rfl

theorem encodeFooterBody_magic (footer : Footer) :
    (encodeFooterBody footer).extract 0 8 = magic := by
  rw [encodeFooterBody_as_words]
  exact ByteArray.extract_append_eq_left rfl

@[simp] theorem encodeFooterBody_size (footer : Footer) :
    (encodeFooterBody footer).size = footerBodySize := by
  simp [encodeFooterBody_as_words, footerWords, footerBodySize, show magic.size = 8 from rfl]

/-- Local footer checks, excluding the reader's separate check against the file extent. -/
def Footer.Valid (footer : Footer) : Prop :=
  footer.layout.Valid ∧ footer.count ≤ maxFileSize ∧
    footer.rootOffset + footer.rootSize + footerBodySize ≤ maxFileSize ∧
    (if footer.count = 0 then footer.rootOffset = 0 ∧ footer.rootSize = 0 else 0 < footer.rootSize)

private theorem width_roundtrip (width : Option Nat) (bound : width.getD 0 ≤ maxRowSize) :
    decodeWidth (encodeWidth width) = width := by
  cases width with
  | none => rfl
  | some n =>
    change n ≤ maxRowSize at bound
    have natural : n.toUInt64.toNat = n := toNat_word (Nat.le_trans bound (by decide))
    have distinct : n.toUInt64 ≠ variableWidth := by
      intro same
      have limit := congrArg UInt64.toNat same
      rw [natural, show variableWidth.toNat = 18446744073709551615 from rfl] at limit
      have small : maxRowSize = 16777216 := rfl
      omega
    simp [encodeWidth, decodeWidth, distinct, natural]

@[simp] theorem decodeFooterBody_encodeFooterBody (footer : Footer) (valid : footer.Valid) :
    decodeFooterBody (encodeFooterBody footer) = .ok footer := by
  obtain ⟨layoutValid, countBound, extent, shape⟩ := valid
  have magicBytes : (encodeFooterBody footer).extract 0 8 = magic := by
    rw [encodeFooterBody_as_words]
    exact ByteArray.extract_append_eq_left rfl
  have field (i : Nat) (within : i < 6) :
      word (encodeFooterBody footer) (8 + 8 * i) = (footerWords footer)[i]'within := by
    rw [encodeFooterBody_as_words]
    exact wordAppended magic (footerWords footer) i within
  have keyWord : word (encodeFooterBody footer) 8 = encodeWidth footer.layout.keyWidth :=
    field 0 (by decide)
  have valueWord : word (encodeFooterBody footer) 16 = encodeWidth footer.layout.valueWidth :=
    field 1 (by decide)
  have idWord : word (encodeFooterBody footer) 24 = footer.layout.tableId := field 2 (by decide)
  have countWord : word (encodeFooterBody footer) 32 = footer.count.toUInt64 := field 3 (by decide)
  have rootWord : word (encodeFooterBody footer) 40 = footer.rootOffset.toUInt64 := field 4 (by decide)
  have sizeWord : word (encodeFooterBody footer) 48 = footer.rootSize.toUInt64 := field 5 (by decide)
  have keyBound : footer.layout.keyWidth.getD 0 ≤ maxRowSize := by
    unfold Layout.Valid at layoutValid
    omega
  have valueBound : footer.layout.valueWidth.getD 0 ≤ maxRowSize := by
    unfold Layout.Valid at layoutValid
    omega
  have offsetBound : footer.rootOffset ≤ maxFileSize := by omega
  have sizeBound : footer.rootSize ≤ maxFileSize := by omega
  have rebuilt : Layout.mk footer.layout.keyWidth footer.layout.valueWidth footer.layout.tableId =
      footer.layout := by cases footer.layout; rfl
  simp only [decodeFooterBody, encodeFooterBody_size, ↓reduceIte, magicBytes, beq_self_eq_true,
    keyWord, valueWord, idWord, countWord, rootWord, sizeWord, width_roundtrip _ keyBound,
    width_roundtrip _ valueBound, toNat_word countBound, toNat_word offsetBound, toNat_word sizeBound,
    rebuilt, layoutValid, countBound, extent, and_self]
  cases footer with
  | mk layout count rootOffset rootSize =>
    by_cases zero : count = 0
    · simp [zero] at shape
      simp [zero, shape, Pure.pure, Except.pure]
    · simp [zero] at shape
      simp [zero, shape, Pure.pure, Except.pure]

def Ref.Valid (ref : Ref) : Prop :=
  0 < ref.size ∧ ref.offset + ref.size ≤ maxFileSize ∧
    0 < ref.count ∧ ref.firstRow + ref.count ≤ maxFileSize

def Ref.Precedes (left right : Ref) : Prop :=
  left.lastKey < right.lastKey ∧ left.firstRow + left.count = right.firstRow ∧
    left.offset + left.size ≤ right.offset

/-- The reference checks local to a single index. The reader separately
checks the children's row and byte extents against their parent. -/
def ValidRefsAfter (prev : Option Ref) : List Ref → Prop
  | [] => True
  | ref :: rest => ref.Valid ∧ (∀ p ∈ prev, p.Precedes ref) ∧ ValidRefsAfter (some ref) rest

structure ValidRefs (refs : Array Ref) : Prop where
  nonempty : 0 < refs.size
  fits : (encodeIndex refs).size ≤ maxRowSize
  adjacent : ValidRefsAfter none refs.toList

theorem ValidRefsAfter.ref_valid (valid : ValidRefsAfter prev refs) (mem : ref ∈ refs) :
    ref.Valid := by
  induction refs generalizing prev with
  | nil => simp at mem
  | cons head rest ih =>
    rcases List.mem_cons.mp mem with rfl | inside
    · exact valid.1
    · exact ih valid.2.2 inside

theorem ValidRefs.ref_valid (valid : ValidRefs refs) (mem : ref ∈ refs.toList) : ref.Valid :=
  valid.adjacent.ref_valid mem

private def refWords (ref : Ref) : List UInt64 :=
  [ref.offset.toUInt64, ref.size.toUInt64, ref.firstRow.toUInt64, ref.count.toUInt64,
    ref.lastKey.size.toUInt64]

private def refBytes (ref : Ref) : ByteArray := encodeWords (refWords ref) ++ ref.lastKey

private def indexBytes : List Ref → ByteArray
  | [] => ByteArray.empty
  | ref :: rest => refBytes ref ++ indexBytes rest

private theorem appendRef_as_bytes (initial : ByteArray) (ref : Ref) :
    appendRef initial ref = initial ++ refBytes ref := by
  unfold refBytes
  rw [← ByteArray.append_assoc, appendWords]
  rfl

private theorem foldAppendRef (initial : ByteArray) (refs : List Ref) :
    refs.foldl appendRef initial = initial ++ indexBytes refs := by
  induction refs generalizing initial with
  | nil => simp [indexBytes]
  | cons ref rest ih =>
    rw [List.foldl_cons, ih, appendRef_as_bytes, ByteArray.append_assoc, indexBytes]

private theorem encodeIndex_as_bytes (refs : Array Ref) :
    encodeIndex refs = indexBytes refs.toList := by
  rw [encodeIndex, ← Array.foldl_toList, foldAppendRef, ByteArray.empty_append]

@[simp] private theorem refBytes_size (ref : Ref) : (refBytes ref).size = indexEntrySize ref.lastKey := by
  simp [refBytes, refWords, indexEntrySize, refPrefixSize]

private theorem indexBytes_size (refs : List Ref) :
    (indexBytes refs).size = (refs.map (fun ref => indexEntrySize ref.lastKey)).sum := by
  induction refs with
  | nil => simp [indexBytes]
  | cons ref rest ih => simp [indexBytes, ih]

theorem encodeIndex_size (refs : Array Ref) :
    (encodeIndex refs).size = (refs.toList.map (fun ref => indexEntrySize ref.lastKey)).sum := by
  rw [encodeIndex_as_bytes, indexBytes_size]

private theorem indexBytes_minSize (refs : List Ref) :
    refPrefixSize * refs.length ≤ (indexBytes refs).size := by
  induction refs with
  | nil => simp
  | cons ref rest ih =>
    simp only [indexBytes, ByteArray.size_append, refBytes_size, indexEntrySize,
      List.length_cons, refPrefixSize] at ih ⊢
    omega

private theorem wordRef (initial tail : ByteArray) (ref : Ref) (i : Nat) (inside : i < 5) :
    word (initial ++ (refBytes ref ++ tail)) (initial.size + 8 * i) = (refWords ref)[i]'inside := by
  have prefixSize : (encodeWords (refWords ref)).size = refPrefixSize := by simp [refWords, refPrefixSize]
  rw [word_right _ _ _ (by simp [indexEntrySize, refPrefixSize]; omega)]
  unfold refBytes
  rw [ByteArray.append_assoc, word_left _ _ _ (by rw [prefixSize]; unfold refPrefixSize; omega)]
  exact word_encodeWords (refWords ref) i inside

private theorem extractRefKey (initial tail : ByteArray) (ref : Ref) :
    (initial ++ (refBytes ref ++ tail)).extract (initial.size + refPrefixSize)
      (initial.size + refPrefixSize + ref.lastKey.size) = ref.lastKey := by
  rw [Nat.add_assoc, ByteArray.extract_append_size_add]
  rw [extract_append_left (by simp [indexEntrySize])]
  unfold refBytes
  exact ByteArray.extract_append_eq_right (by simp [refWords, refPrefixSize])
    (by simp [refWords, refPrefixSize])

private theorem decodeRefs_encoded (initial : ByteArray) (out : Array Ref) (remaining : List Ref)
    (fuel : Nat) (valid : ValidRefsAfter out.back? remaining) (enough : remaining.length ≤ fuel)
    (fits : (initial ++ indexBytes remaining).size ≤ maxFileSize) :
    decodeRefs (initial ++ indexBytes remaining) initial.size out fuel =
      .ok (out ++ remaining.toArray) := by
  induction remaining generalizing initial out fuel with
  | nil => cases fuel <;> simp [indexBytes, decodeRefs, Pure.pure, Except.pure]
  | cons ref rest ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      let bytes := initial ++ (refBytes ref ++ indexBytes rest)
      have extent : bytes.size = initial.size + (refPrefixSize + ref.lastKey.size) +
          (indexBytes rest).size := by simp [bytes, indexEntrySize, Nat.add_assoc]
      have room : initial.size + refPrefixSize ≤ bytes.size := by omega
      have atRef : initial.size ≠ bytes.size := by
        have positive : 0 < refPrefixSize := by decide
        omega
      have keyFits : ref.lastKey.size ≤ bytes.size - (initial.size + refPrefixSize) := by omega
      have byteBound : bytes.size ≤ maxFileSize := fits
      have keyBound : ref.lastKey.size ≤ maxFileSize := by omega
      obtain ⟨⟨sizePos, offsetSpan, countPos, rowSpan⟩, precedes, later⟩ := valid
      have offsetWord : (word bytes (initial.size + 0)).toNat = ref.offset := by
        rw [wordRef initial (indexBytes rest) ref 0 (by decide)]
        exact toNat_word (by omega)
      have sizeWord : (word bytes (initial.size + 8)).toNat = ref.size := by
        rw [wordRef initial (indexBytes rest) ref 1 (by decide)]
        exact toNat_word (by omega)
      have firstWord : (word bytes (initial.size + 16)).toNat = ref.firstRow := by
        rw [wordRef initial (indexBytes rest) ref 2 (by decide)]
        exact toNat_word (by omega)
      have countWord : (word bytes (initial.size + 24)).toNat = ref.count := by
        rw [wordRef initial (indexBytes rest) ref 3 (by decide)]
        exact toNat_word (by omega)
      have keyWord : (word bytes (initial.size + 32)).toNat = ref.lastKey.size := by
        rw [wordRef initial (indexBytes rest) ref 4 (by decide)]
        exact toNat_word keyBound
      have offsetWord := show (word bytes initial.size).toNat = ref.offset from by simpa using offsetWord
      have keyBytes : bytes.extract (initial.size + refPrefixSize)
          (initial.size + refPrefixSize + ref.lastKey.size) = ref.lastKey :=
        extractRefKey initial (indexBytes rest) ref
      have rebuilt : Ref.mk ref.lastKey ref.offset ref.size ref.firstRow ref.count = ref := by
        cases ref
        rfl
      have pushed : out.push ref ++ rest.toArray = out ++ (ref :: rest).toArray := by
        apply Array.toList_inj.mp
        simp
      have step := ih (initial ++ refBytes ref) (out.push ref) fuel
        (by simpa only [Array.back?_push] using later) (by simpa using enough)
        (by rw [ByteArray.append_assoc]; exact byteBound)
      rw [ByteArray.append_assoc, ByteArray.size_append, refBytes_size, indexEntrySize,
        ← Nat.add_assoc, pushed] at step
      change decodeRefs bytes initial.size out (fuel + 1) = _
      rw [decodeRefs]
      simp only [atRef, room, ↓reduceIte, offsetWord, sizeWord, firstWord, countWord, keyWord,
        sizePos, offsetSpan, countPos, rowSpan, keyFits, and_self, keyBytes, rebuilt]
      cases previous : out.back? with
      | none => exact step
      | some prev =>
        have p := precedes prev (Option.mem_def.mpr previous)
        change prev.lastKey < ref.lastKey ∧ prev.firstRow + prev.count = ref.firstRow ∧
          prev.offset + prev.size ≤ ref.offset at p
        simp only [p]
        exact step

theorem encodeIndex_minSize (refs : Array Ref) (nonempty : 0 < refs.size) :
    refPrefixSize ≤ (encodeIndex refs).size := by
  rw [encodeIndex_as_bytes]
  have count : 1 ≤ refs.toList.length := by simpa using Nat.succ_le_of_lt nonempty
  exact Nat.le_trans (by simpa using Nat.mul_le_mul_left refPrefixSize count)
    (indexBytes_minSize refs.toList)

theorem decodeRefs_encodeIndex (refs : Array Ref) (adjacent : ValidRefsAfter none refs.toList)
    (fits : (encodeIndex refs).size ≤ maxFileSize) :
    decodeRefs (encodeIndex refs) 0 #[] ((encodeIndex refs).size / refPrefixSize) = .ok refs := by
  rw [encodeIndex_as_bytes] at fits ⊢
  have fuel : refs.toList.length ≤ (indexBytes refs.toList).size / refPrefixSize := by
    exact (Nat.le_div_iff_mul_le (by decide)).mpr
      (by simpa [Nat.mul_comm] using indexBytes_minSize refs.toList)
  simpa using decodeRefs_encoded ByteArray.empty #[] refs.toList
    ((indexBytes refs.toList).size / refPrefixSize) adjacent fuel (by simpa using fits)

@[simp] theorem decodeIndex_encodeIndex (refs : Array Ref) (valid : ValidRefs refs) :
    decodeIndex (encodeIndex refs) = .ok refs := by
  simp only [decodeIndex, encodeIndex_minSize refs valid.nonempty, valid.fits, and_self, ↓reduceIte]
  exact decodeRefs_encodeIndex refs valid.adjacent (Nat.le_trans valid.fits (by decide))

end ImmutableSSTable.Unified
