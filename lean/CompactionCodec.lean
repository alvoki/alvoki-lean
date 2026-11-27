import Alvoki.Compaction.Core
import Alvoki.Codec.ByteWords

namespace Alvoki.Compaction
open Alvoki.ByteWords

abbrev RawEntry := Model.Entry (UInt64 × UInt64)

private def lane (row : RawEntry) : Nat → UInt64
  | 0 => row.key
  | 1 => row.sequence
  | 2 => row.payload.1
  | 3 => row.payload.2
  | _ => 0

def appendV3Row (out : ByteArray) (row : RawEntry) : ByteArray :=
  pushWordFast (pushWordFast (pushWordFast (pushWordFast out row.key)
    row.sequence) row.payload.1) row.payload.2

def encodeV3Row (row : RawEntry) : ByteArray := appendV3Row ByteArray.empty row

theorem appendV3Row_eq (out : ByteArray) (row : RawEntry) :
    appendV3Row out row = out ++ encodeV3Row row := by
  have pushAppend (a b : ByteArray) (value : UInt64) :
      pushWordFast (a ++ b) value = a ++ pushWordFast b value := by
    rw [pushWordFast_append (a ++ b), ByteArray.append_assoc, ← pushWordFast_append b]
  simp only [encodeV3Row, appendV3Row, pushWordFast_append out row.key, pushAppend]

@[simp] theorem encodeV3Row_size (row : RawEntry) : (encodeV3Row row).size = 32 := by
  simp only [encodeV3Row, appendV3Row, pushWordFast_size, ByteArray.size_empty]

private theorem encodeV3Row_lane (row : RawEntry) (l : Nat) (valid : l < 4) :
    word (encodeV3Row row) (8 * l) = lane row l := by
  rcases row with ⟨k, seq, tag, value⟩
  let a := pushWordFast ByteArray.empty k
  let b := pushWordFast a seq
  let c := pushWordFast b tag
  have aSize : a.size = 8 := by simp [a, pushWordFast_size]
  have bSize : b.size = 16 := by simp [b, pushWordFast_size, aSize]
  have cSize : c.size = 24 := by simp [c, pushWordFast_size, bSize]
  have aRead : word a 0 = k := pushWordFast_roundtrip ByteArray.empty k
  have bRead : word b 8 = seq := by
    rw [← aSize]
    exact pushWordFast_roundtrip a seq
  have cRead : word c 16 = tag := by
    rw [← bSize]
    exact pushWordFast_roundtrip b tag
  have dRead : word (pushWordFast c value) 24 = value := by
    rw [← cSize, pushWordFast_roundtrip]
  change word (pushWordFast c value) (8*l) = _
  have bounds : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 := by omega
  rcases bounds with rfl | rfl | rfl | rfl
  · change word (pushWordFast c value) 0 = k
    rw [word_preserved c value 0 (by omega),
      show word c 0 = word b 0 from word_preserved b tag 0 (by omega),
      show word b 0 = word a 0 from word_preserved a seq 0 (by omega), aRead]
  · change word (pushWordFast c value) 8 = seq
    rw [word_preserved c value 8 (by omega),
      show word c 8 = word b 8 from word_preserved b tag 8 (by omega), bRead]
  · change word (pushWordFast c value) 16 = tag
    rw [word_preserved c value 16 (by omega), cRead]
  · exact dRead

private theorem rawRow_lane (bytes : ByteArray) (i l : Nat) (valid : l < 4) :
    lane (rawRow bytes i) l = word bytes (16 + i * 32 + 8*l) := by
  have h : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl
  · rfl
  · exact congrArg (word bytes) (show 24 + i * 32 = 16 + i * 32 + 8 * 1 by omega)
  · exact congrArg (word bytes) (show 32 + i * 32 = 16 + i * 32 + 8 * 2 by omega)
  · exact congrArg (word bytes) (show 40 + i * 32 = 16 + i * 32 + 8 * 3 by omega)

def encodeV3Payload : List RawEntry → ByteArray
  | [] => ByteArray.empty
  | row :: rest => encodeV3Row row ++ encodeV3Payload rest

@[simp] theorem encodeV3Payload_size (rows : List RawEntry) :
    (encodeV3Payload rows).size = 32 * rows.length := by
  induction rows <;> simp only [encodeV3Payload, ByteArray.size_empty, ByteArray.size_append,
    encodeV3Row_size, List.length_cons, List.length_nil, *] <;> omega

private theorem encodeV3Payload_lane (rows : List RawEntry) (i l : Nat)
    (within : i < rows.length) (valid : l < 4) :
    word (encodeV3Payload rows) (i*32 + 8*l) = lane rows[i] l := by
  induction rows generalizing i with
  | nil => simp at within
  | cons row rows ih =>
    cases i with
    | zero =>
      simp only [encodeV3Payload, List.getElem_cons_zero, Nat.zero_mul, Nat.zero_add]
      have bound : 8*l + 7 < (encodeV3Row row).size := by simp; omega
      rw [word_left (encodeV3Row row) (encodeV3Payload rows) (8*l) bound,
        encodeV3Row_lane row l valid]
    | succ i =>
      have hit : i < rows.length := by simpa using within
      rw [encodeV3Payload, show (i+1)*32 + 8*l = (encodeV3Row row).size + (i*32 + 8*l) by
        rw [encodeV3Row_size]; omega]
      rw [word_right _ _ _ (by rw [encodeV3Payload_size]; omega)]
      exact ih i hit

def encodeV3Header (count : Nat) : ByteArray :=
  pushWordFast (pushWordFast ByteArray.empty count.toUInt64) 3

@[simp] theorem encodeV3Header_size (count : Nat) : (encodeV3Header count).size = 16 := rfl

def encodeV3 (rows : List RawEntry) : ByteArray :=
  encodeV3Header rows.length ++ encodeV3Payload rows

@[simp] theorem encodeV3_size (rows : List RawEntry) :
    (encodeV3 rows).size = 16 + 32 * rows.length := by
  simp [encodeV3, ByteArray.size_append]

theorem encodeV3_count (rows : List RawEntry) :
    word (encodeV3 rows) 0 = rows.length.toUInt64 := by
  rw [encodeV3, word_left _ _ _ (by rw [encodeV3Header_size]; decide), encodeV3Header,
    word_preserved _ _ _ (by simp [pushWordFast_size])]
  exact pushWordFast_roundtrip _ _

theorem encodeV3_version (rows : List RawEntry) :
    word (encodeV3 rows) 8 = 3 := by
  rw [encodeV3, word_left _ _ _ (by rw [encodeV3Header_size]; decide), encodeV3Header]
  exact pushWordFast_roundtrip _ _

private theorem encodeV3_lane (rows : List RawEntry) (i l : Nat)
    (within : i < rows.length) (valid : l < 4) :
    word (encodeV3 rows) (16 + i*32 + 8*l) = lane rows[i] l := by
  rw [encodeV3, show 16 + i*32 + 8*l = (encodeV3Header rows.length).size + (i*32 + 8*l) by
    rw [encodeV3Header_size]; omega, word_right _ _ _ (by rw [encodeV3Payload_size]; omega)]
  exact encodeV3Payload_lane rows i l within valid

@[simp] theorem rawRows_length (bytes : ByteArray) (count : Nat) :
    (rawRows bytes count).length = count := by simp [rawRows]

@[simp] theorem rawRows_get (bytes : ByteArray) (count i : Nat) (within : i < (rawRows bytes count).length) :
    (rawRows bytes count)[i] = rawRow bytes i := by
  simp [rawRows]

theorem rejects_short {bytes : ByteArray} (short : bytes.size < 16) :
    ¬ ∃ run, parse bytes = .ok run :=
  rejects_length (by omega)

theorem rejects_duplicate {bytes : ByteArray} {i j : Nat}
    (order : i < j) (within : j < (word bytes 0).toNat)
    (key : (rawRow bytes i).key = (rawRow bytes j).key)
    (sequence : (rawRow bytes i).sequence = (rawRow bytes j).sequence) :
    ¬ ∃ run, parse bytes = .ok run := by
  apply rejects_order
  intro ordered
  have h := List.pairwise_iff_getElem.mp ordered i j (by simp; omega) (by simpa using within) order
  simp [key, sequence] at h

theorem rejects_tag {bytes : ByteArray} {row : RawEntry}
    (present : row ∈ rawRows bytes (word bytes 0).toNat)
    (unknown : 1 < row.payload.1) :
    ¬ ∃ run, parse bytes = .ok run := by
  apply rejects_row present
  rintro (zero | ⟨one, _⟩)
  · have impossible : ¬ (1 : UInt64) < 0 := by decide
    exact impossible (zero ▸ unknown)
  · exact UInt64.lt_irrefl 1 (one ▸ unknown)

theorem rejects_tombstone_payload {bytes : ByteArray} {row : RawEntry}
    (present : row ∈ rawRows bytes (word bytes 0).toNat)
    (tombstone : row.payload.1 = 1) (nonzero : row.payload.2 ≠ 0) :
    ¬ ∃ run, parse bytes = .ok run := by
  apply rejects_row present
  simpa [CanonicalRow, tombstone] using nonzero

theorem rawRows_encodeV3 (rows : List RawEntry) :
    rawRows (encodeV3 rows) rows.length = rows := by
  apply List.ext_getElem (by simp)
  intro i _ within
  rw [rawRows_get]
  have read (l : Nat) (valid : l < 4) :=
    (rawRow_lane (encodeV3 rows) i l valid).trans (encodeV3_lane rows i l within valid)
  have key := read 0 (by decide)
  have seq := read 1 (by decide)
  have tag := read 2 (by decide)
  have value := read 3 (by decide)
  simp only [lane] at key seq tag value
  change word (encodeV3 rows) (16 + i*32) = _ at key
  change word (encodeV3 rows) (24 + i*32) = _ at seq
  change word (encodeV3 rows) (32 + i*32) = _ at tag
  change word (encodeV3 rows) (40 + i*32) = _ at value
  simp only [rawRow, key, seq, tag, value]

def Run.decodeV3 (run : Run) : List RawEntry :=
  rawRows run.bytes run.count.toNat

/-- A canonical ordered list, within both size bounds, parses and decodes exactly. -/
theorem encodeV3_roundtrip (rows : List RawEntry)
    (fits : 16 + 32 * rows.length < USize.size) (countFits : rows.length < UInt64.size)
    (ordered : Model.Ordered rows) (tags : ∀ row ∈ rows, CanonicalRow row) :
    ∃ run, parse (encodeV3 rows) = .ok run ∧ run.decodeV3 = rows := by
  have cardinal : (word (encodeV3 rows) 0).toNat = rows.length := by
    rw [encodeV3_count]
    exact UInt64.toNat_ofNat_of_lt countFits
  have valid : ValidV3 (encodeV3 rows) := by
    unfold ValidV3

    dsimp only
    rw [cardinal, rawRows_encodeV3, encodeV3_size, encodeV3_version]
    exact ⟨fits, rfl, rfl, ordered, tags⟩
  obtain ⟨run, accepted⟩ := (parse_iff _).mpr valid
  have h := parse_spec accepted
  refine ⟨run, accepted, ?_⟩
  rw [Run.decodeV3, h.1, h.2.1, cardinal, rawRows_encodeV3]

/-- A parser-accepted block re-encodes to exactly the original bytes. -/
theorem decodeV3_reencode {bytes : ByteArray} {run : Run} (accepted : parse bytes = .ok run) :
    encodeV3 run.decodeV3 = bytes := by
  have h := parse_spec accepted
  rw [Run.decodeV3, h.1, h.2.1]
  let n := (word bytes 0).toNat
  let rows := rawRows bytes n
  have count : rows.length = n := rawRows_length bytes n
  have size : bytes.size = 16 + 32 * n := h.2.2.2.2.1
  apply eq_of_aligned_words (by rw [encodeV3_size, rawRows_length, size])
  intro k within
  by_cases zero : k = 0
  · subst k
    rw [Nat.mul_zero, encodeV3_count, rawRows_length]
    exact UInt64.ofNat_toNat
  by_cases version : k = 1
  · subst k
    rw [Nat.mul_one, encodeV3_version]
    exact h.2.2.2.1.symm
  let i := (k - 2) / 4
  let l := (k - 2) % 4
  have row : i < rows.length := by rw [count]; dsimp [i]; omega
  have hit : l < 4 := Nat.mod_lt _ (by decide)
  have offset : 8*k = 16 + i*32 + 8*l := by dsimp [i, l]; omega
  rw [offset, encodeV3_lane rows i l row hit, rawRows_get, rawRow_lane bytes i l hit]

/-- A bounded stock slice contains the exact encoded row bytes. -/
theorem encodeV3Row_extract (run : Run) (i : Nat) (within : i < run.count.toNat) :
    encodeV3Row (rawRow run.bytes i) = run.bytes.extract (16 + i*32) (16 + i*32 + 32) := by
  have size := run.size_eq
  have stop : 16 + i * 32 + 32 ≤ run.bytes.size := by omega
  apply eq_of_aligned_words (by simp [ByteArray.size_extract, Nat.min_eq_left stop])
  intro k hit
  have small : k < 4 := by
    rw [ByteArray.size_extract, Nat.min_eq_left stop] at hit
    omega
  rw [word_extract _ _ _ _ (by omega) stop, encodeV3Row_lane _ _ small, rawRow_lane _ _ _ small]

end Alvoki.Compaction
