import PackedRun
import ByteWords

namespace Alvoki.Packed
open Alvoki.Opt Alvoki.ByteWords

@[inline] private def putRecord (out : ByteArray) (row : Record) : ByteArray :=
  pushWordFast (pushWordFast out row.1) row.2

/-- Encode the v1 count, version and payload. Parse acceptance requires strict key order. -/
def encodeV1 (records : @& Array Record) : ByteArray :=
  records.foldl putRecord
    (pushWordFast (pushWordFast (ByteArray.emptyWithCapacity (16 + 16 * records.size))
      records.size.toUInt64) 1)

def Run.decodeV1 (run : @& Run) : Array Record :=
  Array.ofFn fun i : Fin run.count.toNat => run.view.logicalRecord i.val

def encodeV1Payload : List Record → ByteArray
  | [] => ByteArray.empty
  | row :: rest => putRecord ByteArray.empty row ++ encodeV1Payload rest

private theorem encodeV1Payload_size (rows : List Record) : (encodeV1Payload rows).size = 16 * rows.length := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [encodeV1Payload, ByteArray.size_append, putRecord, pushWordFast_size, ByteArray.size_empty, ih, List.length_cons]
    omega

private theorem foldRecords (rows : List Record) (out : ByteArray) :
    rows.foldl putRecord out = out ++ encodeV1Payload rows := by
  induction rows generalizing out with
  | nil => simp [encodeV1Payload]
  | cons row rest ih =>
    rw [List.foldl_cons, ih, encodeV1Payload]
    have append : putRecord out row = out ++ putRecord ByteArray.empty row := by
      rw [putRecord, putRecord, pushWordFast_append (pushWordFast out row.1),
        pushWordFast_append out, ByteArray.append_assoc, ← pushWordFast_append]
    rw [append, ByteArray.append_assoc]

private theorem encodeV1Payload_word (rows : List Record) (i : Nat) (hit : i < rows.length) :
    word (encodeV1Payload rows) (16 * i) = rows[i].1 ∧
      word (encodeV1Payload rows) (16 * i + 8) = rows[i].2 := by
  induction rows generalizing i with
  | nil => simp at hit
  | cons row rest ih =>
    let block := putRecord ByteArray.empty row
    have size : block.size = 16 := rfl
    cases i with
    | zero =>
      refine ⟨?_, ?_⟩
      · change word (block ++ encodeV1Payload rest) 0 = row.1
        rw [word_left _ _ _ (by rw [size]; decide)]
        unfold block putRecord
        rw [word_preserved _ _ _ (by rw [pushWordFast_size]; omega)]
        exact pushWordFast_roundtrip ByteArray.empty row.1
      · change word (block ++ encodeV1Payload rest) 8 = row.2
        rw [word_left _ _ _ (by rw [size]; decide)]
        exact pushWordFast_roundtrip (pushWordFast ByteArray.empty row.1) row.2
    | succ i =>
      have bound : i < rest.length := by simp only [List.length_cons] at hit; omega
      have suffixSize := encodeV1Payload_size rest
      have key := word_right block (encodeV1Payload rest) (16 * i) (by omega)
      have value := word_right block (encodeV1Payload rest) (16 * i + 8) (by omega)
      have offset : 16 + 16 * i = 16 * (i + 1) := by omega
      have valueOffset : 16 + (16 * i + 8) = 16 * (i + 1) + 8 := by omega
      rw [size, offset] at key
      rw [size, valueOffset] at value
      exact ⟨key.trans (ih i bound).1, value.trans (ih i bound).2⟩

private def header (n : Nat) : ByteArray :=
  pushWordFast (pushWordFast (ByteArray.emptyWithCapacity (16 + 16 * n)) n.toUInt64) 1

private theorem encodeV1_split (records : Array Record) :
    encodeV1 records = header records.size ++ encodeV1Payload records.toList := by
  unfold encodeV1 header
  rw [← Array.foldl_toList, foldRecords]

theorem encodeV1_parts (records : Array Record) :
    encodeV1 records = pushWordFast ByteArray.empty records.size.toUInt64 ++
      pushWordFast ByteArray.empty 1 ++ encodeV1Payload records.toList := by
  rw [encodeV1_split]
  rfl

theorem encodeV1_size (records : Array Record) :
    (encodeV1 records).size = 16 + 16 * records.size := by
  rw [encodeV1_split, ByteArray.size_append, encodeV1Payload_size, Array.length_toList]
  rfl

private theorem encodeV1_keys (records : Array Record) (i : Nat) (hit : i < records.size) :
    word (encodeV1 records) (16 + i * 16) = records[i].1 ∧
      word (encodeV1 records) (24 + i * 16) = records[i].2 := by
  rw [encodeV1_split]
  have hsize : (header records.size).size = 16 := rfl
  have payload := encodeV1Payload_size records.toList
  rw [Array.length_toList] at payload
  have key := word_right (header records.size) (encodeV1Payload records.toList) (16 * i) (by omega)
  have value := word_right (header records.size) (encodeV1Payload records.toList) (16 * i + 8) (by omega)
  rw [hsize, show 16 + 16*i = 16 + i*16 by omega] at key
  rw [hsize, show 16 + (16*i + 8) = 24 + i*16 by omega] at value
  have hit' : i < records.toList.length := by simpa using hit
  have row := encodeV1Payload_word records.toList i hit'
  exact ⟨key.trans (by simpa using row.1), value.trans (by simpa using row.2)⟩

private theorem encodeV1_version (records : Array Record) : word (encodeV1 records) 8 = 1 := by
  have headerSize : (header records.size).size = 16 := rfl
  rw [encodeV1_split, word_left _ _ _ (by rw [headerSize]; decide)]
  exact pushWordFast_roundtrip _ 1

private theorem encodeV1_count (records : Array Record) :
    word (encodeV1 records) 0 = records.size.toUInt64 := by
  have headerSize : (header records.size).size = 16 := rfl
  rw [encodeV1_split, word_left _ _ _ (by rw [headerSize]; decide)]
  unfold header
  rw [word_preserved _ _ _ (by rw [pushWordFast_size]; omega)]
  exact pushWordFast_roundtrip _ _

/-- The executable v1 parser accepts the complete encoding and decodes all rows exactly. -/
theorem encodeV1_roundtrip (records : Array Record)
    (width : 16 + 16 * records.size < USize.size)
    (countFits : records.size < UInt64.size)
    (ordered : ∀ i j : Nat, (less : i < j) → (hit : j < records.size) →
      (records[i]'(by omega)).1 < records[j].1) :
    ∃ run, parseRun (encodeV1 records) = .ok run ∧ run.decodeV1 = records := by
  let bytes := encodeV1 records
  have size : bytes.size = 16 + 16 * records.size := encodeV1_size records
  have fits : bytes.size < USize.size := by omega
  have version : word bytes 8 = 1 := encodeV1_version records
  have countField : (word bytes 0).toNat = records.size := by
    change (word (encodeV1 records) 0).toNat = _
    rw [encodeV1_count]
    exact UInt64.toNat_ofNat_of_lt countFits
  obtain ⟨view, parsed, cardinal⟩ := parseView_v1_complete bytes records.size size fits version countField
    (fun view byteEq cardinal stride values => view.validate_complete fun i j ij jHit => by
      have bound := USize.lt_iff_toNat_lt.mp jHit
      have less := USize.lt_iff_toNat_lt.mp ij
      have iHit := USize.lt_trans ij jHit
      rw [view.key_eq iHit, view.key_eq jHit]
      unfold View.logicalRecord
      dsimp only
      rw [byteEq, stride, (encodeV1_keys records i.toNat (by omega)).1,
        (encodeV1_keys records j.toNat (by omega)).1]
      exact ordered i.toNat j.toNat less (by omega))
  obtain ⟨run, accepted, same⟩ := parseRun_of_view parsed version
  refine ⟨run, accepted, ?_⟩
  have header := parseView_spec parsed
  have layout : view.stride.toNat = 16 ∧ view.values.toNat = 24 := by
    rcases header.2.2.2 with h | h
    · exact h.2
    · simp [version] at h
  apply Array.ext
  · simp [Run.decodeV1, Run.count, same, cardinal]
  · intro i hRun hRecords
    have words := encodeV1_keys records i hRecords
    simp only [Run.decodeV1, Array.getElem_ofFn, View.logicalRecord, Run.count, same, header.1,
      layout.1, layout.2]
    exact Prod.ext words.1 words.2

/-- Every accepted v1 byte string re-encodes byte for byte. -/
theorem decodeV1_reencode {bytes : ByteArray} {run : Run} (accepted : parseRun bytes = .ok run) :
    encodeV1 run.decodeV1 = bytes := by
  obtain ⟨parsed, version⟩ := parseRun_spec accepted
  have source := parseView_spec parsed
  have size := run.view.size_eq
  rw [source.1] at size
  have cardinal : run.decodeV1.size = run.view.count.toNat := by
    simp [Run.decodeV1, Run.count]
  have outputSize : (encodeV1 run.decodeV1).size = bytes.size := by
    rw [encodeV1_size, cardinal, size]
  have aligned (k : Nat) (hit : 8 * k < bytes.size) :
      word (encodeV1 run.decodeV1) (8 * k) = word bytes (8 * k) := by
    by_cases countWord : k = 0
    · subst k
      rw [Nat.mul_zero, encodeV1_count, cardinal, ← source.2.1]
      exact UInt64.ofNat_toNat
    · by_cases versionWord : k = 1
      · subst k
        rw [Nat.mul_one, encodeV1_version, version]
      · let i := (k - 2) / 2
        have within : i < run.decodeV1.size := by rw [cardinal]; dsimp [i]; omega
        have w := encodeV1_keys run.decodeV1 i within
        have row : run.decodeV1[i] = run.view.logicalRecord i := by
          simp [Run.decodeV1]
        rw [row] at w
        simp only [View.logicalRecord, source.1, run.interleaved.1, run.interleaved.2] at w
        by_cases even : (k - 2) % 2 = 0
        · have off : 8 * k = 16 + i * 16 := by dsimp [i]; omega
          rw [off]
          exact w.1
        · have off : 8 * k = 24 + i * 16 := by dsimp [i]; omega
          rw [off]
          exact w.2
  exact eq_of_aligned_words outputSize aligned

#print axioms Alvoki.Packed.encodeV1_roundtrip
#print axioms Alvoki.Packed.decodeV1_reencode

end Alvoki.Packed
