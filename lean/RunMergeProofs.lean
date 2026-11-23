import RunProofs
import CompactionModel

namespace Alvoki.Packed
open Alvoki.Opt Alvoki.ByteWords
open MergeModel
open Alvoki.Compaction

private def liftRow (row : Row) : Model.Entry Row := ⟨row.record.1, 0, row⟩

/-- V1 is the special case of the right-biased ordered union with one version per key. -/
private theorem lift_union (left right : List Row) :
    (union left right).map liftRow =
      Model.union (left.map liftRow) (right.map liftRow) := by
  induction left, right using union.induct with
  | case1 rows => rw [union.eq_1, List.map_nil, Model.union_nil_left]
  | case2 rows nonempty => rw [union.eq_2 _ nonempty, List.map_nil, Model.union_nil_right]
  | case3 a as b bs order ih =>
    have lifted : Model.before (liftRow a) (liftRow b) = true := by simp [liftRow, order]
    simp only [List.map_cons] at ih
    rw [union.eq_3, ite_eq_left order, List.map_cons, List.map_cons, List.map_cons,
      Model.union.eq_3, ite_eq_left lifted, ih]
  | case4 a as b bs order tie ih =>
    have lifted : ¬ Model.before (liftRow a) (liftRow b) = true := by simp [liftRow, order]
    have equal : Model.sameVersion (liftRow a) (liftRow b) = true := by
      simpa [liftRow] using tie
    rw [union.eq_3, ite_eq_right order, ite_eq_left tie, List.map_cons, List.map_cons, List.map_cons,
      Model.union.eq_3, ite_eq_right lifted, ite_eq_left equal, ih]
  | case5 a as b bs order tie ih =>
    have lifted : ¬ Model.before (liftRow a) (liftRow b) = true := by simp [liftRow, order]
    have unequal : ¬ Model.sameVersion (liftRow a) (liftRow b) = true := by
      simpa [liftRow] using tie
    simp only [List.map_cons] at ih
    rw [union.eq_3, ite_eq_right order, ite_eq_right tie, List.map_cons, List.map_cons, List.map_cons,
      Model.union.eq_3, ite_eq_right lifted, ite_eq_right unequal, ih]

private theorem rowsFrom_records (view : View) (i : USize) :
    (rowsFrom view i).map Row.record =
      (List.range' i.toNat (view.count.toNat - i.toNat)).map view.logicalRecord := by
  by_cases hit : i < view.count
  · have within := USize.lt_iff_toNat_lt.mp hit
    have step := addOne i view.count within
    have count : view.count.toNat - i.toNat = (view.count.toNat - (i + 1).toNat) + 1 := by omega
    rw [rowsFrom_cons _ _ hit, List.map_cons, rowsFrom_records, count,
      List.range'_succ, List.map_cons, ← step]
    rfl
  · rw [rowsFrom_nil _ _ hit]
    have n : view.count.toNat - i.toNat = 0 := by
      rw [USize.lt_iff_toNat_lt] at hit
      omega
    simp [n]
termination_by view.count.toNat - i.toNat
decreasing_by omega

private theorem Run.source_records (run : Run) :
    (rowsFrom run.view 0).map Row.record = run.decodeV1.toList := by
  rw [rowsFrom_records,
    show (0 : USize).toNat = 0 from USize.toNat_ofNat_of_lt_32 (by decide),
    Nat.sub_zero, ← List.range_eq_range']
  apply List.ext_getElem (by simp [Run.count])
  intro i _ _
  simp

private theorem Run.source_ordered (run : Run) :
    Model.Ordered ((rowsFrom run.view 0).map liftRow) := by
  apply List.pairwise_map.mpr
  have records : ((rowsFrom run.view 0).map Row.record).Pairwise (fun a b => a.1 < b.1) := by
    rw [run.source_records]
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj ij
    simpa [Run.count] using run.view.logical_ordered run.ordered i j ij
      (show j < run.count.toNat by simpa using hj)
  exact (List.pairwise_map.mp records).imp (fun order => by
    exact Model.before_iff.mpr (Or.inl order))

private theorem union_members {row : Row} {left right : List Row} (found : row ∈ union left right) :
    row ∈ left ∨ row ∈ right := by
  have h : liftRow row ∈ Model.union (left.map liftRow) (right.map liftRow) := by
    rw [← lift_union]
    exact List.mem_map.mpr ⟨row, found, rfl⟩
  rcases Model.mem_union h with l | r
  · obtain ⟨original, mem, eq⟩ := List.mem_map.mp l
    have same : original = row := congrArg Model.Entry.payload eq
    exact Or.inl (same ▸ mem)
  · obtain ⟨original, mem, eq⟩ := List.mem_map.mp r
    have same : original = row := congrArg Model.Entry.payload eq
    exact Or.inr (same ▸ mem)

def mergedRecords (left right : Run) : Array Record :=
  ((mergedRows left right).map Row.record).toArray

theorem mergedRecords_ordered (left right : Run) :
    ((mergedRows left right).map Row.record).Pairwise (fun a b => a.1 < b.1) := by
  have h : Model.Ordered ((mergedRows left right).map liftRow) := by
    unfold mergedRows
    rw [lift_union]
    exact Model.union_ordered left.source_ordered right.source_ordered
  apply List.pairwise_map.mpr
  exact (List.pairwise_map.mp h).imp (fun order => by
    simpa [liftRow] using Model.before_iff.mp order)

theorem mergedKeys_unique (left right : Run) :
    (((mergedRows left right).map Row.record).map Prod.fst).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  exact (mergedRecords_ordered left right).imp UInt64.ne_of_lt

private theorem rowAt_bytes (run : Run) (i : USize) (hit : i < run.view.count) :
    let row := rowAt run.view i hit
    row.bytes = pushWordFast (pushWordFast ByteArray.empty row.record.1) row.record.2 := by
  dsimp only
  let offset := 16 + i.toNat * 16
  let row := rowAt run.view i hit
  let keyBytes := pushWordFast ByteArray.empty row.record.1
  have keySize : keyBytes.size = 8 := by simp [keyBytes, pushWordFast_size]
  have bounds := USize.lt_iff_toNat_lt.mp hit
  have size := run.view.size_eq
  have extent : offset + 16 ≤ run.view.bytes.size := by dsimp [offset]; omega
  apply eq_of_aligned_words
  · change row.bytes.size = _
    simp [row.width, pushWordFast_size]
  intro k wordHit
  have small : k = 0 ∨ k = 1 := by simp only [pushWordFast_size, ByteArray.size_empty] at wordHit; omega
  rcases small with rfl | rfl
  · simp only [Nat.mul_zero]
    change word (run.view.bytes.extract offset (offset + 16)) 0 =
      word (pushWordFast keyBytes row.record.2) 0
    rw [word_extract _ _ _ _ (by omega) extent, word_preserved keyBytes _ _ (by omega)]
    have key : word keyBytes 0 = row.record.1 := pushWordFast_roundtrip _ _
    rw [key]
    simp [row, rowAt, View.logicalRecord, run.interleaved.1, offset]
  · simp only [Nat.mul_one]
    change word (run.view.bytes.extract offset (offset + 16)) 8 =
      word (pushWordFast keyBytes row.record.2) 8
    have read : word (pushWordFast keyBytes row.record.2) 8 = row.record.2 := by
      rw [← keySize, pushWordFast_roundtrip]
    rw [word_extract _ _ _ _ (by omega) extent, read]
    simp only [row, rowAt, View.logicalRecord, run.interleaved.1, run.interleaved.2, offset]
    exact congrArg (word run.view.bytes) (by omega)

private theorem rowsFrom_bytes (run : Run) (i : USize) (row : Row)
    (mem : row ∈ rowsFrom run.view i) :
    row.bytes = pushWordFast (pushWordFast ByteArray.empty row.record.1) row.record.2 := by
  by_cases hit : i < run.view.count
  · rw [rowsFrom_cons _ _ hit, List.mem_cons] at mem
    rcases mem with rfl | rest
    · exact rowAt_bytes run i hit
    · exact rowsFrom_bytes run (i + 1) row rest
  · rw [rowsFrom_nil _ _ hit] at mem
    contradiction
termination_by run.view.count.toNat - i.toNat
decreasing_by
  have h := USize.lt_iff_toNat_lt.mp hit
  have step := addOne i run.view.count h
  omega

private theorem payload_encode (rows : List Row)
    (canonical : ∀ row ∈ rows,
      row.bytes = pushWordFast (pushWordFast ByteArray.empty row.record.1) row.record.2) :
    bytesOf rows = encodeV1Payload (rows.map Row.record) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    rw [bytesOf, List.map_cons, encodeV1Payload, canonical row List.mem_cons_self,
      ih (fun r mem => canonical r (List.mem_cons_of_mem _ mem))]
    rfl

theorem merge_eq_encode (left right : Run) : merge left right = encodeV1 (mergedRecords left right) := by
  rw [merge_refines, encodeV1_parts, mergedRecords]
  simp only [List.size_toArray, List.length_map]
  congr 1
  apply payload_encode
  intro row mem
  rcases union_members mem with l | r
  · exact rowsFrom_bytes left 0 row l
  · exact rowsFrom_bytes right 0 row r

theorem merge_roundtrip (left right : Run)
    (fits : 16 + 16 * (mergedRecords left right).size < USize.size) :
    ∃ out, parseRun (merge left right) = .ok out ∧ out.decodeV1 = mergedRecords left right := by
  rw [merge_eq_encode]
  have countFits : (mergedRecords left right).size < UInt64.size := by
    have limit := USize.size_le_uint64Size
    omega
  refine encodeV1_roundtrip _ fits countFits ?_
  intro i j less hit
  have h := List.pairwise_iff_getElem.mp (mergedRecords_ordered left right)
  simpa only [mergedRecords, List.getElem_toArray] using
    h i j (by simpa [mergedRecords] using (show i < (mergedRecords left right).size by omega))
      (by simpa [mergedRecords] using hit) less

private theorem lookup_winner (run : Run) (rows : List Row)
    (decoded : rows.map Row.record = run.decodeV1.toList) (key : UInt64) :
    run.lookup key = (Model.winner (rows.map liftRow) key 0).map (fun entry => entry.payload.record.2) := by
  cases found : Model.winner (rows.map liftRow) key 0 with
  | none =>
    apply (run.lookup_none_iff key).mpr
    intro i within same
    have mem : run.decodeV1[i] ∈ rows.map Row.record := by
      rw [decoded]
      exact Array.mem_toList_iff.mpr (Array.getElem_mem within)
    obtain ⟨row, rowMem, eq⟩ := List.mem_map.mp mem
    have lifted : liftRow row ∈ rows.map liftRow := List.mem_map.mpr ⟨row, rowMem, rfl⟩
    have unusable := List.find?_eq_none.mp found _ lifted
    have h : row.record.1 = key := (congrArg Prod.fst eq).trans same
    simp [Model.eligible, liftRow, h] at unusable
  | some entry =>
    have chosen := List.mem_of_find?_eq_some found
    obtain ⟨row, rowMem, rfl⟩ := List.mem_map.mp chosen
    have h := List.find?_some found
    have same : row.record.1 = key := by simpa [Model.eligible, liftRow] using h
    have mem : row.record ∈ run.decodeV1 := by
      apply Array.mem_toList_iff.mp
      rw [← decoded]
      exact List.mem_map.mpr ⟨row, rowMem, rfl⟩
    obtain ⟨i, hit, record⟩ := Array.mem_iff_getElem.mp mem
    exact (run.lookup_some_iff key row.record.2).mpr ⟨i, hit, record.trans (Prod.ext same rfl)⟩

/-- A parsed merge returns the right value if present there and the left value otherwise. -/
theorem merge_lookup {left right out : Run} (parsed : parseRun (merge left right) = .ok out)
    (key : UInt64) : out.lookup key = (right.lookup key).or (left.lookup key) := by
  have bound := (parseRun_iff _).mp ⟨out, parsed⟩
  have fits := bound.1
  rw [merge_eq_encode, encodeV1_size] at fits
  obtain ⟨expected, outParsed, outDecoded⟩ := merge_roundtrip left right fits
  rw [parsed] at outParsed
  have same := Except.ok.inj outParsed
  rw [same]
  have decoded : (mergedRows left right).map Row.record = expected.decodeV1.toList := by
    rw [outDecoded]
    rfl
  rw [lookup_winner expected _ decoded, lookup_winner right _ right.source_records,
    lookup_winner left _ left.source_records, mergedRows, lift_union,
    Model.winner_union left.source_ordered right.source_ordered]
  generalize l : Model.winner (List.map liftRow (rowsFrom left.view 0)) key 0 = lw
  generalize r : Model.winner (List.map liftRow (rowsFrom right.view 0)) key 0 = rwinner
  cases lw with
  | none => cases rwinner <;> rfl
  | some lrow =>
    cases rwinner with
    | none => rfl
    | some rrow =>
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some l)
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some r)
      simp [Model.newest, liftRow]

theorem merge_lookup_absent {left right out : Run} (parsed : parseRun (merge left right) = .ok out)
    (key : UInt64) : out.lookup key = none ↔ left.lookup key = none ∧ right.lookup key = none := by
  rw [merge_lookup parsed]
  cases right.lookup key <;> simp [Option.or]

end Alvoki.Packed
