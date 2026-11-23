import CompactionCodec
import SequentialModel

namespace Alvoki.Compaction
open Alvoki.Opt

def retainedRows (left right : Run) (floor : UInt64) : List RawEntry :=
  Model.retain (Model.union left.decodeV3 right.decodeV3) floor

private def payloadAt (left right : Run) (position : Position) : UInt64 × UInt64 :=
  (rawRow (left.source right position).bytes position.2.toNat).payload

private theorem retainedRows_eq (left right : Run) (floor : UInt64)
    (leftFits : left.bytes.size < USize.size) (rightFits : right.bytes.size < USize.size) :
    retainedRows left right floor =
      (positionsRetained left right floor).map (Model.Entry.mapPayload (payloadAt left right)) := by
  have leftRows := positions_decode left right false leftFits
  have rightRows := positions_decode left right true rightFits
  change (left.positions false).map (Model.Entry.mapPayload (payloadAt left right)) = left.decodeV3
    at leftRows
  change (right.positions true).map (Model.Entry.mapPayload (payloadAt left right)) = right.decodeV3
    at rightRows
  rw [retainedRows, ← leftRows, ← rightRows, Model.union_map, Model.retain_map]
  rfl

theorem Run.decoded_valid {bytes : ByteArray} {run : Run} (accepted : parse bytes = .ok run) :
    Model.Ordered run.decodeV3 ∧ ∀ r ∈ run.decodeV3, CanonicalRow r := by
  have h := parse_spec accepted
  simpa only [Run.decodeV3, h.1, h.2.1] using h.2.2.2.2.2

private theorem positionBytes_encode (left right : Run) (rows : List (Model.Entry Position))
    (members : ∀ r ∈ rows, r ∈ Model.union (left.positions false) (right.positions true))
    (leftFits : left.bytes.size < USize.size) (rightFits : right.bytes.size < USize.size) :
    positionBytes left right rows =
      encodeV3Payload (rows.map (Model.Entry.mapPayload (payloadAt left right))) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have selected := members row List.mem_cons_self
    have bounded := USize.lt_iff_toNat_lt.mp (position_bounds selected)
    have ⟨keys, seqs⟩ := position_key_sequence selected leftFits rightFits
    rw [positionBytes, List.map_cons, encodeV3Payload,
      ih (fun r mem => members r (List.mem_cons_of_mem _ mem))]
    apply congrArg (· ++ encodeV3Payload (rows.map (Model.Entry.mapPayload (payloadAt left right))))
    rw [show row.mapPayload (payloadAt left right) =
        rawRow (left.source right row.payload).bytes row.payload.2.toNat by
      unfold Model.Entry.mapPayload payloadAt
      rw [keys, seqs]]
    exact (encodeV3Row_extract _ _ bounded).symm

/-- Both stock output paths write the canonical v3 encoding of the logical retained history. -/
theorem compact_eq_encode (left right : Run) (floor : UInt64)
    (leftFits : left.bytes.size < USize.size) (rightFits : right.bytes.size < USize.size) :
    compact left right floor = encodeV3 (retainedRows left right floor) := by
  rw [compact_refines, retainedRows_eq left right floor leftFits rightFits, encodeV3,
    encodeV3Header, List.length_map]
  apply congrArg (pushWordFast (pushWordFast ByteArray.empty
    (positionsRetained left right floor).length.toUInt64) 3 ++ ·)
  exact positionBytes_encode left right _ (fun _ mem =>
    (Model.retainFrom_sublist _ floor 0 false).subset mem) leftFits rightFits

theorem compactSpans_eq_encode (left right : Run) (floor : UInt64)
    (leftFits : left.bytes.size < USize.size) (rightFits : right.bytes.size < USize.size) :
    compactSpans left right floor = encodeV3 (retainedRows left right floor) := by
  rw [compactSpans_eq_compact, compact_eq_encode left right floor leftFits rightFits]

theorem compact_roundtrip {left right : Run} {leftBytes rightBytes : ByteArray}
    (lp : parse leftBytes = .ok left) (rp : parse rightBytes = .ok right) (floor : UInt64)
    (fits : 16 + 32 * (retainedRows left right floor).length < USize.size) :
    ∃ out, parse (compact left right floor) = .ok out ∧ out.decodeV3 = retainedRows left right floor := by
  have leftFits : left.bytes.size < USize.size := (parse_spec lp).1 ▸ (parse_spec lp).2.2.1
  have rightFits : right.bytes.size < USize.size := (parse_spec rp).1 ▸ (parse_spec rp).2.2.1
  rw [compact_eq_encode left right floor leftFits rightFits]
  have ⟨lo, lt⟩ := Run.decoded_valid lp
  have ⟨ro, rt⟩ := Run.decoded_valid rp
  have count : (retainedRows left right floor).length < UInt64.size := by
    have width := USize.size_le_uint64Size
    omega
  apply encodeV3_roundtrip _ fits count (Model.retain_ordered (Model.union_ordered lo ro) floor)
  intro row member
  have original := (Model.retainFrom_sublist _ floor 0 false).subset member
  exact (Model.mem_union original).elim (lt row) (rt row)

theorem decode_compact {left right out : Run} {leftBytes rightBytes : ByteArray}
    (lp : parse leftBytes = .ok left) (rp : parse rightBytes = .ok right) {floor : UInt64}
    (parsed : parse (compact left right floor) = .ok out) :
    out.decodeV3 = retainedRows left right floor := by
  have leftFits : left.bytes.size < USize.size := (parse_spec lp).1 ▸ (parse_spec lp).2.2.1
  have rightFits : right.bytes.size < USize.size := (parse_spec rp).1 ▸ (parse_spec rp).2.2.1
  have encoded := compact_eq_encode left right floor leftFits rightFits
  have size := (parse_spec parsed).2.2.1
  rw [encoded, encodeV3_size] at size
  obtain ⟨other, h, rows⟩ := compact_roundtrip lp rp floor size
  rw [parsed] at h
  have same := Except.ok.inj h
  rw [same, rows]

theorem compact_preserves {left right out : Run} {leftBytes rightBytes : ByteArray}
    (lp : parse leftBytes = .ok left) (rp : parse rightBytes = .ok right) {floor snapshot : UInt64}
    (parsed : parse (compact left right floor) = .ok out) (live : floor ≤ snapshot) (key : UInt64) :
    Model.winner out.decodeV3 key snapshot =
      Model.winner (Model.union left.decodeV3 right.decodeV3) key snapshot := by
  rw [decode_compact lp rp parsed]
  exact Model.winner_retain _ key live

def isPut (payload : UInt64 × UInt64) : Bool := payload.1 == 0

def checksum (sum : UInt64) (row : RawEntry) : UInt64 := sum + (row.key ^^^ row.payload.2)

private theorem fold_eq_on {rows : List α} (a b : β → α → β)
    (same : ∀ row ∈ rows, ∀ state, a state row = b state row) (start : β) :
    rows.foldl a start = rows.foldl b start := by
  induction rows generalizing start with
  | nil => rfl
  | cons row rows ih =>
    simp only [List.foldl_cons, same row List.mem_cons_self]
    exact ih (fun r mem => same r (List.mem_cons_of_mem _ mem)) _

/-- The direct scan folds the exact ordered visible rows of the merged history. -/
theorem scan_refines (left right : Run) (snapshot : UInt64)
    (leftFits : left.bytes.size < USize.size) (rightFits : right.bytes.size < USize.size) :
    scan left right snapshot =
      (Model.visibleRows (Model.union left.decodeV3 right.decodeV3) snapshot isPut).foldl checksum 0 := by
  rw [scan_positions, Model.visibleRows, List.foldl_filter]
  change _ = (retainedRows left right snapshot).foldl _ 0
  rw [retainedRows_eq left right snapshot leftFits rightFits, List.foldl_map]
  apply fold_eq_on
  intro row mem sum
  let source := left.source right row.payload
  have fits : source.bytes.size < USize.size := by
    cases h : row.payload.1 <;> simp [source, Run.source, h, leftFits, rightFits]
  have h := position_fields ((Model.retainFrom_sublist _ snapshot 0 false).subset mem) fits
  dsimp only
  rw [h.1, h.2]
  rfl

/-- An already materialized run folds its exact ordered visible rows. -/
theorem Run.scan_refines (run : Run) (snapshot : UInt64) (fits : run.bytes.size < USize.size) :
    run.scan snapshot = (Model.visibleRows run.decodeV3 snapshot isPut).foldl checksum 0 := by
  obtain ⟨empty, count, emptyFits, eq⟩ := run.scan_with_empty snapshot
  rw [eq, Alvoki.Compaction.scan_refines run empty snapshot fits emptyFits]
  simp [Run.decodeV3, count, rawRows]

theorem compact_visibleRows_eq {left right out : Run} {leftBytes rightBytes : ByteArray}
    (lp : parse leftBytes = .ok left) (rp : parse rightBytes = .ok right) {floor snapshot : UInt64}
    (parsed : parse (compact left right floor) = .ok out) (live : floor ≤ snapshot) :
    Model.visibleRows out.decodeV3 snapshot isPut =
      Model.visibleRows (Model.union left.decodeV3 right.decodeV3) snapshot isPut :=
  Model.visibleRows_congr (Run.decoded_valid parsed).1
    (Model.union_ordered (Run.decoded_valid lp).1 (Run.decoded_valid rp).1) snapshot isPut
    (compact_preserves lp rp parsed live)

theorem compact_scan_eq {left right out : Run} {leftBytes rightBytes : ByteArray}
    (lp : parse leftBytes = .ok left) (rp : parse rightBytes = .ok right) {floor snapshot : UInt64}
    (parsed : parse (compact left right floor) = .ok out) (live : floor ≤ snapshot) :
    out.scan snapshot = scan left right snapshot := by
  have leftFits : left.bytes.size < USize.size := (parse_spec lp).1 ▸ (parse_spec lp).2.2.1
  have rightFits : right.bytes.size < USize.size := (parse_spec rp).1 ▸ (parse_spec rp).2.2.1
  have outFits : out.bytes.size < USize.size := (parse_spec parsed).1 ▸ (parse_spec parsed).2.2.1
  rw [out.scan_refines snapshot outFits, scan_refines left right snapshot leftFits rightFits,
    compact_visibleRows_eq lp rp parsed live]

def decodedValue (payload : UInt64 × UInt64) : Option UInt64 :=
  if isPut payload then some payload.2 else none

/-- Turn an accepted v3 block into a sequential history with typed tombstones. -/
def Run.history {bytes : ByteArray} {run : Run} (accepted : parse bytes = .ok run) :
    Sequential.History UInt64 :=
  ⟨run.decodeV3.map (Model.Entry.mapPayload decodedValue),
    List.pairwise_map.mpr ((Run.decoded_valid accepted).1.imp fun before => before)⟩

/-- The packed compactor implements the sequential model's adjacent-run replacement. -/
theorem compact_history {left right out : Run} {leftBytes rightBytes : ByteArray}
    (lp : parse leftBytes = .ok left) (rp : parse rightBytes = .ok right) {floor : UInt64}
    (parsed : parse (compact left right floor) = .ok out) :
    Run.history parsed = Sequential.compactPair (Run.history lp) (Run.history rp) floor := by
  apply Sequential.History.ext_rows
  unfold Run.history Sequential.compactPair Sequential.History.union Sequential.History.retain
  dsimp only
  rw [decode_compact lp rp parsed, Model.union_map, Model.retain_map]
  rfl

end Alvoki.Compaction
