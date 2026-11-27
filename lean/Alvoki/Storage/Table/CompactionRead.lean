import Alvoki.Storage.Table.CompactionReadContract
import CompactionProofs
import OptProofs

namespace Alvoki.Compaction
open Alvoki.Opt

/-- A parsed run paired with erased evidence of its origin. -/
structure CheckedRun where
  private mk ::
  run : Run
  accepted : parse run.bytes = .ok run

def CheckedRun.openBytes (bytes : ByteArray) : Except String CheckedRun :=
  match parsed : parse bytes with
  | .error message => .error message
  | .ok run => .ok ⟨run, (parse_spec parsed).1 ▸ parsed⟩

def CheckedRun.history (checked : CheckedRun) : Sequential.History UInt64 :=
  Run.history checked.accepted

theorem CheckedRun.fits (checked : CheckedRun) : checked.run.bytes.size < USize.size :=
  (parse_spec checked.accepted).2.2.1

theorem CheckedRun.byteSize_eq_history (checked : CheckedRun) :
    checked.run.bytes.size = 16 + 32 * checked.history.rows.length := by
  rw [checked.run.size_eq]
  simp only [CheckedRun.history, Run.history, Run.decodeV3, List.length_map, rawRows_length]

@[inline] def CheckedRun.lowerBoundKey (checked : @& CheckedRun) (target : UInt64) : USize :=
  searchMachine checked.run.keyOrZero target checked.run.count

theorem CheckedRun.lowerBoundKey_spec (checked : CheckedRun) (target : UInt64) :
    Partition (fun i => decide ((rawRow checked.run.bytes i).key < target))
      checked.run.count.toNat (checked.lowerBoundKey target).toNat := by
  let run := checked.run
  have read (i : Nat) (bound : i < run.count.toNat) :
      run.keyOrZero i.toUSize = (rawRow run.bytes i).key := by
    have exactIndex : i.toUSize.toNat = i :=
      USize.toNat_ofNat_of_lt (Nat.lt_trans bound run.count.toNat_lt_size)
    have hit : i.toUSize < run.count := USize.lt_iff_toNat_lt.mpr (by rwa [exactIndex])
    rw [run.keyOrZero_eq _ hit checked.fits, exactIndex]
  have sorted (i j : Nat) (le : i ≤ j) (bound : j < run.count.toNat) :
      run.keyOrZero i.toUSize ≤ run.keyOrZero j.toUSize := by
    rcases Nat.eq_or_lt_of_le le with rfl | less
    · exact UInt64.le_refl _
    · rw [read j bound, read i (Nat.lt_trans less bound)]
      have ordered := (Run.decoded_valid checked.accepted).1
      change Model.Ordered (rawRows run.bytes run.count.toNat) at ordered
      have before := List.pairwise_iff_getElem.mp ordered i j (by simp; omega) (by simpa using bound) less
      rw [rawRows_get, rawRows_get, Model.before_iff] at before
      exact before.elim UInt64.le_of_lt (fun eq => eq.1 ▸ UInt64.le_refl _)
  have p := searchMachine_partition run.keyOrZero target run.count sorted
  refine ⟨p.1, ?_, ?_⟩
  · intro i before
    change decide ((rawRow run.bytes i).key < target) = true
    rw [← read i (Nat.lt_of_lt_of_le before p.1)]
    exact p.2.1 i before
  · intro i after bound
    change decide ((rawRow run.bytes i).key < target) = false
    rw [← read i bound]
    exact p.2.2 i after bound

@[inline] def CheckedRun.upperBoundKey (checked : @& CheckedRun) (key : UInt64) : USize :=
  if key.toNat + 1 < UInt64.size then checked.lowerBoundKey (UInt64.ofNat (key.toNat + 1))
  else checked.run.count

theorem CheckedRun.upperBoundKey_spec (checked : CheckedRun) (key : UInt64) :
    Partition (fun i => decide ((rawRow checked.run.bytes i).key ≤ key))
      checked.run.count.toNat (checked.upperBoundKey key).toNat := by
  unfold CheckedRun.upperBoundKey
  split
  · rename_i fits
    have eq (i : Nat) : (rawRow checked.run.bytes i).key ≤ key ↔
        (rawRow checked.run.bytes i).key < UInt64.ofNat (key.toNat + 1) := by
      rw [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' fits]
      omega
    simpa only [eq] using checked.lowerBoundKey_spec (UInt64.ofNat (key.toNat + 1))
  · rename_i maxKey
    refine ⟨Nat.le_refl _, fun i _ => decide_eq_true ?_, fun _ le lt => (Nat.not_lt_of_ge le lt).elim⟩
    rw [UInt64.le_iff_toNat_le]
    have cap := (rawRow checked.run.bytes i).key.toNat_lt_size
    omega

private def rawInterval (run : Run) (i stop : USize) : List RawEntry :=
  (List.range' i.toNat (stop.toNat - i.toNat)).map (rawRow run.bytes)

private theorem rawInterval_cons (run : Run) (i stop : USize) (hit : i < stop) :
    rawInterval run i stop = rawRow run.bytes i.toNat :: rawInterval run (i + 1) stop := by
  have within := USize.lt_iff_toNat_lt.mp hit
  have next := addOne i stop within
  have amt : stop.toNat - i.toNat = (stop.toNat - (i + 1).toNat) + 1 := by omega
  unfold rawInterval
  conv => lhs; rw [amt, List.range'_succ, List.map_cons]
  rw [next]

private theorem rawInterval_end (run : Run) (i stop : USize) (past : ¬i < stop) :
    rawInterval run i stop = [] := by
  rw [USize.lt_iff_toNat_lt] at past
  simp [rawInterval, show stop.toNat - i.toNat = 0 by omega]

@[specialize] private def foldFrom (run : @& Run) (i stop : USize) (stopBound : stop ≤ run.count)
    (consume : α → RawEntry → α) (initial : α) : α :=
  if hit : i < stop then
    foldFrom run (i + 1) stop stopBound consume
      (consume initial (run.rowAt i (USize.lt_of_lt_of_le hit stopBound)))
  else initial
termination_by stop.toNat - i.toNat
decreasing_by
  have order := USize.lt_iff_toNat_lt.mp hit
  have step := addOne i stop order
  omega

private theorem foldFrom_eq (run : Run) (i stop : USize) (stopBound : stop ≤ run.count)
    (fits : run.bytes.size < USize.size) (consume : α → RawEntry → α) (initial : α) :
    foldFrom run i stop stopBound consume initial = (rawInterval run i stop).foldl consume initial := by
  rw [foldFrom]
  by_cases hit : i < stop
  · rw [dite_eq_left hit, rawInterval_cons run i stop hit, List.foldl_cons,
      run.rowAt_eq _ _ fits]
    exact foldFrom_eq run (i + 1) stop stopBound fits consume _
  · rw [dite_eq_right hit, rawInterval_end run i stop hit]
    rfl
termination_by stop.toNat - i.toNat
decreasing_by
  have order := USize.lt_iff_toNat_lt.mp hit
  have step := addOne i stop order
  omega

private def findFrom (run : @& Run) (i stop : USize) (stopBound : stop ≤ run.count)
    (snapshot : UInt64) : Option RawEntry :=
  if hit : i < stop then
    let row := run.rowAt i (USize.lt_of_lt_of_le hit stopBound)
    if row.sequence ≤ snapshot then some row
    else findFrom run (i + 1) stop stopBound snapshot
  else none
termination_by stop.toNat - i.toNat
decreasing_by
  have order := USize.lt_iff_toNat_lt.mp hit
  have step := addOne i stop order
  omega

private theorem findFrom_eq (run : Run) (i stop : USize) (stopBound : stop ≤ run.count)
    (fits : run.bytes.size < USize.size) (snapshot : UInt64) :
    findFrom run i stop stopBound snapshot =
      (rawInterval run i stop).find? (fun row => row.sequence ≤ snapshot) := by
  rw [findFrom]
  by_cases hit : i < stop
  · rw [dite_eq_left hit, rawInterval_cons run i stop hit, run.rowAt_eq _ _ fits]
    by_cases eligible : (rawRow run.bytes i.toNat).sequence ≤ snapshot
    · simp [eligible]
    · simp only [eligible, ite_false, decide_false, List.find?_cons]
      exact findFrom_eq run (i + 1) stop stopBound fits snapshot
  · rw [dite_eq_right hit, rawInterval_end run i stop hit]
    rfl
termination_by stop.toNat - i.toNat
decreasing_by
  have order := USize.lt_iff_toNat_lt.mp hit
  have step := addOne i stop order
  omega

theorem CheckedRun.key_lt_bound (checked : CheckedRun) (target : UInt64) (i : Nat)
    (within : i < checked.run.count.toNat) :
    (rawRow checked.run.bytes i).key < target ↔ i < (checked.lowerBoundKey target).toNat := by
  have ⟨_, lo, hi⟩ := checked.lowerBoundKey_spec target
  constructor
  · intro lt
    by_cases past : (checked.lowerBoundKey target).toNat ≤ i
    · exact (of_decide_eq_false (hi i past within) lt).elim
    · omega
  · intro before
    exact of_decide_eq_true (lo i before)

def RawEntry.version (row : RawEntry) : Model.Entry (Option UInt64) :=
  row.mapPayload decodedValue

/-- Iterate the versions in a half-open key range. Tombstones are passed to the consumer. -/
@[specialize] def CheckedRun.foldRange (checked : @& CheckedRun) (start stop : UInt64)
    (consume : α → Model.Entry (Option UInt64) → α) (initial : α) : α :=
  foldFrom checked.run (checked.lowerBoundKey start) (checked.lowerBoundKey stop)
    (USize.le_iff_toNat_le.mpr (checked.lowerBoundKey_spec stop).1)
    (fun state row => consume state row.version) initial

/-- Return the winning version, including a tombstone. An outer none means no eligible version. -/
def CheckedRun.lookupEntry (checked : @& CheckedRun) (key snapshot : UInt64) :
    Option (Model.Entry (Option UInt64)) :=
  (findFrom checked.run (checked.lowerBoundKey key) (checked.upperBoundKey key)
    (USize.le_iff_toNat_le.mpr (checked.upperBoundKey_spec key).1) snapshot).map RawEntry.version

def CheckedRun.lookup (checked : @& CheckedRun) (key snapshot : UInt64) : Option UInt64 :=
  (checked.lookupEntry key snapshot).bind Model.Entry.payload

def inRange (start stop : UInt64) (row : Model.Entry α) : Bool :=
  start ≤ row.key && row.key < stop

private theorem raw_keyRange (checked : CheckedRun) (start stop : UInt64) :
    (checked.run.decodeV3.filter (inRange start stop)) =
      rawInterval checked.run (checked.lowerBoundKey start) (checked.lowerBoundKey stop) := by
  unfold Run.decodeV3 rawRows rawInterval
  rw [List.filter_map]
  apply congrArg (List.map (rawRow checked.run.bytes))
  apply filterIndexRange _ _ _ _ (checked.lowerBoundKey_spec stop).1
  intro i bound
  have lo := checked.key_lt_bound start i bound
  have hi := checked.key_lt_bound stop i bound
  simp only [Function.comp_apply, inRange, Bool.and_eq_true_iff, decide_eq_true_eq, hi]
  rw [← UInt64.not_lt, lo, Nat.not_lt]

theorem CheckedRun.foldRange_eq (checked : CheckedRun) (start stop : UInt64)
    (consume : α → Model.Entry (Option UInt64) → α) (initial : α) :
    checked.foldRange start stop consume initial =
      (checked.history.rows.filter (inRange start stop)).foldl consume initial := by
  unfold CheckedRun.foldRange
  rw [foldFrom_eq _ _ _ _ checked.fits, ← raw_keyRange]
  change _ = ((checked.run.decodeV3.map RawEntry.version).filter (inRange start stop)).foldl consume initial
  rw [List.filter_map, List.foldl_map]
  rfl

/-- The private search over the bounded interval agrees with scanning those
raw rows. This boundary does not claim the interval contains exactly a key. -/
theorem CheckedRun.lookupEntry_as_interval (checked : CheckedRun) (key snapshot : UInt64) :
    checked.lookupEntry key snapshot =
      ((List.range' (checked.lowerBoundKey key).toNat
        ((checked.upperBoundKey key).toNat - (checked.lowerBoundKey key).toNat)).map
          (rawRow checked.run.bytes) |>.find? (fun row => row.sequence ≤ snapshot)).map
        RawEntry.version := by
  unfold CheckedRun.lookupEntry
  rw [findFrom_eq _ _ _ _ checked.fits]
  rfl

private theorem foldPrepend (rows acc : List α) :
    (rows.foldl (fun out row => row :: out) acc).reverse = acc.reverse ++ rows := by
  induction rows generalizing acc with
  | nil => simp
  | cons row rest ih =>
    simp only [List.foldl_cons, ih, List.reverse_cons, List.append_assoc, List.singleton_append]

/-- Materialize only the requested key interval, preserving every version for table-wide merge. -/
def CheckedRun.rangeEntries (checked : @& CheckedRun) (start stop : UInt64) :
    List (Model.Entry (Option UInt64)) :=
  (checked.foldRange start stop (fun out row => row :: out) []).reverse

theorem CheckedRun.rangeEntries_eq (checked : CheckedRun) (start stop : UInt64) :
    checked.rangeEntries start stop = checked.history.rows.filter (inRange start stop) := by
  rw [CheckedRun.rangeEntries, checked.foldRange_eq, foldPrepend]
  rfl

def CheckedRun.rangeHistory (checked : @& CheckedRun) (start stop : UInt64) :
    Sequential.History UInt64 :=
  ⟨checked.rangeEntries start stop, by rw [checked.rangeEntries_eq]; exact checked.history.ordered.filter _⟩

private def physicalRow (row : Model.Entry (Option UInt64)) : RawEntry :=
  row.mapPayload fun value => match value with
  | none => (1, 0)
  | some v => (0, v)

theorem CheckedRun.openBytes_spec {bytes : ByteArray} {checked : CheckedRun}
    (opened : openBytes bytes = .ok checked) :
    parse bytes = .ok checked.run ∧ checked.run.bytes = bytes := by
  unfold openBytes at opened
  split at opened
  · contradiction
  · rename_i parsed
    cases opened
    exact ⟨parsed, (parse_spec parsed).1⟩

/-- Flush an ordered memtable as a validated v3 run. -/
def CheckedRun.ofHistory (history : Sequential.History UInt64) : Except String CheckedRun :=
  openBytes (history.rows.foldl (fun out row => appendV3Row out (physicalRow row))
    (encodeV3Header history.rows.length))

private theorem foldFlush_eq (rows : List (Model.Entry (Option UInt64))) (out : ByteArray) :
    rows.foldl (fun bytes row => appendV3Row bytes (physicalRow row)) out =
      out ++ encodeV3Payload (rows.map physicalRow) := by
  induction rows generalizing out with
  | nil => simp [encodeV3Payload]
  | cons row rest ih =>
    rw [List.foldl_cons, ih, List.map_cons, encodeV3Payload, appendV3Row_eq,
      ByteArray.append_assoc]

private theorem ofHistory_eq (history : Sequential.History UInt64) :
    CheckedRun.ofHistory history = CheckedRun.openBytes (encodeV3 (history.rows.map physicalRow)) := by
  simp [CheckedRun.ofHistory, foldFlush_eq, encodeV3]

theorem CheckedRun.ofHistory_complete (history : Sequential.History UInt64)
    (fits : 16 + 32 * history.rows.length < USize.size) :
    ∃ run, ofHistory history = .ok run := by
  let rows := history.rows.map physicalRow
  have size : 16 + 32 * rows.length < USize.size := by simpa [rows] using fits
  have count : rows.length < UInt64.size := by
    have machine : rows.length < USize.size := by omega
    exact Nat.lt_of_lt_of_le machine USize.size_le_uint64Size
  have ordered : Model.Ordered rows := by
    change (history.rows.map physicalRow).Pairwise (fun a b => Model.before a b)
    rw [List.pairwise_map]
    exact history.ordered
  have tags : ∀ row ∈ rows, CanonicalRow row := by
    intro _ mem
    obtain ⟨entry, _, rfl⟩ := List.mem_map.mp mem
    cases entry with
    | mk key sequence value => cases value <;> simp [CanonicalRow, physicalRow, Model.Entry.mapPayload]
  obtain ⟨run, parsed, _⟩ := encodeV3_roundtrip rows size count ordered tags
  change parse (encodeV3 (history.rows.map physicalRow)) = .ok run at parsed
  rw [ofHistory_eq, openBytes]
  split
  · rename_i failed
    rw [parsed] at failed
    cases failed
  · exact ⟨_, rfl⟩

theorem CheckedRun.ofHistory_spec {history : Sequential.History UInt64} {checked : CheckedRun}
    (written : ofHistory history = .ok checked) : checked.history = history := by
  rw [ofHistory_eq] at written
  obtain ⟨_, bytes⟩ := openBytes_spec written
  have size := checked.run.size_eq
  rw [bytes, encodeV3_size] at size
  have count : checked.run.count.toNat = (history.rows.map physicalRow).length := by omega
  apply Sequential.History.ext_rows
  change (rawRows checked.run.bytes checked.run.count.toNat).map RawEntry.version = history.rows
  rw [bytes, count, rawRows_encodeV3, List.map_map]
  have inverse (row : Model.Entry (Option UInt64)) : (physicalRow row).version = row := by
    cases row with
    | mk k s v => cases v <;> rfl
  simp [Function.comp_def, inverse]

theorem CheckedRun.openOwnBytes (checked : CheckedRun) :
    openBytes checked.run.bytes = .ok checked := by
  unfold openBytes
  split
  · rename_i notParsed
    rw [checked.accepted] at notParsed
    contradiction
  · rename_i parsed
    rw [checked.accepted] at parsed
    cases parsed
    cases checked
    rfl

def CheckedRun.compact (left right : @& CheckedRun) (floor : UInt64) : Except String CheckedRun :=
  openBytes (compactSpans left.run right.run floor)

theorem CheckedRun.compact_spec {left right out : CheckedRun} {floor : UInt64}
    (compacted : left.compact right floor = .ok out) :
    out.history = Sequential.compactPair left.history right.history floor := by
  have parsed := (openBytes_spec compacted).1
  rw [compactSpans_eq_compact] at parsed
  exact compact_history left.accepted right.accepted parsed

/-- Remove versions shadowed at every retained snapshot within a single run.
The boundary version, including a tombstone, remains in the packed output. -/
def CheckedRun.retainVersions (run : @& CheckedRun) (floor : UInt64) : Except String CheckedRun := do
  let empty ← ofHistory .empty
  run.compact empty floor

theorem CheckedRun.retainVersions_spec {run out : CheckedRun} {floor : UInt64}
    (retained : run.retainVersions floor = .ok out) : out.history = run.history.retain floor := by
  unfold retainVersions at retained
  cases encoded : ofHistory .empty with
  | error => simp [encoded, Bind.bind, Except.bind] at retained
  | ok empty =>
    have compacted : run.compact empty floor = .ok out := by
      simpa [encoded, Bind.bind, Except.bind] using retained
    rw [compact_spec compacted, ofHistory_spec encoded]
    apply Sequential.History.ext_rows
    simp [Sequential.compactPair, Sequential.History.union, Sequential.History.retain,
      Sequential.History.empty, Model.union_nil_right]

/-- Bound the actual packed file by the retained history's input rows.
The fixed v3 header and row width also account for retained tombstones. -/
theorem CheckedRun.byteSize_le_of_retainedHistory {source : Sequential.History UInt64} {out : CheckedRun}
    {floor : UInt64} (retained : out.history = source.retain floor) :
    out.run.bytes.size ≤ 16 + 32 * Model.retentionRowBound source.rows floor := by
  rw [out.byteSize_eq_history, retained]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 32 (Model.retain_length_le source.ordered floor)) 16

theorem CheckedRun.retainVersions_byteSize_le {run out : CheckedRun} {floor : UInt64}
    (retained : run.retainVersions floor = .ok out) :
    out.run.bytes.size ≤ 16 + 32 * Model.retentionRowBound run.history.rows floor :=
  byteSize_le_of_retainedHistory (retainVersions_spec retained)

theorem CheckedRun.compact_byteSize_le {left right out : CheckedRun} {floor : UInt64}
    (compacted : left.compact right floor = .ok out) :
    out.run.bytes.size ≤ 16 + 32 * Model.retentionRowBound (left.history.union right.history).rows floor :=
  byteSize_le_of_retainedHistory (compact_spec compacted)

theorem CheckedRun.retainVersions_complete (run : CheckedRun) (floor : UInt64) :
    ∃ out, run.retainVersions floor = .ok out := by
  obtain ⟨empty, encoded⟩ := ofHistory_complete .empty (by
    have width := USize.le_size
    simp only [Sequential.History.empty, List.length_nil, Nat.mul_zero, Nat.add_zero]
    omega)
  have emptyRows : empty.run.decodeV3 = [] := by
    have mapped := congrArg Sequential.History.rows (ofHistory_spec encoded)
    change (empty.run.decodeV3.map _ : List (Model.Entry (Option UInt64))) = [] at mapped
    exact List.map_eq_nil_iff.mp mapped
  have limit : 16 + 32 * (retainedRows run.run empty.run floor).length < USize.size := by
    rw [retainedRows, emptyRows, Model.union_nil_right]
    have kept := (Model.retainFrom_sublist run.run.decodeV3 floor 0 false).length_le
    change (Model.retain run.run.decodeV3 floor).length ≤ run.run.decodeV3.length at kept
    have count : run.run.decodeV3.length = run.run.count.toNat := rawRows_length _ _
    rw [count] at kept
    have fits := run.fits
    rw [run.run.size_eq] at fits
    omega
  obtain ⟨_, parsed, _⟩ := compact_roundtrip run.accepted empty.accepted floor limit
  unfold retainVersions
  simp only [encoded, Bind.bind, Except.bind, CheckedRun.compact, openBytes]
  split
  · rename_i failed
    rw [compactSpans_eq_compact, parsed] at failed
    contradiction
  · exact ⟨_, rfl⟩

end Alvoki.Compaction
