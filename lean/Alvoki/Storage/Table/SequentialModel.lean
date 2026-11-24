import CompactionModel

namespace Alvoki.Sequential
open Compaction.Model

/-- An ordered run of versions. The payload carries either a value or a tombstone. -/
structure History (α : Type) where
  rows : List (Entry (Option α))
  ordered : Ordered rows

theorem History.ext_rows {a b : History α} (eq : a.rows = b.rows) : a = b := by
  cases a
  cases b
  cases eq
  rfl

def History.empty : History α := ⟨[], List.Pairwise.nil⟩

def History.singleton (row : Entry (Option α)) : History α :=
  ⟨[row], List.pairwise_singleton _ _⟩

def History.union (older newer : History α) : History α :=
  ⟨Compaction.Model.union older.rows newer.rows, union_ordered older.ordered newer.ordered⟩

def History.retain (run : History α) (floor : UInt64) : History α :=
  ⟨Compaction.Model.retain run.rows floor, retain_ordered run.ordered floor⟩

/-- Candidates are folded from oldest publication to newest publication. -/
def across (key snapshot : UInt64) : List (History α) → Option (Entry (Option α))
  | [] => none
  | run :: newer => newest (winner run.rows key snapshot) (across key snapshot newer)

private theorem newest_assoc (a b c : Option (Entry α)) :
    newest (newest a b) c = newest a (newest b c) := by
  cases a with
  | none => cases b <;> cases c <;> rfl
  | some a =>
    cases b with
    | none => cases c <;> rfl
    | some b =>
      cases c with
      | none => by_cases ab : b.sequence < a.sequence <;> simp [newest, ab]
      | some c =>
        by_cases ab : b.sequence < a.sequence <;>
          by_cases bc : c.sequence < b.sequence <;>
          by_cases ac : c.sequence < a.sequence <;>
          simp [newest, ab, bc, ac]
        all_goals
          simp only [UInt64.lt_iff_toNat_lt] at *
          omega

def combined : List (History α) → History α
  | [] => .empty
  | left :: right => left.union (combined right)

theorem combined_winner (runs : List (History α)) (key snapshot : UInt64) :
    winner (combined runs).rows key snapshot = across key snapshot runs := by
  induction runs with
  | nil => rfl
  | cons run runs ih =>
    change winner (Compaction.Model.union run.rows (combined runs).rows) key snapshot = _
    rw [winner_union run.ordered (combined runs).ordered, ih]
    rfl

structure Table (α : Type) where
  runs : List (History α)
  memory : History α

def Table.histories (table : Table α) : List (History α) := table.runs ++ [table.memory]

/-- Insert a supplied version into the raw history. SnapshotTable.write assigns
sequences for callers of the snapshot API. -/
def Table.write (table : Table α) (row : Entry (Option α)) : Table α :=
  { table with memory := table.memory.union (.singleton row) }

def Table.flush (table : Table α) : Table α :=
  ⟨table.histories, .empty⟩

def Table.lookup (table : Table α) (key snapshot : UInt64) : Option α :=
  (across key snapshot table.histories).bind Entry.payload

def Table.range (table : Table α) (start stop snapshot : UInt64) : List (Entry (Option α)) :=
  (visibleRows (combined table.histories).rows snapshot Option.isSome).filter
    fun row => start ≤ row.key && row.key < stop

theorem Table.range_exact (table : Table α) (start stop snapshot : UInt64)
    (row : Entry (Option α)) :
    row ∈ table.range start stop snapshot ↔
      (across row.key snapshot table.histories = some row ∧ row.payload.isSome = true) ∧
      (start ≤ row.key ∧ row.key < stop) := by
  rw [Table.range, List.mem_filter, mem_visibleRows (combined table.histories).ordered,
    combined_winner]
  simp

theorem Table.range_ordered (table : Table α) (start stop snapshot : UInt64) :
    (table.range start stop snapshot).Pairwise (fun a b => a.key < b.key) :=
  (visibleRows_key_order (combined table.histories).ordered snapshot Option.isSome).filter _

theorem across_append_empty (runs : List (History α)) (key snapshot : UInt64) :
    across key snapshot (runs ++ [.empty]) = across key snapshot runs := by
  induction runs with
  | nil => rfl
  | cons a runs ih => simp only [List.cons_append, across, ih]

/-- The winning put with its original sequence, if the key is visible. -/
def Table.visibleEntry (table : Table α) (key snapshot : UInt64) : Option (Entry (Option α)) :=
  (across key snapshot table.histories).filter (fun row => row.payload.isSome)

theorem Table.lookup_eq_visibleEntry (table : Table α) (key snapshot : UInt64) :
    table.lookup key snapshot = (table.visibleEntry key snapshot).bind Entry.payload := by
  unfold Table.lookup Table.visibleEntry
  cases across key snapshot table.histories with
  | none => rfl
  | some row => cases h : row.payload <;> simp [Option.filter, h]

/-- A range is determined by the visible entries inside its half-open key interval. -/
theorem Table.range_congr {before after : Table α} (start stop snapshot : UInt64)
    (same : ∀ key, start ≤ key ∧ key < stop →
      after.visibleEntry key snapshot = before.visibleEntry key snapshot) :
    after.range start stop snapshot = before.range start stop snapshot := by
  have exactEntry (table : Table α) (row : Entry (Option α)) :
      row ∈ table.range start stop snapshot ↔
        table.visibleEntry row.key snapshot = some row ∧ (start ≤ row.key ∧ row.key < stop) := by
    rw [Table.range_exact, Table.visibleEntry, Option.filter_eq_some_iff]
  have afterOrdered := after.range_ordered start stop snapshot
  have beforeOrdered := before.range_ordered start stop snapshot
  have distinct {a b : Entry (Option α)} (lt : a.key < b.key) : a ≠ b :=
    fun eq => UInt64.lt_irrefl a.key (eq ▸ lt)
  have members (row : Entry (Option α)) :
      row ∈ after.range start stop snapshot ↔ row ∈ before.range start stop snapshot := by
    rw [exactEntry, exactEntry]
    constructor
    · rintro ⟨entry, within⟩
      exact ⟨(same row.key within).symm.trans entry, within⟩
    · rintro ⟨entry, within⟩
      exact ⟨(same row.key within).trans entry, within⟩
  have perm := (List.perm_ext_iff_of_nodup
    (afterOrdered.imp distinct) (beforeOrdered.imp distinct)).mpr members
  exact perm.eq_of_pairwise (fun _ _ _ _ lt gt => (UInt64.lt_asymm lt gt).elim)
    afterOrdered beforeOrdered

theorem Table.range_of_visibleEntry_eq {before after : Table α} (start stop snapshot : UInt64)
    (same : ∀ key, after.visibleEntry key snapshot = before.visibleEntry key snapshot) :
    after.range start stop snapshot = before.range start stop snapshot :=
  Table.range_congr start stop snapshot (fun key _ => same key)

private theorem Table.range_preserved {before after : Table α} (start stop snapshot : UInt64)
    (same : ∀ key, across key snapshot after.histories = across key snapshot before.histories) :
    after.range start stop snapshot = before.range start stop snapshot := by
  apply Table.range_of_visibleEntry_eq
  intro key
  unfold Table.visibleEntry
  rw [same key]

theorem Table.flush_lookup (table : Table α) (key snapshot : UInt64) :
    table.flush.lookup key snapshot = table.lookup key snapshot := by
  rw [Table.lookup, Table.lookup]
  exact congrArg (·.bind Entry.payload) (across_append_empty table.histories key snapshot)

theorem Table.flush_range (table : Table α) (start stop snapshot : UInt64) :
    table.flush.range start stop snapshot = table.range start stop snapshot :=
  Table.range_preserved start stop snapshot (fun key =>
    across_append_empty table.histories key snapshot)

/-- Compaction replaces an adjacent older/newer pair at the same publication precedence. -/
def compactPair (left right : History α) (floor : UInt64) : History α :=
  (left.union right).retain floor

theorem across_compact (older : List (History α)) (left right : History α)
    (newer : List (History α)) (key : UInt64) {floor snapshot : UInt64} (live : floor ≤ snapshot) :
    across key snapshot (older ++ compactPair left right floor :: newer) =
      across key snapshot (older ++ left :: right :: newer) := by
  induction older with
  | nil =>
    simp only [List.nil_append, across, compactPair, History.retain, History.union]
    rw [winner_retain _ key live, winner_union left.ordered right.ordered, newest_assoc]
  | cons a older ih => simp only [List.cons_append, across, ih]

theorem Table.compact_lookup (older : List (History α)) (left right : History α)
    (newer : List (History α)) (memory : History α) (key : UInt64)
    {floor snapshot : UInt64} (live : floor ≤ snapshot) :
    (Table.mk (older ++ compactPair left right floor :: newer) memory).lookup key snapshot =
      (Table.mk (older ++ left :: right :: newer) memory).lookup key snapshot := by
  simp only [Table.lookup, Table.histories, List.append_assoc, List.cons_append]
  rw [across_compact _ _ _ _ key live]

theorem Table.compact_range (older : List (History α)) (left right : History α)
    (newer : List (History α)) (memory : History α) (start stop : UInt64)
    {floor snapshot : UInt64} (live : floor ≤ snapshot) :
    (Table.mk (older ++ compactPair left right floor :: newer) memory).range start stop snapshot =
      (Table.mk (older ++ left :: right :: newer) memory).range start stop snapshot := by
  apply Table.range_preserved
  intro key
  simp only [Table.histories, List.append_assoc, List.cons_append]
  exact across_compact _ _ _ _ key live

def replaceSuffix (replace : List β → Option (List β)) :
    Nat → List β → Option (List β)
  | 0, rows => replace rows
  | _ + 1, [] => none
  | n + 1, head :: rows => (replaceSuffix replace n rows).map (head :: ·)

theorem replaceSuffix_spec_at {replace : List β → Option (List β)}
    {index : Nat} {rows result : List β} (changed : replaceSuffix replace index rows = some result) :
    ∃ prefixRows suffix replacement, prefixRows.length = index ∧ rows = prefixRows ++ suffix ∧
      result = prefixRows ++ replacement ∧ replace suffix = some replacement := by
  induction index generalizing rows result with
  | zero => exact ⟨[], rows, result, rfl, rfl, rfl, changed⟩
  | succ n ih =>
    cases rows with
    | nil => simp [replaceSuffix] at changed
    | cons row rows =>
      cases h : replaceSuffix replace n rows with
      | none => simp [replaceSuffix, h] at changed
      | some rest =>
        obtain ⟨prefixRows, suffix, replacement, length, old, new, valid⟩ := ih h
        have eq : row :: rest = result := by simpa [replaceSuffix, h] using changed
        exact ⟨row :: prefixRows, suffix, replacement, by simp [length],
          congrArg (row :: ·) old, eq.symm.trans (congrArg (row :: ·) new), valid⟩

theorem replaceSuffix_spec {replace : List β → Option (List β)}
    {index : Nat} {rows result : List β} (changed : replaceSuffix replace index rows = some result) :
    ∃ prefixRows suffix replacement, rows = prefixRows ++ suffix ∧
      result = prefixRows ++ replacement ∧ replace suffix = some replacement := by
  obtain ⟨prefixRows, suffix, replacement, _, original, updated, valid⟩ := replaceSuffix_spec_at changed
  exact ⟨prefixRows, suffix, replacement, original, updated, valid⟩

theorem replaceSuffix_map_success (interpret : β → γ)
    (replace : List β → Option (List β)) (spec : List γ → Option (List γ))
    (agrees : ∀ input output, replace input = some output →
      spec (input.map interpret) = some (output.map interpret))
    {index : Nat} {rows result : List β} (changed : replaceSuffix replace index rows = some result) :
    replaceSuffix spec index (rows.map interpret) = some (result.map interpret) := by
  induction index generalizing rows result with
  | zero => exact agrees _ _ changed
  | succ n ih =>
    cases rows with
    | nil => simp [replaceSuffix] at changed
    | cons head rest =>
      cases h : replaceSuffix replace n rest with
      | none => simp [replaceSuffix, h] at changed
      | some output =>
        have eq : head :: output = result := by simpa [replaceSuffix, h] using changed
        rw [← eq]
        simp [replaceSuffix, ih h]

def compactSuffix (floor : UInt64) : List (History α) → Option (List (History α))
  | a :: b :: rest => some (compactPair a b floor :: rest)
  | _ => none

/-- Compact the two adjacent runs starting at the given index. -/
def Table.compactAt (table : Table α) (index : Nat) (floor : UInt64) : Option (Table α) :=
  (replaceSuffix (compactSuffix floor) index table.runs).map fun runs => { table with runs }

theorem Table.compactAt_winner {table result : Table α} {index : Nat} {floor snapshot : UInt64}
    (changed : table.compactAt index floor = some result) (live : floor ≤ snapshot) (key : UInt64) :
    across key snapshot result.histories = across key snapshot table.histories := by
  unfold Table.compactAt at changed
  cases h : replaceSuffix (compactSuffix floor) index table.runs with
  | none => simp [h] at changed
  | some runs =>
    have eq : { table with runs := runs } = result := by simpa [h] using changed
    subst result
    have ⟨older, suffix, replacement, original, updated, valid⟩ := replaceSuffix_spec h
    rcases suffix with _ | ⟨left, _ | ⟨right, newer⟩⟩ <;> simp [compactSuffix] at valid
    subst replacement
    simp only [Table.histories, original, updated, List.append_assoc, List.cons_append]
    exact across_compact older left right (newer ++ [table.memory]) key live

/-- A handle belongs to one table's sequential history. IDs are never reused. -/
structure SnapshotHandle where
  private mk ::
  id : Nat
  deriving DecidableEq, Repr

structure SnapshotPin where
  handle : SnapshotHandle
  sequence : UInt64
  deriving DecidableEq, Repr

structure SnapshotPins where
  private mk ::
  floor : UInt64
  active : List SnapshotPin
  nextHandle : Nat
  safe : ∀ pin ∈ active, floor ≤ pin.sequence
  issued : ∀ pin ∈ active, pin.handle.id < nextHandle
  unique : (active.map SnapshotPin.handle).Nodup

def SnapshotPins.empty : SnapshotPins := ⟨0, [], 0, by simp, by simp, by simp⟩

/-- Allocate a fresh handle for a snapshot in the supported committed interval. -/
def SnapshotPins.acquire (pins : SnapshotPins) (committed snapshot : UInt64) :
    Option (SnapshotPin × SnapshotPins) :=
  if h : pins.floor ≤ snapshot ∧ snapshot ≤ committed then
    let pin : SnapshotPin := ⟨⟨pins.nextHandle⟩, snapshot⟩
    some (pin, ⟨pins.floor, pin :: pins.active, pins.nextHandle + 1,
      fun s mem => by
        rcases List.mem_cons.mp mem with rfl | tail
        · exact h.1
        · exact pins.safe s tail,
      fun s mem => by
        rcases List.mem_cons.mp mem with rfl | tail
        · exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt (pins.issued s tail),
      by
        rw [List.map_cons, List.nodup_cons]
        refine ⟨?_, pins.unique⟩
        intro mem
        obtain ⟨s, found, same⟩ := List.mem_map.mp mem
        have below := pins.issued s found
        have id := congrArg SnapshotHandle.id same
        exact (Nat.ne_of_lt below) id⟩)
  else none

theorem SnapshotPins.acquire_spec {pins next : SnapshotPins} {committed snapshot : UInt64}
    {pin : SnapshotPin} (h : pins.acquire committed snapshot = some (pin, next)) :
    pins.floor ≤ snapshot ∧ snapshot ≤ committed ∧ pin.sequence = snapshot ∧
      pin.handle.id = pins.nextHandle ∧ next.active = pin :: pins.active ∧
      next.nextHandle = pins.nextHandle + 1 ∧ next.floor = pins.floor := by
  unfold SnapshotPins.acquire at h
  split at h
  · rename_i valid
    cases h
    exact ⟨valid.1, valid.2, rfl, rfl, rfl, rfl, rfl⟩
  · contradiction

theorem SnapshotPins.acquire_iff (pins : SnapshotPins) (committed snapshot : UInt64) :
    (pins.acquire committed snapshot).isSome = true ↔
      pins.floor ≤ snapshot ∧ snapshot ≤ committed := by
  unfold SnapshotPins.acquire
  split <;> simp_all

/-- Release is idempotent. A handle removes only its own acquisition. -/
def SnapshotPins.release (pins : SnapshotPins) (handle : SnapshotHandle) : SnapshotPins :=
  let keep := fun pin : SnapshotPin => decide (pin.handle ≠ handle)
  have sub := List.filter_sublist (p := keep) (l := pins.active)
  ⟨pins.floor, pins.active.filter keep, pins.nextHandle,
    fun p h => pins.safe p (sub.subset h), fun p h => pins.issued p (sub.subset h),
    pins.unique.sublist (sub.map SnapshotPin.handle)⟩

@[simp] theorem SnapshotPins.mem_release (pins : SnapshotPins) (handle : SnapshotHandle)
    (pin : SnapshotPin) : pin ∈ (pins.release handle).active ↔
      pin ∈ pins.active ∧ pin.handle ≠ handle := by
  simp [SnapshotPins.release]

theorem SnapshotPins.release_idempotent (pins : SnapshotPins) (handle : SnapshotHandle) :
    (pins.release handle).release handle = pins.release handle := by
  unfold SnapshotPins.release
  simp only [List.filter_filter, Bool.and_self]

/-- Specification of the short-circuit traversal with one unit charged per pin comparison. -/
private def floorScan (next : UInt64) : List SnapshotPin → Bool × Nat
  | [] => (true, 0)
  | pin :: rest =>
    if next ≤ pin.sequence then
      let suffix := floorScan next rest
      (suffix.1, suffix.2 + 1)
    else (false, 1)

theorem SnapshotPins.floor_check_cost (next : UInt64) (active : List SnapshotPin) :
    (floorScan next active).1 = active.all (fun pin => next ≤ pin.sequence) ∧
      (floorScan next active).2 ≤ active.length := by
  induction active with
  | nil => simp [floorScan]
  | cons pin rest ih =>
    by_cases h : next ≤ pin.sequence <;> simp [floorScan, h, ih.1, ih.2]

def SnapshotPins.advance (pins : SnapshotPins) (next : UInt64) : Option SnapshotPins :=
  if good : (decide (pins.floor ≤ next) && pins.active.all (fun p => next ≤ p.sequence)) = true then
    some ⟨next, pins.active, pins.nextHandle,
      List.all_eq_true.mp (Bool.and_eq_true_iff.mp good).2 |> fun h p mem =>
        of_decide_eq_true (h p mem), pins.issued, pins.unique⟩
  else none

theorem SnapshotPins.advance_iff (pins : SnapshotPins) (next : UInt64) :
    (pins.advance next).isSome = true ↔
      pins.floor ≤ next ∧ ∀ pin ∈ pins.active, next ≤ pin.sequence := by
  have spec : (decide (pins.floor ≤ next) && pins.active.all (fun p => next ≤ p.sequence)) = true ↔
      pins.floor ≤ next ∧ ∀ pin ∈ pins.active, next ≤ pin.sequence := by
    constructor
    · intro h
      have both := Bool.and_eq_true_iff.mp h
      exact ⟨of_decide_eq_true both.1, fun p mem =>
        of_decide_eq_true (List.all_eq_true.mp both.2 p mem)⟩
    · intro h
      exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true h.1,
        List.all_eq_true.mpr (fun p mem => decide_eq_true (h.2 p mem))⟩
  unfold SnapshotPins.advance
  rw [← spec]
  split <;> simp_all

theorem SnapshotPins.advance_spec {pins result : SnapshotPins} {next : UInt64}
    (advanced : pins.advance next = some result) :
    pins.floor ≤ result.floor ∧ result.floor = next ∧ result.active = pins.active ∧
      result.nextHandle = pins.nextHandle ∧ ∀ pin ∈ pins.active, next ≤ pin.sequence := by
  have legal := (pins.advance_iff next).mp (by simp [advanced])
  unfold SnapshotPins.advance at advanced
  split at advanced
  · cases advanced
    exact ⟨legal.1, rfl, rfl, rfl, legal.2⟩
  · contradiction

theorem SnapshotPins.active_compaction (pins : SnapshotPins) {pin : SnapshotPin}
    (pinned : pin ∈ pins.active) (older : List (History α)) (left right : History α)
    (newer : List (History α)) (memory : History α) (key : UInt64) :
    (Table.mk (older ++ compactPair left right pins.floor :: newer) memory).lookup key pin.sequence =
      (Table.mk (older ++ left :: right :: newer) memory).lookup key pin.sequence :=
  Table.compact_lookup older left right newer memory key (pins.safe pin pinned)

private def keepVersion (key sequence : UInt64) (row : Entry (Option α)) : Bool :=
  !(row.key == key && row.sequence == sequence && row.payload.isNone)

/-- Purge a specified tombstone from the full logical history. -/
def History.purgeTombstone (history : History α) (key sequence : UInt64) : History α :=
  ⟨history.rows.filter (keepVersion key sequence), history.ordered.filter _⟩

private theorem winner_filter_kept {rows : List (Entry α)} {candidate : Entry α}
    {key snapshot : UInt64} (found : winner rows key snapshot = some candidate)
    (keep : Entry α → Bool) (kept : keep candidate = true) :
    winner (rows.filter keep) key snapshot = some candidate := by
  obtain ⟨visible, prefixRows, suffix, original, earlier⟩ := List.find?_eq_some_iff_append.mp found
  rw [winner, List.find?_filter]
  refine List.find?_eq_some_iff_append.mpr ⟨by simp [visible, kept], prefixRows, suffix, original, ?_⟩
  intro row mem
  have h := earlier row mem
  cases test : eligible key snapshot row <;> simp_all

/-- A tombstone can be purged if the complete remaining history still returns
absence at every supported snapshot at which that tombstone wins. -/
theorem History.purgeTombstone_preserves (history : History α) (key sequence floor : UInt64)
    (unmasked : ∀ snapshot, floor ≤ snapshot → ∀ row,
      winner history.rows key snapshot = some row → row.sequence = sequence → row.payload = none →
      Compaction.Model.read (history.purgeTombstone key sequence).rows key snapshot = none)
    (query snapshot : UInt64) (live : floor ≤ snapshot) :
    Compaction.Model.read (history.purgeTombstone key sequence).rows query snapshot =
      Compaction.Model.read history.rows query snapshot := by
  cases found : winner history.rows query snapshot with
  | none =>
    have remaining : winner (history.purgeTombstone key sequence).rows query snapshot = none := by
      apply List.find?_eq_none.mpr
      intro row mem
      exact List.find?_eq_none.mp found row (List.mem_filter.mp mem).1
    simp [Compaction.Model.read, found, remaining]
  | some row =>
    by_cases keep : keepVersion key sequence row = true
    · have remaining := winner_filter_kept found (keepVersion key sequence) keep
      simp [Compaction.Model.read, History.purgeTombstone, found, remaining]
    · have removed : row.key = key ∧ row.sequence = sequence ∧ row.payload = none := by
        simpa [keepVersion, and_assoc] using keep
      have queryEq : row.key = query := by
        have visible := List.find?_some found
        exact (by simpa [eligible] using visible : row.key = query ∧ row.sequence ≤ snapshot).1
      subst query
      have remaining := unmasked snapshot live row (removed.1 ▸ found) removed.2.1 removed.2.2
      have same := removed.1
      subst key
      rw [remaining, Compaction.Model.read, found]
      exact removed.2.2.symm

private def purgeSuffix (key sequence : UInt64) :
    List (History α) → Option (List (History α))
  | run :: rest => some (run.purgeTombstone key sequence :: rest)
  | [] => none

/-- Proposal for replacing one run by the same run with a tombstone removed. -/
def Table.purgeCandidate (table : Table α) (index : Nat) (key sequence : UInt64) :
    Option (Table α) :=
  (replaceSuffix (purgeSuffix key sequence) index table.runs).map fun runs => { table with runs }

private theorem History.purge_other_key (run : History α) (key sequence query snapshot : UInt64)
    (different : query ≠ key) :
    winner (run.purgeTombstone key sequence).rows query snapshot = winner run.rows query snapshot := by
  simp only [History.purgeTombstone, winner, List.find?_filter]
  congr 1
  funext row
  by_cases found : row.key = query
  · simp [eligible, keepVersion, found, different]
  · simp [eligible, found]

theorem Table.purgeCandidate_other_key {table result : Table α} {index : Nat}
    {key sequence : UInt64} (candidate : table.purgeCandidate index key sequence = some result)
    (query snapshot : UInt64) (different : query ≠ key) :
    across query snapshot result.histories = across query snapshot table.histories := by
  unfold Table.purgeCandidate at candidate
  cases h : replaceSuffix (purgeSuffix key sequence) index table.runs with
  | none => simp [h] at candidate
  | some runs =>
    have eq : { table with runs := runs } = result := by simpa [h] using candidate
    subst result
    have ⟨older, suffix, replacement, original, updated, valid⟩ := replaceSuffix_spec h
    cases suffix with
    | nil => simp [purgeSuffix] at valid
    | cons run newer =>
      simp [purgeSuffix] at valid
      subst replacement
      simp only [Table.histories, original, updated, List.append_assoc, List.cons_append]
      clear candidate original updated h runs
      induction older with
      | nil => simp [across, run.purge_other_key key sequence query snapshot different]
      | cons head older ih => simp only [List.cons_append, across, ih]

end Alvoki.Sequential
