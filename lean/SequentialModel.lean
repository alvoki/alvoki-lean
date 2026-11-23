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

private theorem across_append_empty (runs : List (History α)) (key snapshot : UInt64) :
    across key snapshot (runs ++ [.empty]) = across key snapshot runs := by
  induction runs with
  | nil => rfl
  | cons a runs ih => simp only [List.cons_append, across, ih]

private theorem Table.range_preserved {before after : Table α} (start stop snapshot : UInt64)
    (same : ∀ key, across key snapshot after.histories = across key snapshot before.histories) :
    after.range start stop snapshot = before.range start stop snapshot := by
  unfold Table.range
  rw [visibleRows_congr (combined after.histories).ordered (combined before.histories).ordered
    snapshot Option.isSome (fun key => by simpa only [combined_winner] using same key)]

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

/-- Each successful acquisition adds a pin. Multiple readers may pin the same sequence. -/
structure SnapshotPins where
  floor : UInt64
  active : List UInt64
  safe : ∀ snap ∈ active, floor ≤ snap

def SnapshotPins.acquire (pins : SnapshotPins) (snapshot : UInt64) : Option SnapshotPins :=
  if h : pins.floor ≤ snapshot then
    some ⟨pins.floor, snapshot :: pins.active, fun s mem => by
      rcases List.mem_cons.mp mem with rfl | tail
      · exact h
      · exact pins.safe s tail⟩
  else none

/-- On release only one occurrence is removed. -/
def SnapshotPins.release (pins : SnapshotPins) (snapshot : UInt64) : SnapshotPins :=
  ⟨pins.floor, pins.active.erase snapshot, fun s mem => pins.safe s (List.mem_of_mem_erase mem)⟩

def SnapshotPins.advance (pins : SnapshotPins) (next : UInt64) : Option SnapshotPins :=
  if good : pins.floor ≤ next ∧ ∀ s ∈ pins.active, next ≤ s then
    some ⟨next, pins.active, good.2⟩
  else none

theorem SnapshotPins.advance_spec {pins result : SnapshotPins} {next : UInt64}
    (advanced : pins.advance next = some result) :
    pins.floor ≤ result.floor ∧ result.floor = next ∧ result.active = pins.active ∧
      ∀ snap ∈ pins.active, next ≤ snap := by
  unfold SnapshotPins.advance at advanced
  split at advanced
  · rename_i good
    injection advanced with same
    subst result
    exact ⟨good.1, rfl, rfl, good.2⟩
  · contradiction

theorem SnapshotPins.active_compaction (pins : SnapshotPins) {snapshot : UInt64}
    (pinned : snapshot ∈ pins.active) (older : List (History α)) (left right : History α)
    (newer : List (History α)) (memory : History α) (key : UInt64) :
    (Table.mk (older ++ compactPair left right pins.floor :: newer) memory).lookup key snapshot =
      (Table.mk (older ++ left :: right :: newer) memory).lookup key snapshot :=
  Table.compact_lookup older left right newer memory key (pins.safe snapshot pinned)

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

end Alvoki.Sequential
