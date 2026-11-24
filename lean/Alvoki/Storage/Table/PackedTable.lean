import Alvoki.Storage.Table.CompactionRead
import Alvoki.Storage.Table.MemTable
import Alvoki.Storage.Table.SnapshotTable

namespace Alvoki.Storage
open Alvoki.Compaction (CheckedRun inRange)
open Alvoki.Compaction.Model
open Alvoki.Sequential (History SnapshotHandle SnapshotPin SnapshotPins SnapshotTable)

/-- The in-memory engine stores immutable packed v3 runs and an ordered memtable. -/
structure PackedTable where
  private mk ::
  runs : List CheckedRun
  private memtable : MemTable
  committed : UInt64
  pins : SnapshotPins

/-- The logical pending history. Native point and range reads use the
memtable's own operations. -/
def PackedTable.memory (state : PackedTable) : History UInt64 := state.memtable.history

def PackedTable.memoryIsEmpty (state : @& PackedTable) : Bool := state.memtable.isEmpty

theorem PackedTable.memoryIsEmpty_spec (state : PackedTable) :
    state.memoryIsEmpty = state.memory.rows.isEmpty :=
  state.memtable.isEmpty_spec

def PackedTable.emptyWithMemTable (kind : MemTable.Kind) : PackedTable :=
  ⟨[], MemTable.emptyWith kind, 0, .empty⟩

def PackedTable.empty : PackedTable := ⟨[], .empty, 0, .empty⟩


/-- Every stored row belongs at or below the table's committed sequence. -/
structure PackedTable.RowBounds (state : PackedTable) : Prop where
  runs : ∀ run ∈ state.runs, ∀ row ∈ run.history.rows, row.sequence ≤ state.committed
  memory : ∀ row ∈ state.memory.rows, row.sequence ≤ state.committed

theorem PackedTable.empty_rowBounds : PackedTable.empty.RowBounds := by
  constructor <;> simp [PackedTable.empty, PackedTable.memory, History.empty]

/-- Open a checkpoint with a fresh pin registry. All loaded versions must be
at or below the checkpoint watermark. -/
def PackedTable.restore (runs : List CheckedRun) (committed floor : UInt64) :
    Option PackedTable :=
  if floor ≤ committed && runs.all (fun run =>
      run.history.rows.all (fun row => row.sequence ≤ committed)) then
    (SnapshotPins.empty.advance floor).map (fun pins => ⟨runs, .empty, committed, pins⟩)
  else none

theorem PackedTable.restore_spec {runs : List CheckedRun} {committed floor : UInt64}
    {state : PackedTable} (opened : restore runs committed floor = some state) :
    state.runs = runs ∧ state.memory = History.empty ∧ state.committed = committed ∧
      state.pins.floor = floor ∧ state.pins.active = [] := by
  unfold restore at opened
  split at opened
  · obtain ⟨pins, advanced, rfl⟩ := Option.map_eq_some_iff.mp opened
    have spec := SnapshotPins.advance_spec advanced
    exact ⟨rfl, rfl, rfl, spec.2.1, spec.2.2.1⟩
  · contradiction

theorem PackedTable.restore_rowBounds {runs : List CheckedRun} {committed floor : UInt64}
    {state : PackedTable} (opened : restore runs committed floor = some state) : state.RowBounds := by
  unfold restore at opened
  split at opened
  · rename_i accepted
    obtain ⟨pins, _, rfl⟩ := Option.map_eq_some_iff.mp opened
    have bounded := (Bool.and_eq_true_iff.mp accepted).2
    exact ⟨fun run mem row inside => of_decide_eq_true
      (List.all_eq_true.mp (List.all_eq_true.mp bounded run mem) row inside), by simp [PackedTable.memory, History.empty]⟩
  · contradiction

theorem PackedTable.restore_complete (runs : List CheckedRun) (committed floor : UInt64)
    (validFloor : floor ≤ committed)
    (bounded : ∀ run ∈ runs, ∀ row ∈ run.history.rows, row.sequence ≤ committed) :
    ∃ state, restore runs committed floor = some state := by
  have validRuns : (runs.all (fun run => run.history.rows.all
      (fun row => row.sequence ≤ committed))) = true := by
    exact List.all_eq_true.mpr fun run mem => List.all_eq_true.mpr fun row member =>
      decide_eq_true (bounded run mem row member)
  have moved : (SnapshotPins.empty.advance floor).isSome = true := by
    apply (SnapshotPins.advance_iff _ _).mpr
    simp [SnapshotPins.empty, UInt64.le_iff_toNat_le]
  cases h : SnapshotPins.empty.advance floor with
  | none => simp [h] at moved
  | some pins => simp [restore, validFloor, validRuns, h]

/-- Logical view for proofs and fixture oracles. -/
def PackedTable.describe (state : PackedTable) : Sequential.Table UInt64 :=
  ⟨state.runs.map CheckedRun.history, state.memory⟩

/-- Restart replaces the pin registry while leaving the data and watermarks intact. -/
structure PackedTable.SameData (left right : PackedTable) : Prop where
  runs : left.runs = right.runs
  memory : left.memory = right.memory
  committed : left.committed = right.committed
  floor : left.pins.floor = right.pins.floor

theorem PackedTable.SameData.describe {left right : PackedTable} (same : left.SameData right) :
    left.describe = right.describe := by
  simp only [PackedTable.describe, same.runs, same.memory]

theorem PackedTable.SameData.rowBounds {left right : PackedTable} (same : left.SameData right)
    (bounded : right.RowBounds) : left.RowBounds := by
  constructor
  · rw [same.runs, same.committed]
    exact bounded.runs
  · rw [same.memory, same.committed]
    exact bounded.memory

theorem PackedTable.restore_sameData {state restored : PackedTable}
    (flushed : state.memory = History.empty)
    (opened : restore state.runs state.committed state.pins.floor = some restored) :
    restored.SameData state :=
  let ⟨runs, memory, committed, floor, _⟩ := restore_spec opened
  ⟨runs, memory.trans flushed.symm, committed, floor⟩

structure PackedTable.Refines (state : PackedTable) (model : SnapshotTable UInt64) : Prop where
  table : state.describe = model.table
  committed : state.committed = model.committed
  pins : state.pins = model.pins

theorem PackedTable.emptyWithMemTable_refines (kind : MemTable.Kind) :
    (PackedTable.emptyWithMemTable kind).Refines (SnapshotTable.empty : SnapshotTable UInt64) := by
  refine ⟨?_, rfl, rfl⟩
  simp [PackedTable.emptyWithMemTable, PackedTable.describe, PackedTable.memory,
    SnapshotTable.empty]

theorem PackedTable.empty_refines : PackedTable.empty.Refines (SnapshotTable.empty : SnapshotTable UInt64) :=
  ⟨rfl, rfl, rfl⟩

def PackedTable.write (state : PackedTable) (key : UInt64) (value : Option UInt64) : Option PackedTable :=
  if state.committed.toNat + 1 < UInt64.size then
    let sequence := UInt64.ofNat (state.committed.toNat + 1)
    some { state with committed := sequence, memtable := state.memtable.insert ⟨key, sequence, value⟩ }
  else none

theorem PackedTable.RowBounds.write {state next : PackedTable} {key : UInt64} {value : Option UInt64}
    (bounded : state.RowBounds) (written : state.write key value = some next) : next.RowBounds := by
  unfold PackedTable.write at written
  split at written
  · rename_i fits
    cases written
    have grows : state.committed ≤ UInt64.ofNat (state.committed.toNat + 1) := by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' fits]
      exact Nat.le_add_right _ _
    refine ⟨fun run mem row inside => UInt64.le_trans (bounded.runs run mem row inside) grows, ?_⟩
    intro row inside
    simp only [PackedTable.memory, MemTable.history_insert] at inside
    change row ∈ union state.memory.rows (History.singleton _).rows at inside
    rcases mem_union inside with old | added
    · exact UInt64.le_trans (bounded.memory row old) grows
    · cases List.mem_singleton.mp added
      exact UInt64.le_refl _
  · contradiction

theorem PackedTable.SameData.write {left right next : PackedTable} (same : left.SameData right)
    {key : UInt64} {value : Option UInt64} (written : right.write key value = some next) :
    ∃ result, left.write key value = some result ∧ result.SameData next := by
  unfold PackedTable.write at written ⊢
  rw [same.committed]
  split at written
  · rename_i fits
    rw [ite_eq_left fits]
    cases written
    refine ⟨_, rfl, ⟨same.runs, ?_, rfl, same.floor⟩⟩
    simp only [PackedTable.memory, MemTable.history_insert]
    rw [← PackedTable.memory, ← PackedTable.memory, same.memory]
  · contradiction

def PackedTable.acquireAt (state : PackedTable) (snapshot : UInt64) :
    Option (SnapshotPin × PackedTable) :=
  (state.pins.acquire state.committed snapshot).map fun (pin, pins) => (pin, { state with pins })

/-- Acquisition activates a pin at the requested sequence and changes only the pin registry. -/
structure PackedTable.AcquiredAt (before after : PackedTable) (snapshot : UInt64)
    (pin : SnapshotPin) : Prop where
  sequence : pin.sequence = snapshot
  active : pin ∈ after.pins.active
  sameData : after.SameData before

theorem PackedTable.acquireAt_spec {before after : PackedTable} {snapshot : UInt64}
    {pin : SnapshotPin} (acquired : before.acquireAt snapshot = some (pin, after)) :
    before.AcquiredAt after snapshot pin := by
  obtain ⟨⟨_, pins⟩, recorded, equal⟩ := Option.map_eq_some_iff.mp acquired
  cases equal
  obtain ⟨_, _, sequence, _, active, _, floor⟩ := SnapshotPins.acquire_spec recorded
  exact ⟨sequence, active ▸ List.mem_cons_self .., ⟨rfl, rfl, rfl, floor⟩⟩

theorem PackedTable.RowBounds.acquireAt {state after : PackedTable} {snapshot : UInt64}
    {pin : SnapshotPin} (bounded : state.RowBounds) (acquired : state.acquireAt snapshot = some (pin, after)) :
    after.RowBounds :=
  (PackedTable.acquireAt_spec acquired).sameData.rowBounds bounded

def PackedTable.acquire (state : PackedTable) : Option (SnapshotPin × PackedTable) :=
  state.acquireAt state.committed

def PackedTable.release (state : PackedTable) (handle : SnapshotHandle) : PackedTable :=
  { state with pins := state.pins.release handle }

theorem PackedTable.RowBounds.release {state : PackedTable} (bounded : state.RowBounds)
    (handle : SnapshotHandle) : (state.release handle).RowBounds :=
  ⟨bounded.runs, bounded.memory⟩

def PackedTable.advanceFloor (state : PackedTable) (floor : UInt64) : Option PackedTable :=
  if floor ≤ state.committed then (state.pins.advance floor).map fun pins => { state with pins }
  else none

theorem PackedTable.RowBounds.advanceFloor {state after : PackedTable} {floor : UInt64}
    (bounded : state.RowBounds) (advanced : state.advanceFloor floor = some after) : after.RowBounds := by
  unfold PackedTable.advanceFloor at advanced
  split at advanced
  · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp advanced
    exact ⟨bounded.runs, bounded.memory⟩
  · contradiction

def PackedTable.flush (state : PackedTable) : Except String PackedTable :=
  match CheckedRun.ofHistory state.memory with
  | .ok run => .ok { state with runs := state.runs ++ [run], memtable := state.memtable.clear }
  | .error message => .error message

theorem PackedTable.flush_memory_empty {state after : PackedTable}
    (flushed : state.flush = .ok after) : after.memory = History.empty := by
  unfold PackedTable.flush at flushed
  cases encoded : CheckedRun.ofHistory state.memory <;> simp [encoded] at flushed
  subst after
  exact state.memtable.history_clear

theorem PackedTable.RowBounds.flush {state after : PackedTable}
    (bounded : state.RowBounds) (flushed : state.flush = .ok after) : after.RowBounds := by
  unfold PackedTable.flush at flushed
  cases encoded : CheckedRun.ofHistory state.memory with
  | error message => simp [encoded] at flushed
  | ok run =>
    rw [encoded] at flushed
    cases flushed
    refine ⟨?_, by simp [PackedTable.memory, History.empty]⟩
    intro source member row inside
    rcases List.mem_append.mp member with old | added
    · exact bounded.runs source old row inside
    · obtain rfl := List.mem_singleton.mp added
      rw [CheckedRun.ofHistory_spec encoded] at inside
      exact bounded.memory row inside

private def compactSuffix (floor : UInt64) : List CheckedRun → Option (List CheckedRun)
  | left :: right :: tail =>
    match left.compact right floor with
    | .ok run => some (run :: tail)
    | .error _ => none
  | _ => none

def PackedTable.compact (state : PackedTable) (index : Nat) : Option PackedTable :=
  (Sequential.replaceSuffix (compactSuffix state.pins.floor) index state.runs).map fun runs =>
    { state with runs }

theorem PackedTable.RowBounds.compact {state after : PackedTable} {index : Nat}
    (bounded : state.RowBounds) (compacted : state.compact index = some after) : after.RowBounds := by
  unfold PackedTable.compact at compacted
  obtain ⟨runs, accepted, rfl⟩ := Option.map_eq_some_iff.mp compacted
  obtain ⟨older, suffix, replacement, original, updated, valid⟩ := Sequential.replaceSuffix_spec accepted
  refine ⟨?_, bounded.memory⟩
  rcases suffix with _ | ⟨left, _ | ⟨right, tail⟩⟩ <;> simp [compactSuffix] at valid
  cases merged : left.compact right state.pins.floor with
  | error message => simp [merged] at valid
  | ok run =>
    have replacements : run :: tail = replacement := by simpa [merged] using valid
    intro source member row inside
    rw [updated, ← replacements] at member
    rcases List.mem_append.mp member with old | rest
    · exact bounded.runs source (by rw [original]; exact List.mem_append_left _ old) row inside
    · rcases List.mem_cons.mp rest with rfl | other
      · rw [CheckedRun.compact_spec merged] at inside
        change row ∈ retain (union left.history.rows right.history.rows) state.pins.floor at inside
        rcases mem_union ((retainFrom_sublist _ _ _ _).subset inside) with inLeft | inRight
        · exact bounded.runs left (by simp [original]) row inLeft
        · exact bounded.runs right (by simp [original]) row inRight
      · exact bounded.runs source (by simp [original, other]) row inside

private def winnerAcross (key snapshot : UInt64) (memory : MemTable) :
    List CheckedRun → Option (Entry (Option UInt64))
  | [] => memory.lookup key snapshot
  | run :: tail => newest (run.lookupEntry key snapshot) (winnerAcross key snapshot memory tail)

private theorem winnerAcross_eq (key snapshot : UInt64) (memory : MemTable)
    (runs : List CheckedRun) :
    winnerAcross key snapshot memory runs =
      Sequential.across key snapshot (runs.map CheckedRun.history ++ [memory.history]) := by
  induction runs with
  | nil =>
    simp only [winnerAcross, List.map_nil, List.nil_append, Sequential.across, MemTable.lookup_spec]
    cases winner memory.history.rows key snapshot <;> rfl
  | cons run rest ih =>
    simp only [winnerAcross, List.map_cons, List.cons_append, Sequential.across, ih, run.lookupEntry_eq]

def PackedTable.lookupAt (state : @& PackedTable) (key snapshot : UInt64) : Option UInt64 :=
  (winnerAcross key snapshot state.memtable state.runs).bind Entry.payload

theorem PackedTable.lookupAt_eq (state : PackedTable) (key snapshot : UInt64) :
    state.lookupAt key snapshot = state.describe.lookup key snapshot := by
  unfold PackedTable.lookupAt
  rw [winnerAcross_eq]
  rfl

def PackedTable.lookup (state : @& PackedTable) (handle : SnapshotHandle)
    (key : UInt64) : Option (Option UInt64) :=
  (state.pins.find handle).map fun pin => state.lookupAt key pin.sequence

theorem PackedTable.lookup_refines {state : PackedTable} {model : SnapshotTable UInt64}
    (refinement : state.Refines model) (handle : SnapshotHandle) (key : UInt64) :
    state.lookup handle key = model.lookup handle key := by
  simp only [PackedTable.lookup, SnapshotTable.lookup, refinement.pins,
    PackedTable.lookupAt_eq, refinement.table]

private abbrev clip := MemTableContract.clip

private theorem winner_clip (history : History UInt64) (start stop key snapshot : UInt64)
    (within : start ≤ key ∧ key < stop) :
    winner (clip history start stop).rows key snapshot = winner history.rows key snapshot := by
  change (history.rows.filter (inRange start stop)).find? (eligible key snapshot) = _
  unfold winner
  simp only [List.find?_filter]
  have agrees : (fun row : Entry (Option UInt64) =>
      decide (inRange start stop row ∧ eligible key snapshot row)) = eligible key snapshot := by
    funext row
    by_cases matchesKey : row.key = key
    · simp [inRange, eligible, matchesKey, within.1, within.2]
    · have no : (row.key == key) = false := Bool.eq_false_iff.mpr (fun h => matchesKey (beq_iff_eq.mp h))
      simp [eligible, no]
  rw [agrees]

private theorem across_clip (runs : List (History UInt64)) (start stop key snapshot : UInt64)
    (within : start ≤ key ∧ key < stop) :
    Sequential.across key snapshot (runs.map fun run => clip run start stop) =
      Sequential.across key snapshot runs := by
  induction runs with
  | nil => rfl
  | cons run rest ih =>
    simp only [List.map_cons, Sequential.across, ih, winner_clip _ _ _ _ _ within]

private def rangeSources (state : PackedTable) (start stop : UInt64) : Sequential.Table UInt64 :=
  ⟨state.runs.map (fun run => run.rangeHistory start stop), state.memtable.range start stop⟩

/-- Merge only the requested key interval from each source and return its visible puts. -/
def PackedTable.rangeAt (state : @& PackedTable) (start stop snapshot : UInt64) :
    List (Entry (Option UInt64)) :=
  (rangeSources state start stop).range start stop snapshot

theorem PackedTable.rangeAt_eq (state : PackedTable) (start stop snapshot : UInt64) :
    state.rangeAt start stop snapshot = state.describe.range start stop snapshot := by
  unfold PackedTable.rangeAt
  apply Sequential.Table.range_congr
  intro key within
  have hist (run : CheckedRun) : run.rangeHistory start stop = clip run.history start stop := by
    apply History.ext_rows
    exact run.rangeEntries_eq start stop
  have sources : (rangeSources state start stop).histories =
      (state.describe.histories.map fun run => clip run start stop) := by
    unfold rangeSources PackedTable.describe Sequential.Table.histories
    simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, MemTable.range_spec, PackedTable.memory]
    rw [List.map_congr_left]
    intro run _
    exact hist run
  rw [Sequential.Table.visibleEntry, Sequential.Table.visibleEntry, sources,
    across_clip _ start stop key snapshot within]

def PackedTable.range (state : @& PackedTable) (handle : SnapshotHandle)
    (start stop : UInt64) : Option (List (Entry (Option UInt64))) :=
  (state.pins.find handle).map fun pin => state.rangeAt start stop pin.sequence

theorem PackedTable.range_refines {state : PackedTable} {model : SnapshotTable UInt64}
    (refinement : state.Refines model) (handle : SnapshotHandle) (start stop : UInt64) :
    state.range handle start stop = model.range handle start stop := by
  simp only [PackedTable.range, SnapshotTable.range, refinement.pins,
    PackedTable.rangeAt_eq, refinement.table]

private theorem PackedTable.acquireAt_reads {before after : PackedTable} {snapshot : UInt64}
    {pin : SnapshotPin} (acquired : before.acquireAt snapshot = some (pin, after)) :
    (∀ key, after.lookup pin.handle key = some (before.describe.lookup key snapshot)) ∧
    (∀ start stop, after.range pin.handle start stop =
      some (before.describe.range start stop snapshot)) := by
  have spec := PackedTable.acquireAt_spec acquired
  have found := after.pins.find_of_mem spec.active
  constructor
  · intro key
    simp only [PackedTable.lookup, found, Option.map_some, spec.sequence, PackedTable.lookupAt_eq,
      spec.sameData.describe]
  · intro start stop
    simp only [PackedTable.range, found, Option.map_some, spec.sequence, PackedTable.rangeAt_eq,
      spec.sameData.describe]

/-- Reacquiring a retained snapshot after replay reads the reference data,
regardless of the identifiers issued in the old pin registry. -/
theorem PackedTable.SameData.acquireAt_reads {reopened reference : PackedTable}
    (same : reopened.SameData reference) {snapshot : UInt64}
    (retained : reference.pins.floor ≤ snapshot) (committed : snapshot ≤ reference.committed) :
    ∃ pin after, reopened.acquireAt snapshot = some (pin, after) ∧
      (∀ key, after.lookup pin.handle key = some (reference.describe.lookup key snapshot)) ∧
      (∀ start stop, after.range pin.handle start stop =
        some (reference.describe.range start stop snapshot)) := by
  have available : (reopened.acquireAt snapshot).isSome = true := by
    rw [PackedTable.acquireAt, Option.isSome_map, SnapshotPins.acquire_iff, same.floor, same.committed]
    exact ⟨retained, committed⟩
  obtain ⟨⟨pin, after⟩, acquired⟩ := Option.isSome_iff_exists.mp available
  exact ⟨pin, after, acquired, by
    simpa only [same.describe] using PackedTable.acquireAt_reads acquired⟩

theorem PackedTable.write_refines {before after : PackedTable} {model : SnapshotTable UInt64}
    {key : UInt64} {value : Option UInt64} (same : before.Refines model)
    (written : before.write key value = some after) :
    ∃ result, model.write key value = some result ∧ after.Refines result := by
  unfold PackedTable.write at written
  split at written
  · rename_i fits
    cases written
    have bound : model.committed.toNat + 1 < UInt64.size := same.committed ▸ fits
    have success := (model.write_iff key value).mpr bound
    cases accepted : model.write key value with
    | none => simp [accepted] at success
    | some result =>
      have ⟨sequence, pins, table⟩ := SnapshotTable.write_spec accepted
      have clock : UInt64.ofNat (before.committed.toNat + 1) = result.committed := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_ofNat_of_lt' fits, sequence, same.committed]
      refine ⟨result, rfl, ⟨?_, clock, same.pins.trans pins.symm⟩⟩
      rw [table, ← same.table]
      simp only [PackedTable.describe, Sequential.Table.write, clock, PackedTable.memory, MemTable.history_insert]
  · contradiction

theorem PackedTable.release_refines {state : PackedTable} {model : SnapshotTable UInt64}
    (same : state.Refines model) (handle : SnapshotHandle) :
    (state.release handle).Refines (model.release handle) :=
  ⟨same.table, same.committed, congrArg (·.release handle) same.pins⟩

theorem PackedTable.acquireAt_refines {before after : PackedTable} {model : SnapshotTable UInt64}
    {pin : SnapshotPin} {snapshot : UInt64} (same : before.Refines model)
    (acquired : before.acquireAt snapshot = some (pin, after)) :
    ∃ result, model.acquireAt snapshot = some (pin, result) ∧ after.Refines result := by
  unfold PackedTable.acquireAt at acquired
  obtain ⟨⟨selected, pins⟩, choice, eq⟩ := Option.map_eq_some_iff.mp acquired
  cases eq
  have modelChoice : model.pins.acquire model.committed snapshot = some (pin, pins) := by
    rwa [← same.pins, ← same.committed]
  unfold SnapshotTable.acquireAt
  split
  · rename_i missing
    rw [modelChoice] at missing
    contradiction
  · rename_i found
    rw [modelChoice] at found
    cases found
    exact ⟨_, rfl, ⟨same.table, same.committed, rfl⟩⟩

theorem PackedTable.advanceFloor_refines {before after : PackedTable} {model : SnapshotTable UInt64}
    {floor : UInt64} (same : before.Refines model)
    (advanced : before.advanceFloor floor = some after) :
    ∃ result, model.advanceFloor floor = some result ∧ after.Refines result := by
  unfold PackedTable.advanceFloor at advanced
  split at advanced
  · rename_i within
    obtain ⟨pins, newPins, rfl⟩ := Option.map_eq_some_iff.mp advanced
    have bound : floor ≤ model.committed := same.committed ▸ within
    have moved : model.pins.advance floor = some pins := by rwa [← same.pins]
    unfold SnapshotTable.advanceFloor
    rw [dite_eq_left bound]
    split
    · rename_i missing
      rw [moved] at missing
      contradiction
    · rename_i found
      rw [moved] at found
      cases found
      exact ⟨_, rfl, ⟨same.table, same.committed, rfl⟩⟩
  · contradiction

theorem PackedTable.flush_refines {before after : PackedTable} {model : SnapshotTable UInt64}
    (same : before.Refines model) (flushed : before.flush = .ok after) :
    after.Refines model.flush := by
  unfold PackedTable.flush at flushed
  cases h : CheckedRun.ofHistory before.memory with
  | error message => simp [h] at flushed
  | ok run =>
    rw [h] at flushed
    cases flushed
    have hist := CheckedRun.ofHistory_spec h
    refine ⟨?_, same.committed, same.pins⟩
    simp only [PackedTable.describe, SnapshotTable.flush, Sequential.Table.flush, ← same.table,
      Sequential.Table.histories, List.map_append, List.map_cons, List.map_nil, hist,
      PackedTable.memory, MemTable.history_clear]

private theorem compactSuffix_refines (floor : UInt64) (input output : List CheckedRun)
    (success : compactSuffix floor input = some output) :
    Sequential.compactSuffix floor (input.map CheckedRun.history) = some (output.map CheckedRun.history) := by
  rcases input with _ | ⟨left, _ | ⟨right, tail⟩⟩ <;> simp [compactSuffix] at success
  cases compacted : left.compact right floor with
  | error message => simp [compacted] at success
  | ok run =>
    have target : run :: tail = output := by simpa [compacted] using success
    rw [← target]
    simp only [List.map_cons, Sequential.compactSuffix, CheckedRun.compact_spec compacted]

theorem PackedTable.compact_refines {before after : PackedTable} {model : SnapshotTable UInt64}
    {index : Nat} (same : before.Refines model) (compacted : before.compact index = some after) :
    ∃ result, model.compact index = some result ∧ after.Refines result := by
  unfold PackedTable.compact at compacted
  obtain ⟨runs, accepted, rfl⟩ := Option.map_eq_some_iff.mp compacted
  have mapped := Sequential.replaceSuffix_map_success CheckedRun.history
    (compactSuffix before.pins.floor) (Sequential.compactSuffix before.pins.floor)
    (compactSuffix_refines before.pins.floor) accepted
  have modelResult : Sequential.replaceSuffix (Sequential.compactSuffix model.pins.floor) index
      model.table.runs = some (runs.map CheckedRun.history) := by
    simpa only [← same.pins, ← same.table, PackedTable.describe] using mapped
  unfold SnapshotTable.compact Sequential.Table.compactAt
  rw [modelResult]
  have memory : before.memory = model.table.memory := congrArg Sequential.Table.memory same.table
  refine ⟨_, rfl, ⟨?_, same.committed, same.pins⟩⟩
  change Sequential.Table.mk (runs.map CheckedRun.history) before.memory = _
  exact congrArg (Sequential.Table.mk (runs.map CheckedRun.history)) memory

private def retainRunSuffix (floor : UInt64) : List CheckedRun → Option (List CheckedRun)
  | run :: tail => (run.retainVersions floor).toOption.map (· :: tail)
  | [] => none

/-- Rewrite one run at the table's current retention floor. The original
position in the oldest-to-newest run order and the pin registry stay intact. -/
def PackedTable.retainRunVersions (state : PackedTable) (index : Nat) : Option PackedTable :=
  (Sequential.replaceSuffix (retainRunSuffix state.pins.floor) index state.runs).map fun runs =>
    { state with runs }

theorem PackedTable.retainRunVersions_spec {before after : PackedTable} {index : Nat}
    (retained : before.retainRunVersions index = some after) :
    after.memory = before.memory ∧ after.committed = before.committed ∧ after.pins = before.pins ∧
      ∃ older source output newer, older.length = index ∧ before.runs = older ++ source :: newer ∧
        after.runs = older ++ output :: newer ∧ source.retainVersions before.pins.floor = .ok output ∧
        output.history = source.history.retain before.pins.floor := by
  unfold PackedTable.retainRunVersions at retained
  obtain ⟨runs, changed, rfl⟩ := Option.map_eq_some_iff.mp retained
  obtain ⟨older, suffix, replacement, length, original, updated, valid⟩ := Sequential.replaceSuffix_spec_at changed
  cases suffix with
  | nil => simp [retainRunSuffix] at valid
  | cons source newer =>
    cases written : source.retainVersions before.pins.floor with
    | error => simp [retainRunSuffix, written, Except.toOption] at valid
    | ok output =>
      have replaced : output :: newer = replacement := by
        simpa [retainRunSuffix, written, Except.toOption] using valid
      exact ⟨rfl, rfl, rfl, older, source, output, newer, length, original,
        updated.trans (congrArg (older ++ ·) replaced.symm), written, CheckedRun.retainVersions_spec written⟩

theorem PackedTable.RowBounds.retainRunVersions {before after : PackedTable} {index : Nat}
    (bounded : before.RowBounds) (retained : before.retainRunVersions index = some after) :
    after.RowBounds := by
  obtain ⟨memory, clock, _, older, source, output, newer, _, original, updated, _, history⟩ :=
    PackedTable.retainRunVersions_spec retained
  constructor
  · intro run member row inside
    rw [updated] at member
    rw [clock]
    rcases List.mem_append.mp member with earlier | remaining
    · exact bounded.runs run (by rw [original]; exact List.mem_append_left _ earlier) row inside
    · rcases List.mem_cons.mp remaining with rfl | later
      · rw [history] at inside
        exact bounded.runs source (by simp [original]) row ((retainFrom_sublist _ _ _ _).subset inside)
      · exact bounded.runs run (by simp [original, later]) row inside
  · rw [memory, clock]
    exact bounded.memory

private theorem across_retain (older newer : List (History α)) (run : History α) (key : UInt64)
    {floor snapshot : UInt64} (retained : floor ≤ snapshot) :
    Sequential.across key snapshot (older ++ run.retain floor :: newer) =
      Sequential.across key snapshot (older ++ run :: newer) := by
  induction older with
  | nil => simp [Sequential.across, History.retain, winner_retain _ key retained]
  | cons head older ih => simp only [List.cons_append, Sequential.across, ih]

theorem PackedTable.retainRunVersions_visibleEntry {before after : PackedTable} {index : Nat} {snapshot : UInt64}
    (retained : before.retainRunVersions index = some after) (supported : before.pins.floor ≤ snapshot)
    (key : UInt64) : after.describe.visibleEntry key snapshot = before.describe.visibleEntry key snapshot := by
  obtain ⟨memory, _, _, older, source, output, newer, _, original, updated, _, history⟩ :=
    PackedTable.retainRunVersions_spec retained
  unfold Sequential.Table.visibleEntry Sequential.Table.histories PackedTable.describe
  rw [memory, original, updated]
  simp only [List.map_append, List.map_cons, List.append_assoc, List.cons_append, history]
  rw [across_retain _ _ _ key supported]

theorem PackedTable.retainRunVersions_reads {before after : PackedTable} {index : Nat} {snapshot : UInt64}
    (retained : before.retainRunVersions index = some after) (supported : before.pins.floor ≤ snapshot)
    (key start stop : UInt64) :
    after.lookupAt key snapshot = before.lookupAt key snapshot ∧
      after.rangeAt start stop snapshot = before.rangeAt start stop snapshot := by
  have visible := retainRunVersions_visibleEntry retained supported
  constructor
  · rw [lookupAt_eq, lookupAt_eq, Sequential.Table.lookup_eq_visibleEntry,
      Sequential.Table.lookup_eq_visibleEntry, visible key]
  · rw [rangeAt_eq, rangeAt_eq]
    exact Sequential.Table.range_of_visibleEntry_eq start stop snapshot visible

end Alvoki.Storage
