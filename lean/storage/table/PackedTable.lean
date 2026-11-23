import CompactionRead
import SnapshotTable

namespace Alvoki.Storage
open Alvoki.Compaction (CheckedRun inRange)
open Alvoki.Compaction.Model
open Alvoki.Sequential (History SnapshotHandle SnapshotPin SnapshotPins SnapshotTable)

/-- The in-memory engine stores immutable packed v3 runs and an ordered memtable. -/
structure PackedTable where
  private mk ::
  runs : List CheckedRun
  memory : History UInt64
  committed : UInt64
  pins : SnapshotPins

def PackedTable.empty : PackedTable := ⟨[], .empty, 0, .empty⟩

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

theorem PackedTable.empty_refines : PackedTable.empty.Refines (SnapshotTable.empty : SnapshotTable UInt64) :=
  ⟨rfl, rfl, rfl⟩

def PackedTable.write (state : PackedTable) (key : UInt64) (value : Option UInt64) : Option PackedTable :=
  if state.committed.toNat + 1 < UInt64.size then
    let sequence := UInt64.ofNat (state.committed.toNat + 1)
    some { state with committed := sequence, memory := state.memory.union (.singleton ⟨key, sequence, value⟩) }
  else none

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
    simp only [same.memory]
  · contradiction

def PackedTable.acquireAt (state : PackedTable) (snapshot : UInt64) :
    Option (SnapshotPin × PackedTable) :=
  (state.pins.acquire state.committed snapshot).map fun (pin, pins) => (pin, { state with pins })

def PackedTable.acquire (state : PackedTable) : Option (SnapshotPin × PackedTable) :=
  state.acquireAt state.committed

def PackedTable.release (state : PackedTable) (handle : SnapshotHandle) : PackedTable :=
  { state with pins := state.pins.release handle }

def PackedTable.advanceFloor (state : PackedTable) (floor : UInt64) : Option PackedTable :=
  if floor ≤ state.committed then (state.pins.advance floor).map fun pins => { state with pins }
  else none

def PackedTable.flush (state : PackedTable) : Except String PackedTable :=
  match CheckedRun.ofHistory state.memory with
  | .ok run => .ok { state with runs := state.runs ++ [run], memory := .empty }
  | .error message => .error message

private def compactSuffix (floor : UInt64) : List CheckedRun → Option (List CheckedRun)
  | left :: right :: tail =>
    match left.compact right floor with
    | .ok run => some (run :: tail)
    | .error _ => none
  | _ => none

def PackedTable.compact (state : PackedTable) (index : Nat) : Option PackedTable :=
  (Sequential.replaceSuffix (compactSuffix state.pins.floor) index state.runs).map fun runs =>
    { state with runs }

private def winnerAcross (key snapshot : UInt64) (memory : History UInt64) :
    List CheckedRun → Option (Entry (Option UInt64))
  | [] => winner memory.rows key snapshot
  | run :: tail => newest (run.lookupEntry key snapshot) (winnerAcross key snapshot memory tail)

private theorem winnerAcross_eq (key snapshot : UInt64) (memory : History UInt64)
    (runs : List CheckedRun) :
    winnerAcross key snapshot memory runs =
      Sequential.across key snapshot (runs.map CheckedRun.history ++ [memory]) := by
  induction runs with
  | nil =>
    simp only [winnerAcross, List.map_nil, List.nil_append, Sequential.across]
    cases winner memory.rows key snapshot <;> rfl
  | cons run rest ih =>
    simp only [winnerAcross, List.map_cons, List.cons_append, Sequential.across, ih, run.lookupEntry_eq]

def PackedTable.lookupAt (state : @& PackedTable) (key snapshot : UInt64) : Option UInt64 :=
  (winnerAcross key snapshot state.memory state.runs).bind Entry.payload

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

private def clip (history : History UInt64) (start stop : UInt64) : History UInt64 :=
  ⟨history.rows.filter (inRange start stop), history.ordered.filter _⟩

private theorem winner_clip (history : History UInt64) (start stop key snapshot : UInt64)
    (within : start ≤ key ∧ key < stop) :
    winner (clip history start stop).rows key snapshot = winner history.rows key snapshot := by
  unfold clip winner
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

private theorem range_eq_of_winner {before after : Sequential.Table UInt64} (start stop snapshot : UInt64)
    (agrees : ∀ key, start ≤ key ∧ key < stop →
      Sequential.across key snapshot after.histories = Sequential.across key snapshot before.histories) :
    after.range start stop snapshot = before.range start stop snapshot := by
  let left := after.range start stop snapshot
  let right := before.range start stop snapshot
  have lo := after.range_ordered start stop snapshot
  have ro := before.range_ordered start stop snapshot
  have distinct {a b : Entry (Option UInt64)} (lt : a.key < b.key) (eq : a = b) : False :=
    UInt64.lt_irrefl a.key (eq ▸ lt)
  have same (row : Entry (Option UInt64)) : row ∈ left ↔ row ∈ right := by
    change (row ∈ after.range start stop snapshot ↔ row ∈ before.range start stop snapshot)
    rw [Sequential.Table.range_exact, Sequential.Table.range_exact]
    constructor
    · rintro ⟨⟨winner, put⟩, within⟩
      exact ⟨⟨(agrees row.key within).symm.trans winner, put⟩, within⟩
    · rintro ⟨⟨winner, put⟩, within⟩
      exact ⟨⟨(agrees row.key within).trans winner, put⟩, within⟩
  have perm := (List.perm_ext_iff_of_nodup (lo.imp distinct) (ro.imp distinct)).mpr same
  exact perm.eq_of_pairwise (fun a _ _ _ lt gt => (UInt64.lt_irrefl a.key (UInt64.lt_trans lt gt)).elim) lo ro

private def rangeSources (state : PackedTable) (start stop : UInt64) : Sequential.Table UInt64 :=
  ⟨state.runs.map (fun run => run.rangeHistory start stop), clip state.memory start stop⟩

/-- Merge only the requested key interval from each source and return its visible puts. -/
def PackedTable.rangeAt (state : @& PackedTable) (start stop snapshot : UInt64) :
    List (Entry (Option UInt64)) :=
  (rangeSources state start stop).range start stop snapshot

theorem PackedTable.rangeAt_eq (state : PackedTable) (start stop snapshot : UInt64) :
    state.rangeAt start stop snapshot = state.describe.range start stop snapshot := by
  unfold PackedTable.rangeAt
  apply range_eq_of_winner
  intro key within
  have hist (run : CheckedRun) : run.rangeHistory start stop = clip run.history start stop := by
    apply History.ext_rows
    exact run.rangeEntries_eq start stop
  have sources : (rangeSources state start stop).histories =
      (state.describe.histories.map fun run => clip run start stop) := by
    unfold rangeSources PackedTable.describe Sequential.Table.histories
    simp only [List.map_append, List.map_map, List.map_cons, List.map_nil]
    rw [List.map_congr_left]
    intro run _
    exact hist run
  rw [sources]
  exact across_clip _ start stop key snapshot within

def PackedTable.range (state : @& PackedTable) (handle : SnapshotHandle)
    (start stop : UInt64) : Option (List (Entry (Option UInt64))) :=
  (state.pins.find handle).map fun pin => state.rangeAt start stop pin.sequence

theorem PackedTable.range_refines {state : PackedTable} {model : SnapshotTable UInt64}
    (refinement : state.Refines model) (handle : SnapshotHandle) (start stop : UInt64) :
    state.range handle start stop = model.range handle start stop := by
  simp only [PackedTable.range, SnapshotTable.range, refinement.pins,
    PackedTable.rangeAt_eq, refinement.table]

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
      simp only [PackedTable.describe, Sequential.Table.write, clock]
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
      Sequential.Table.histories, List.map_append, List.map_cons, List.map_nil, hist]

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
  simp [PackedTable.describe, memory]

end Alvoki.Storage
