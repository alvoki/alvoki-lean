import Alvoki.Storage.Table.PackedTable
import Alvoki.Storage.Proofs.Table.CheckedRunCompaction

namespace Alvoki.Storage
open Alvoki.Compaction (CheckedRun inRange)
open Alvoki.Compaction.Model
open Alvoki.Sequential (History SnapshotHandle SnapshotPin SnapshotPins SnapshotTable)

theorem PackedTable.compact_spec {state after : PackedTable} {index : Nat}
    (compacted : state.compact index = some after) :
    after.memory = state.memory ∧ after.committed = state.committed ∧ after.pins = state.pins ∧
      ∃ older left right run newer, older.length = index ∧
        state.runs = older ++ left :: right :: newer ∧ after.runs = older ++ run :: newer ∧
        run.history = Sequential.compactPair left.history right.history state.pins.floor := by
  obtain ⟨memory, clock, pins, older, left, right, run, newer, length, original, updated, merged⟩ :=
    PackedTable.compact_execution compacted
  exact ⟨memory, clock, pins, older, left, right, run, newer, length, original, updated,
    CheckedRun.compact_spec merged⟩

theorem PackedTable.RowBounds.compact {state after : PackedTable} {index : Nat}
    (bounded : state.RowBounds) (compacted : state.compact index = some after) : after.RowBounds := by
  obtain ⟨memory, clock, _, older, left, right, run, newer, _, original, updated, history⟩ :=
    PackedTable.compact_spec compacted
  constructor
  · intro source member row inside
    rw [updated] at member
    rw [clock]
    rcases List.mem_append.mp member with earlier | rest
    · exact bounded.runs source (by rw [original]; exact List.mem_append_left _ earlier) row inside
    · rcases List.mem_cons.mp rest with rfl | later
      · rw [history] at inside
        change row ∈ retain (union left.history.rows right.history.rows) state.pins.floor at inside
        rcases mem_union ((retainFrom_sublist _ _ _ _).subset inside) with inLeft | inRight
        · exact bounded.runs left (by simp [original]) row inLeft
        · exact bounded.runs right (by simp [original]) row inRight
      · exact bounded.runs source (by simp [original, later]) row inside
  · simpa only [memory, clock] using bounded.memory

theorem PackedTable.compact_refines {before after : PackedTable} {model : SnapshotTable UInt64}
    {index : Nat} (same : before.Refines model) (compacted : before.compact index = some after) :
    ∃ result, model.compact index = some result ∧ after.Refines result := by
  obtain ⟨memory, clock, pins, older, left, right, run, newer, length, original, updated, history⟩ :=
    PackedTable.compact_spec compacted
  have replaced : Sequential.compactSuffix before.pins.floor
      (left.history :: right.history :: newer.map CheckedRun.history) =
      some (run.history :: newer.map CheckedRun.history) := by
    simp [Sequential.compactSuffix, history]
  have mapped := Sequential.replaceSuffix_at_prefix (older.map CheckedRun.history) replaced
  have modelResult : Sequential.replaceSuffix (Sequential.compactSuffix model.pins.floor) index
      model.table.runs = some (after.runs.map CheckedRun.history) := by
    simpa only [← same.pins, ← same.table, PackedTable.describe, original, updated,
      List.map_append, List.map_cons, List.length_map, length] using mapped
  unfold SnapshotTable.compact Sequential.Table.compactAt
  rw [modelResult]
  refine ⟨_, rfl, ⟨?_, clock.trans same.committed, pins.trans same.pins⟩⟩
  simp only [PackedTable.describe, memory, ← same.table]

theorem PackedTable.retainRunVersions_spec {before after : PackedTable} {index : Nat}
    (retained : before.retainRunVersions index = some after) :
    after.memory = before.memory ∧ after.committed = before.committed ∧ after.pins = before.pins ∧
      ∃ older source output newer, older.length = index ∧ before.runs = older ++ source :: newer ∧
        after.runs = older ++ output :: newer ∧ source.retainVersions before.pins.floor = .ok output ∧
        output.history = source.history.retain before.pins.floor := by
  obtain ⟨memory, clock, pins, older, source, output, newer, length, original, updated, written⟩ :=
    PackedTable.retainRunVersions_execution retained
  exact ⟨memory, clock, pins, older, source, output, newer, length, original, updated, written,
    CheckedRun.retainVersions_spec written⟩

theorem PackedTable.retainRunVersions_byteSize_le {before after : PackedTable} {index : Nat}
    (retained : before.retainRunVersions index = some after) :
    ∃ source output,
      before.runs[index]? = some source ∧ after.runs[index]? = some output ∧
      output.run.bytes.size ≤ 16 + 32 * retentionRowBound source.history.rows before.pins.floor := by
  obtain ⟨_, _, _, older, source, output, newer, length, original, updated, written, _⟩ :=
    PackedTable.retainRunVersions_spec retained
  have atIndex (run : CheckedRun) : (older ++ run :: newer)[index]? = some run := by
    rw [List.getElem?_append_right (Nat.le_of_eq length), ← length, Nat.sub_self]
    rfl
  exact ⟨source, output, original.symm ▸ atIndex source, updated.symm ▸ atIndex output,
    CheckedRun.retainVersions_byteSize_le written⟩

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


end Alvoki.Storage
