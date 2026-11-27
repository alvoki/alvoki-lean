import Alvoki.Storage.Table.PackedTable
import Alvoki.Storage.Proofs.Table.CheckedRunLookup

namespace Alvoki.Storage
open Alvoki.Compaction (CheckedRun)
open Alvoki.Compaction.Model
open Alvoki.Sequential (SnapshotHandle SnapshotPin SnapshotPins SnapshotTable)

theorem PackedTable.lookupAt_eq (state : PackedTable) (key snapshot : UInt64) :
    state.lookupAt key snapshot = state.describe.lookup key snapshot := by
  rw [PackedTable.lookupAt_as_runLookups]
  have agrees (runs : List CheckedRun) :
      (runs.map (fun run => run.lookupEntry key snapshot)).foldr newest
          (winner state.memory.rows key snapshot) =
        Sequential.across key snapshot (runs.map CheckedRun.history ++ [state.memory]) := by
    induction runs with
    | nil =>
      simp only [List.map_nil, List.foldr_nil, List.nil_append, Sequential.across]
      cases winner state.memory.rows key snapshot <;> rfl
    | cons run rest ih =>
      simp only [List.map_cons, List.foldr_cons, List.cons_append, Sequential.across]
      rw [ih, CheckedRun.lookupEntry_eq]
  change _ = (Sequential.across key snapshot (state.runs.map CheckedRun.history ++ [state.memory])).bind Entry.payload
  rw [agrees]

theorem PackedTable.lookup_refines {state : PackedTable} {model : SnapshotTable UInt64}
    (refinement : state.Refines model) (handle : SnapshotHandle) (key : UInt64) :
    state.lookup handle key = model.lookup handle key := by
  simp only [PackedTable.lookup, SnapshotTable.lookup, refinement.pins,
    PackedTable.lookupAt_eq, refinement.table]

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
