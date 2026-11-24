import Alvoki.Storage.Disk.SegmentedWriterState

namespace Alvoki.Storage.DiskSession

open WAL.Boundary Sequential

/-- Update the live table within the same writer, leaving its durable
checkpoint, WAL and owner exactly as observed. -/
def SegmentedWriterState.withTable (state : SegmentedWriterState) (table : PackedTable) : SegmentedWriterState :=
  { state with installed := { state.installed with table } }

private theorem SegmentedWriterState.Ready.withTable {directory descriptor state table model}
    (ready : SegmentedWriterState.Ready directory descriptor state)
    (bounds : table.RowBounds) (refines : table.Refines model) (represents : RepresentsWalHistory state.history model) :
    (state.withTable table).Ready directory descriptor := by
  exact { ready with resumed := { ready.resumed with bounds, canonical := ⟨model, refines, represents⟩ } }

/-- Successful in-memory operations of the native writer. Release uses the
reported session comparison through the same guard as the adapter. -/
inductive SegmentedTableStep (before : PackedTable) : PackedTable → Prop where
  | acquireAt {snapshot pin table} (acquired : before.acquireAt snapshot = some (pin, table)) :
      SegmentedTableStep before table
  | release (handle : SnapshotHandle) (sameSession : Bool) :
      SegmentedTableStep before
        (withLocalHandle (m := Id) (pure before) (pure sameSession) before (fun table => pure (table.release handle)))
  | advanceFloor {floor table} (advanced : before.advanceFloor floor = some table) :
      SegmentedTableStep before table
  | compact {index table} (compacted : before.compact index = some table) :
      SegmentedTableStep before table

theorem SegmentedTableStep.preservesReady {directory descriptor} {state : SegmentedWriterState} {table : PackedTable}
    (step : SegmentedTableStep state.installed.table table) (ready : state.Ready directory descriptor) :
    (state.withTable table).Ready directory descriptor := by
  obtain ⟨model, refined, represented⟩ := ready.resumed.canonical
  have bounds := ready.resumed.bounds
  cases step with
  | acquireAt acquired =>
    obtain ⟨_, refines, represents⟩ := represented.acquireAt refined bounds acquired
    exact ready.withTable (bounds.acquireAt acquired) refines represents
  | release handle sameSession =>
    cases sameSession
    · exact ready
    · exact ready.withTable (bounds.release handle) (PackedTable.release_refines refined handle)
        (represented.release handle)
  | advanceFloor advanced =>
    obtain ⟨_, _, refines, represents⟩ := represented.advanceFloor refined bounds advanced
    exact ready.withTable (bounds.advanceFloor advanced) refines represents
  | compact compacted =>
    obtain ⟨_, _, refines, represents⟩ := represented.compact refined bounds compacted
    exact ready.withTable (bounds.compact compacted) refines represents

end Alvoki.Storage.DiskSession
