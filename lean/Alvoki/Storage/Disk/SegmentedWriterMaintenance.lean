import Alvoki.Storage.Disk.RetainedWriterState

namespace Alvoki.Storage.DiskSession

open WAL.Boundary Sequential

/-- Update the live table within the same writer, leaving its durable
checkpoint, WAL and owner exactly as observed. -/
def SegmentedWriterState.withTable (state : SegmentedWriterState) (table : PackedTable) : SegmentedWriterState :=
  { state with installed := { state.installed with table } }

/-- Successful in-memory table operations. Release uses the reported
session comparison through the same guard as the native adapter. -/
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
  | retainRunVersions {index table} (retained : before.retainRunVersions index = some table) :
      SegmentedTableStep before table

private theorem SegmentedTableStep.preservesResumed {installed files target history published checkpoint table}
    (step : SegmentedTableStep installed.table table)
    (ready : ResumedAppendReady installed files target history published checkpoint) :
    ResumedAppendReady { installed with table } files target history published checkpoint := by
  obtain ⟨model, refined, represented⟩ := ready.canonical
  have bounds := ready.bounds
  have withTable {table : PackedTable} {model : SnapshotTable UInt64} (bounded : table.RowBounds)
      (refines : table.Refines model) (represents : RepresentsWalHistory history model) :
      ResumedAppendReady { installed with table } files target history published checkpoint :=
    { ready with bounds := bounded, canonical := ⟨model, refines, represents⟩ }
  cases step with
  | acquireAt acquired =>
    obtain ⟨_, refines, represents⟩ := represented.acquireAt refined bounds acquired
    exact withTable (bounds.acquireAt acquired) refines represents
  | release handle sameSession =>
    cases sameSession
    · exact ready
    · exact withTable (bounds.release handle) (PackedTable.release_refines refined handle)
        (represented.release handle)
  | advanceFloor advanced =>
    obtain ⟨_, _, refines, represents⟩ := represented.advanceFloor refined bounds advanced
    exact withTable (bounds.advanceFloor advanced) refines represents
  | compact compacted =>
    obtain ⟨_, _, refines, represents⟩ := represented.compact refined bounds compacted
    exact withTable (bounds.compact compacted) refines represents
  | retainRunVersions retained =>
    obtain ⟨_, refines, represents⟩ := represented.retainRunVersions refined bounds retained
    exact withTable (bounds.retainRunVersions retained) refines represents

theorem SegmentedTableStep.preservesReady {directory descriptor} {state : SegmentedWriterState} {table : PackedTable}
    (step : SegmentedTableStep state.installed.table table) (ready : state.Ready directory descriptor) :
    (state.withTable table).Ready directory descriptor :=
  { ready with resumed := step.preservesResumed ready.resumed }

theorem SegmentedTableStep.preservesRetained {directory descriptor} {state : SegmentedWriterState} {table : PackedTable}
    (step : SegmentedTableStep state.installed.table table) (ready : state.RetainedReady directory descriptor) :
    (state.withTable table).RetainedReady directory descriptor :=
  { ready with resumed := step.preservesResumed ready.resumed }

end Alvoki.Storage.DiskSession
