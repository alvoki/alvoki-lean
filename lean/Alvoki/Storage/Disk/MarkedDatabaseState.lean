import Alvoki.Storage.Disk.MarkedSessionHistory

namespace Alvoki.WAL.Boundary

open Storage
open Sequential (SnapshotHandle SnapshotPin SnapshotPins SnapshotTable)

/-- The actual writer state, its installed generation, and the checkpoint
selected by its manifest. -/
structure MarkedDatabaseState where
  writer : MarkedWriterState
  checkpoint : FixedMarkedCheckpoint
  generation : UInt64

def MarkedDatabaseState.withWriter (state : MarkedDatabaseState) (writer : MarkedWriterState) :
    MarkedDatabaseState := { state with writer }

def MarkedDatabaseState.withTable (state : MarkedDatabaseState) (table : PackedTable) :
    MarkedDatabaseState := state.withWriter { state.writer with table }

/-- The selected checkpoint represents its covered prefix, and the live
writer refines the entire durable WAL at its own retention floor. -/
structure MarkedDatabaseState.Valid (state : MarkedDatabaseState) : Prop where
  ready : state.writer.ReadyFor state.checkpoint.manifest
  coveredPrefix : ∃ pending, state.writer.history = state.checkpoint.covered ++ pending
  live : ∃ model, state.writer.table.Refines model ∧ RepresentsWalHistory state.writer.history model
  covered : RepresentsWalHistory state.checkpoint.covered state.checkpoint.model
  generationMatches : ((state.checkpoint.manifest.mapM fun bytes => (Manifest.decode bytes).map
    (·.generation)).map (·.getD 0) : Except String UInt64) = .ok state.generation

namespace MarkedDatabaseState.Valid

private theorem withExtendedWriter {state : MarkedDatabaseState} {writer : MarkedWriterState}
    {suffix : List WAL.Write} {model : SnapshotTable UInt64} (valid : state.Valid)
    (ready : writer.ReadyFor state.checkpoint.manifest)
    (extended : writer.history = state.writer.history ++ suffix)
    (refined : writer.table.Refines model) (represented : RepresentsWalHistory writer.history model) :
    (state.withWriter writer).Valid := by
  obtain ⟨pending, startingHistory⟩ := valid.coveredPrefix
  refine ⟨ready, ⟨pending ++ suffix, ?_⟩, ⟨model, refined, represented⟩,
    valid.covered, valid.generationMatches⟩
  change writer.history = state.checkpoint.covered ++ (pending ++ suffix)
  rw [extended, startingHistory, List.append_assoc]

private theorem withTable {state : MarkedDatabaseState} {table : PackedTable}
    {model : SnapshotTable UInt64} (valid : state.Valid)
    (bounded : table.RowBounds) (refined : table.Refines model)
    (represented : RepresentsWalHistory state.writer.history model) : (state.withTable table).Valid := by
  refine ⟨⟨valid.ready.settled, valid.ready.ordered, ?_, valid.ready.length, valid.ready.fits, bounded⟩,
    valid.coveredPrefix, ⟨model, refined, represented⟩, valid.covered, valid.generationMatches⟩
  change state.writer.history.length = table.committed.toNat
  rw [refined.committed, represented.committed_count]

theorem acknowledgedWrites {state : MarkedDatabaseState} {writer : MarkedWriterState}
    {submitted : List WAL.Write} (valid : state.Valid)
    (path : AcknowledgedWrites state.writer submitted writer) :
    (state.withWriter writer).Valid ∧ writer.history = state.writer.history ++ submitted := by
  obtain ⟨model, refined, represented⟩ := valid.live
  obtain ⟨ready, extended, next, _, nextRefined, nextHistory⟩ :=
    path.refinesHistory valid.ready refined represented
  exact ⟨valid.withExtendedWriter ready extended nextRefined nextHistory, extended⟩

theorem advanceFloor {state : MarkedDatabaseState} {table : PackedTable} {floor : UInt64}
    (valid : state.Valid) (advanced : state.writer.table.advanceFloor floor = some table) :
    (state.withTable table).Valid := by
  obtain ⟨model, refined, represented⟩ := valid.live
  obtain ⟨next, _, nextRefined, nextHistory⟩ :=
    represented.advanceFloor refined valid.ready.rowBounds advanced
  exact valid.withTable (valid.ready.rowBounds.advanceFloor advanced) nextRefined nextHistory

theorem compact {state : MarkedDatabaseState} {table : PackedTable} {index : Nat}
    (valid : state.Valid) (compacted : state.writer.table.compact index = some table) :
    (state.withTable table).Valid := by
  obtain ⟨model, refined, represented⟩ := valid.live
  obtain ⟨next, _, nextRefined, nextHistory⟩ := represented.compact refined valid.ready.rowBounds compacted
  exact valid.withTable (valid.ready.rowBounds.compact compacted) nextRefined nextHistory

theorem acquireAt {state : MarkedDatabaseState} {table : PackedTable} {snapshot : UInt64}
    {pin : SnapshotPin} (valid : state.Valid)
    (acquired : state.writer.table.acquireAt snapshot = some (pin, table)) :
    (state.withTable table).Valid := by
  obtain ⟨model, refined, represented⟩ := valid.live
  obtain ⟨next, selected, nextRefined⟩ := PackedTable.acquireAt_refines refined acquired
  have bounded := valid.ready.rowBounds.acquireAt acquired
  refine valid.withTable bounded nextRefined ?_
  unfold SnapshotTable.acquireAt at selected
  split at selected
  · contradiction
  · rename_i accepted
    cases selected
    obtain ⟨_, _, _, _, _, _, floor⟩ := SnapshotPins.acquire_spec accepted
    exact represented.preserve rfl (UInt64.le_of_eq floor.symm)
      (nextRefined.rowsBounded bounded) (fun _ _ _ => rfl)

theorem release {state : MarkedDatabaseState} (valid : state.Valid) (handle : SnapshotHandle) :
    (state.withTable (state.writer.table.release handle)).Valid := by
  obtain ⟨model, refined, represented⟩ := valid.live
  have nextRefined := PackedTable.release_refines refined handle
  have bounded := valid.ready.rowBounds.release handle
  exact valid.withTable bounded nextRefined (represented.preserve rfl (UInt64.le_refl _)
    (nextRefined.rowsBounded bounded) (fun _ _ _ => rfl))

/-- The next writer is the actual successful reopen. The old history is
extended in order and the pin registry starts with no active pins. -/
theorem sessionStep {state : MarkedDatabaseState} {writer : MarkedWriterState}
    {writes : MarkedSessionWrites} (valid : state.Valid)
    (step : MarkedSessionStep state.checkpoint state.writer writes writer) :
    ∃ suffix, (state.withWriter writer).Valid ∧ writer.history = state.writer.history ++ suffix ∧
      writes.Retains suffix ∧ writer.table.pins.active = [] := by
  obtain ⟨pending, start⟩ := valid.coveredPrefix
  obtain ⟨suffix, ready, extended, retains, model, refined, represented, fresh⟩ :=
    step.refinesHistory valid.ready start valid.covered
  exact ⟨suffix, valid.withExtendedWriter ready extended refined represented, extended, retains, fresh⟩

end MarkedDatabaseState.Valid

end Alvoki.WAL.Boundary
