import Alvoki.Storage.Disk.Proofs.Recovery.MarkedDatabaseState

namespace Alvoki.WAL.Boundary

open Storage
open Sequential (SnapshotHandle SnapshotPin)

/-- Data at the ready boundary, including the durable run bindings that
checkpoint readers observe. The proof supplies a matching checkpoint. -/
structure ObservedMarkedState where
  writer : MarkedWriterState
  generation : UInt64
  durable : UInt64 → Nat → Option ByteArray

def ObservedMarkedState.withWriter (state : ObservedMarkedState) (writer : MarkedWriterState) :
    ObservedMarkedState := { state with writer }

def ObservedMarkedState.withTable (state : ObservedMarkedState) (table : PackedTable) :
    ObservedMarkedState := state.withWriter { state.writer with table }

def ObservedMarkedState.Valid (state : ObservedMarkedState) : Prop :=
  ∃ checkpoint : FixedMarkedCheckpoint, checkpoint.image.durable = state.durable ∧
    (⟨state.writer, checkpoint, state.generation⟩ : MarkedDatabaseState).Valid

def MarkedDatabaseState.observe (state : MarkedDatabaseState) : ObservedMarkedState :=
  ⟨state.writer, state.generation, state.checkpoint.image.durable⟩

theorem MarkedDatabaseState.Valid.observe {state : MarkedDatabaseState} (valid : state.Valid) :
    state.observe.Valid := ⟨state.checkpoint, rfl, valid⟩

namespace ObservedMarkedState.Valid

theorem acknowledgedWrites {state : ObservedMarkedState} {writer : MarkedWriterState}
    {submitted : List WAL.Write} (valid : state.Valid)
    (path : AcknowledgedWrites state.writer submitted writer) :
    (state.withWriter writer).Valid ∧ writer.history = state.writer.history ++ submitted := by
  obtain ⟨checkpoint, durable, represented⟩ := valid
  obtain ⟨next, extended⟩ := represented.acknowledgedWrites path
  exact ⟨⟨checkpoint, durable, next⟩, extended⟩

theorem advanceFloor {state : ObservedMarkedState} {table : PackedTable} {floor : UInt64}
    (valid : state.Valid) (advanced : state.writer.table.advanceFloor floor = some table) :
    (state.withTable table).Valid := by
  obtain ⟨checkpoint, durable, represented⟩ := valid
  exact ⟨checkpoint, durable, represented.advanceFloor advanced⟩

theorem compact {state : ObservedMarkedState} {table : PackedTable} {index : Nat}
    (valid : state.Valid) (compacted : state.writer.table.compact index = some table) :
    (state.withTable table).Valid := by
  obtain ⟨checkpoint, durable, represented⟩ := valid
  exact ⟨checkpoint, durable, represented.compact compacted⟩

theorem acquireAt {state : ObservedMarkedState} {table : PackedTable} {snapshot : UInt64}
    {pin : SnapshotPin} (valid : state.Valid)
    (acquired : state.writer.table.acquireAt snapshot = some (pin, table)) :
    (state.withTable table).Valid := by
  obtain ⟨checkpoint, durable, represented⟩ := valid
  exact ⟨checkpoint, durable, represented.acquireAt acquired⟩

theorem release {state : ObservedMarkedState} (valid : state.Valid) (handle : SnapshotHandle) :
    (state.withTable (state.writer.table.release handle)).Valid := by
  obtain ⟨checkpoint, durable, represented⟩ := valid
  exact ⟨checkpoint, durable, represented.release handle⟩

/-- The same raw reopen evidence can use whichever matching checkpoint the
invariant supplies, since its run observations depend on the durable map. -/
theorem sessionStep {state : ObservedMarkedState} {writer : MarkedWriterState}
    {writes : MarkedSessionWrites} (valid : state.Valid)
    (step : MarkedSessionStep state.durable state.writer writes writer) :
    ∃ suffix, (state.withWriter writer).Valid ∧ writer.history = state.writer.history ++ suffix ∧
      writes.Retains suffix ∧ writer.table.pins.active = [] := by
  obtain ⟨checkpoint, durable, represented⟩ := valid
  have selected : MarkedSessionStep checkpoint.image.durable state.writer writes writer :=
    durable.symm ▸ step
  obtain ⟨suffix, next, extended, retained, fresh⟩ := represented.sessionStep selected
  exact ⟨suffix, ⟨checkpoint, durable, next⟩, extended, retained, fresh⟩

end ObservedMarkedState.Valid

end Alvoki.WAL.Boundary
