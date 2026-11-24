import Alvoki.Storage.Disk.VersionedReadyWriter

namespace Alvoki.WAL.Boundary

open Storage
open Sequential (SnapshotHandle SnapshotPin SnapshotTable)

namespace ObservedMarkedState.VersionedReady

/-- In-memory maintenance leaves the observed manifest, WAL and exact run
bindings unchanged. It only needs to preserve the live table's history. -/
private theorem withTable {state : ObservedMarkedState} {table : PackedTable} {model : SnapshotTable UInt64}
    (valid : state.VersionedReady) (bounded : table.RowBounds) (refined : table.Refines model)
    (represented : RepresentsWalHistory state.writer.history model) : (state.withTable table).VersionedReady := by
  refine ⟨⟨valid.ready.settled, valid.ready.ordered, ?_, valid.ready.length, valid.ready.fits, bounded⟩,
    ⟨model, refined, represented⟩, valid.selected, valid.generationMatches⟩
  change state.writer.history.length = table.committed.toNat
  rw [refined.committed, represented.committed_count]

theorem advanceFloor {state : ObservedMarkedState} {table : PackedTable} {floor : UInt64}
    (valid : state.VersionedReady) (advanced : state.writer.table.advanceFloor floor = some table) :
    (state.withTable table).VersionedReady := by
  obtain ⟨_, refined, represented⟩ := valid.live
  obtain ⟨_, _, nextRefined, nextHistory⟩ := represented.advanceFloor refined valid.ready.rowBounds advanced
  exact valid.withTable (valid.ready.rowBounds.advanceFloor advanced) nextRefined nextHistory

theorem compact {state : ObservedMarkedState} {table : PackedTable} {index : Nat}
    (valid : state.VersionedReady) (compacted : state.writer.table.compact index = some table) :
    (state.withTable table).VersionedReady := by
  obtain ⟨_, refined, represented⟩ := valid.live
  obtain ⟨_, _, nextRefined, nextHistory⟩ := represented.compact refined valid.ready.rowBounds compacted
  exact valid.withTable (valid.ready.rowBounds.compact compacted) nextRefined nextHistory

theorem acquireAt {state : ObservedMarkedState} {table : PackedTable} {snapshot : UInt64} {pin : SnapshotPin}
    (valid : state.VersionedReady) (acquired : state.writer.table.acquireAt snapshot = some (pin, table)) :
    (state.withTable table).VersionedReady := by
  obtain ⟨_, refined, represented⟩ := valid.live
  obtain ⟨_, nextRefined, nextHistory⟩ := represented.acquireAt refined valid.ready.rowBounds acquired
  exact valid.withTable (valid.ready.rowBounds.acquireAt acquired) nextRefined nextHistory

theorem release {state : ObservedMarkedState} (valid : state.VersionedReady) (handle : SnapshotHandle) :
    (state.withTable (state.writer.table.release handle)).VersionedReady := by
  obtain ⟨_, refined, represented⟩ := valid.live
  exact valid.withTable (valid.ready.rowBounds.release handle) (PackedTable.release_refines refined handle)
    (represented.release handle)

theorem pinnedReads {state : ObservedMarkedState} (valid : state.VersionedReady) {reference : SnapshotTable UInt64}
    (replayed : SnapshotWalReplay .empty state.writer.history reference) {pin : SnapshotPin}
    (active : pin ∈ state.writer.table.pins.active) :
    (∀ key, state.writer.table.lookup pin.handle key = some (reference.table.lookup key pin.sequence)) ∧
    ∀ start stop, state.writer.table.range pin.handle start stop =
      some (reference.table.range start stop pin.sequence) := by
  obtain ⟨_, refined, represented⟩ := valid.live
  exact represented.packedPinnedReads refined replayed active

end ObservedMarkedState.VersionedReady

end Alvoki.WAL.Boundary
