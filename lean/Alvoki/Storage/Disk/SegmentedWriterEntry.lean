import Alvoki.Storage.Disk.SegmentedWriterState
import Alvoki.Storage.Disk.SegmentedBootstrapReady
import Alvoki.Storage.Disk.RotationRetrySession

namespace Alvoki.Storage.DiskSession

open WalSegmentRepair

/-- The successful first open reports the zero keeper and selected empty
checkpoint. Use that same owned directory as the first writer state. -/
def _root_.Alvoki.Storage.WalSegmentRepair.BootstrapReady.writerState
    {after : WalSegmentRotation.State} (bootstrap : BootstrapReady after) (owners : LockOwners) : SegmentedWriterState :=
  SegmentedWriterState.ofReopen ⟨.empty, 0, 0, 0⟩ bootstrap.walImage []
    bootstrap.checkpointImage bootstrap.target none
    ⟨bootstrap.walImage.checkpointReopenFiles after.metadata none, owners⟩

theorem _root_.Alvoki.Storage.WalSegmentRepair.BootstrapReady.writerReady
    {directory : DiskDirectory} {descriptor : Nat} {after : LockedFileState WalSegmentRotation.State}
    (bootstrap : BootstrapReady after.image) (held : after.owners.Owns directory descriptor) :
    (bootstrap.writerState after.owners).Ready directory descriptor := by
  obtain ⟨chain, layout, _⟩ := bootstrap.walCanonical
  exact ⟨bootstrap.appendReady, layout, chain, rfl, rfl, rfl, rfl, held⟩

/-- A healthy rotation retry provides the next writer's complete layout,
including the previous keeper if it has become sealed. The ownership and
the exact phase come from the returned session. -/
theorem RotationRetryReady.writerReady {directory descriptor liveRefs published history original state target result}
    (opened : RotationRetryReady directory descriptor liveRefs published history original state target result)
    (chain : WalSegment.Chain history 0 original.segments) :
    ∃ session final, ∃ writer : SegmentedWriterState,
      result = .ok session final ∧ session.directory = directory ∧ session.descriptor = descriptor ∧
      session.phase = .ready writer.installed ∧ writer.files = final.image.settledReopenImage original ∧
      writer.wal = final.image.visible original ∧ writer.target = target ∧
      writer.owners = final.owners ∧ writer.history = history ∧ writer.published.durable = published.durable ∧
      writer.Ready directory descriptor := by
  obtain ⟨checkpoint, table, _, session, final, returned, _, _, path, lock, phase, _, _, held,
    _, _, _, _, _, _, _, _, resumed, layout, _, retained, directoryFiles, sealed, active, _⟩ := opened
  let installed : Installed := ⟨table, (checkpoint.getD (.empty, 0)).2, (WAL.encode history).size, target.first⟩
  let wal := final.image.visible original
  let files := final.image.settledReopenImage original
  let writer := SegmentedWriterState.ofReopen installed wal history published target checkpoint ⟨files, final.owners⟩
  refine ⟨session, final, writer, returned, path, lock, phase, rfl, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · change { wal with directory := files.directory } = wal
    rw [directoryFiles]
  exact ⟨⟨resumed.ready, resumed.through, resumed.keeper, resumed.bytes, resumed.contents, resumed.generation,
      resumed.selected, resumed.accepted, resumed.ordered, resumed.bounds, resumed.canonical⟩,
    ⟨layout.ordered, layout.forward, layout.activeEnd, layout.activeBytes⟩, retained chain, rfl, sealed,
    active.symm, rfl, held⟩

end Alvoki.Storage.DiskSession
