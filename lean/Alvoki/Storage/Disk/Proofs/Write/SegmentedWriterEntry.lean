import Alvoki.Storage.Disk.Proofs.Write.SegmentedWriterState
import Alvoki.Storage.Disk.Proofs.Bootstrap.SegmentedBootstrapReady
import Alvoki.Storage.Disk.Proofs.Rotation.RotationRetrySession
import Alvoki.Storage.Disk.Proofs.Write.RetainedWriterState

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

/-- A healthy rotation retry provides the next retained writer's layout,
including the previous keeper if it has become sealed. The owner and
exact phase come from the returned session. -/
theorem RotationRetryReady.writerRetainedReady
    {directory descriptor liveRefs published history original state target result}
    (opened : RotationRetryReady directory descriptor liveRefs published history original state target result)
    (spans : ∀ segment ∈ original.segments, segment.bytes.size = (segment.last - segment.first) * WAL.frameSize) :
    ∃ session final, ∃ writer : SegmentedWriterState,
      result = .ok session final ∧ session.directory = directory ∧ session.descriptor = descriptor ∧
      session.phase = .ready writer.installed ∧ writer.files = final.image.settledReopenImage original ∧
      writer.wal = final.image.visible original ∧ writer.target = target ∧
      writer.owners = final.owners ∧ writer.history = history ∧ writer.published.durable = published.durable ∧
      writer.RetainedReady directory descriptor := by
  obtain ⟨checkpoint, table, _, session, final, returned, _, _, path, lock, phase, _, _, held,
    _, _, _, _, _, _, _, _, resumed, layout, valid, _, directoryFiles, sealed, active, _⟩ := opened
  let installed : Installed := ⟨table, (checkpoint.getD (.empty, 0)).2, (WAL.encode history).size, target.first⟩
  let wal := final.image.visible original
  let files := final.image.settledReopenImage original
  let writer := SegmentedWriterState.ofReopen installed wal history published target checkpoint ⟨files, final.owners⟩
  refine ⟨session, final, writer, returned, path, lock, phase, rfl, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · change { wal with directory := files.directory } = wal
    rw [directoryFiles]
  have sealedSpans : ∀ segment ∈ wal.sealed, segment.bytes.size = (segment.last - segment.first) * WAL.frameSize := by
    intro segment member
    apply spans
    by_cases absent : final.image.successor = .absent
    · exact List.mem_append_left _ (by simpa [wal, WalSegmentRotation.State.visible, absent] using member)
    · simpa [wal, WalSegmentRotation.State.visible, absent, WalSegmentImage.rotated, WalSegmentImage.segments] using member
  have writerValid : writer.wal.Valid writer.history := by
    change ({ wal with directory := files.directory } : WalSegmentImage).Valid history
    rw [directoryFiles]
    exact valid
  exact ⟨⟨resumed.ready, resumed.through, resumed.keeper, resumed.bytes, resumed.contents, resumed.generation,
      resumed.selected, resumed.accepted, resumed.ordered, resumed.bounds, resumed.canonical⟩,
    ⟨layout.ordered, layout.forward, layout.activeEnd, layout.activeBytes⟩, writerValid, sealedSpans, rfl, sealed,
    active.symm, rfl, held⟩

/-- A caller with a complete physical chain also keeps that stronger
property through the same successful rotation recovery. -/
theorem RotationRetryReady.writerReady {directory descriptor liveRefs published history original state target result}
    (opened : RotationRetryReady directory descriptor liveRefs published history original state target result)
    (chain : WalSegment.Chain history 0 original.segments) :
    ∃ session final, ∃ writer : SegmentedWriterState,
      result = .ok session final ∧ session.directory = directory ∧ session.descriptor = descriptor ∧
      session.phase = .ready writer.installed ∧ writer.files = final.image.settledReopenImage original ∧
      writer.wal = final.image.visible original ∧ writer.target = target ∧
      writer.owners = final.owners ∧ writer.history = history ∧ writer.published.durable = published.durable ∧
      writer.Ready directory descriptor := by
  obtain ⟨session, final, writer, returned, path, lock, phase, files, visible, exactTarget, owners, history,
    durable, retained⟩ := opened.writerRetainedReady (fun _ member => chain.member_byteSize member)
  obtain ⟨_, _, _, knownSession, knownFinal, knownReturned, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, carriesChain, _⟩ := opened
  have same := (EStateM.Result.ok.inj (knownReturned.symm.trans returned)).2
  refine ⟨session, final, writer, returned, path, lock, phase, files, visible, exactTarget, owners, history, durable,
    ⟨retained.resumed, retained.layout, ?_, retained.directoryFiles, retained.sealedFiles, retained.active,
      retained.manifestFiles, retained.held⟩⟩
  rw [visible, ← same, history]
  exact carriesChain chain

end Alvoki.Storage.DiskSession
