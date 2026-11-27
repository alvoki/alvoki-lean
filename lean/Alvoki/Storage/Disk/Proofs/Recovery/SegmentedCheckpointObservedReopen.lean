import Alvoki.Storage.Disk.Proofs.Recovery.SegmentedCheckpointPowerLoss
import Alvoki.Storage.Disk.Proofs.Session.DiskOpenAdmission

namespace Alvoki.Storage.DiskSession

open WalSegmentRepair
open System (FilePath)

/-- The writer reconstructed from the report's exact returned session and
file image, with the unchanged WAL and the selected publication's run map. -/
structure CheckpointChunkWriter {files : Type} (directory : DiskDirectory) (before : SegmentedWriterState)
    {retry : LockedFileState FileImage} {layout : CanonicalKeeperLayout retry.image before.history}
    (published : CheckpointPublication.Image) (observed : MarkedRetryChunkReports files directory layout published)
    (after : SegmentedWriterState) : Prop where
  reopened : ∃ session final, observed.run = .ok session final ∧ session.directory = directory ∧
    session.descriptor = observed.slot.description ∧ session.phase = .ready after.installed ∧
    after.files = final.image ∧ after.owners = final.owners
  target : after.target = layout.target
  keeper : layout.keeper = before.wal.active
  aligned : layout.tail = ByteArray.empty
  selectedSeals : layout.sealed ++ [layout.keeper] =
    (published.segmentedCheckpointView before.wal).readDescriptors layout.range.watermark
  history : after.history = before.history
  wal : after.wal = { before.wal with directory := after.files.directory }
  durable : after.published.durable = published.durable
  retained : after.RetainedReady directory observed.slot.description

/-- A successful open has one returned session and file state. Match the
writer's ready payload and state to that exact result. -/
theorem CheckpointChunkWriter.atReopen
    (endpoint : CheckpointChunkWriter directory before published observed after)
    {session : SegmentedSession} {final : LockedFileState FileImage}
    (returned : observed.run = .ok session final) :
    session.phase = .ready after.installed ∧ after.files = final.image ∧ after.owners = final.owners := by
  obtain ⟨_, _, ran, _, _, phase, files, owners⟩ := endpoint.reopened
  obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj (returned.symm.trans ran)
  exact ⟨phase, files, owners⟩

theorem CheckpointChunkWriter.preservesChain
    (endpoint : CheckpointChunkWriter directory before published observed after)
    (chain : WalSegment.Chain before.history 0 before.wal.segments) : WalSegment.Chain after.history 0 after.wal.segments := by
  rw [endpoint.history, endpoint.wal]
  exact chain

/-- A reached checkpoint primitive can be interrupted without a returned
result. At the final retry, the marked dispatcher reads the checkpoint
selected by the surviving pair, then installs the replay of the same WAL.
The callback packet is indexed by the physical selected layout at that
retry. It supplies the successful native admission reports for its exact lock
slot, the chunk reads and the successful reached repair effects.
Any provenance of its native callbacks and admission is retained in the result. -/
theorem CheckpointPowerCut.reopensFromChunks {files : Type} {directory : DiskDirectory}
    {before : SegmentedWriterState} {writer : Nat} {input : FilePath} (cut : CheckpointPowerCut directory before)
    (ready : before.RetainedReady directory writer) (published : CheckpointPublication.Image)
    (projected : before.published.executeVersioned cut.checkpoint.plan cut.checkpoint.cut = some published)
    (pair : DirectoryPublication.Bindings) (survives : pair ∈ (published.segmentedCheckpointView before.wal).directory.crashImages)
    (retry : LockedFileState FileImage)
    (failures : BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
      ⟨(physical before published).crash pair (some before.wal.active.bytes) [],
        before.owners.set (directory.file .lock) none⟩ retry)
    (observedBy : ∀ {layout : CanonicalKeeperLayout retry.image before.history}
      (operations : MarkedRetryChunkOperations files directory layout),
      OpenAdmissionReports input directory operations.slot → Prop)
    (observes : ∀ layout : CanonicalKeeperLayout retry.image before.history,
      layout.keeper = before.wal.active → layout.tail = ByteArray.empty →
      layout.sealed ++ [layout.keeper] = (published.segmentedCheckpointView before.wal).readDescriptors layout.range.watermark →
      ∃ (observed : MarkedRetryChunkReports files directory layout published)
        (admission : OpenAdmissionReports input directory observed.slot),
        observedBy observed.toMarkedRetryChunkOperations admission) :
    BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
      ⟨physical before published, before.owners⟩ retry ∧
    ∃ (layout : CanonicalKeeperLayout retry.image before.history)
      (observed : MarkedRetryChunkReports files directory layout published)
      (admission : OpenAdmissionReports input directory observed.slot)
      (sizes : SizedCheckpointRunReports directory observed.reported.inventory.reports
        retry.image.directory.active.manifest published.durable)
      (opened : Reopened) (checkpoint : Option (PackedTable × UInt64)) (model : Sequential.SnapshotTable UInt64)
      (session : SegmentedSession) (final : LockedFileState FileImage),
      observed.runWithAdmission admission = .ok session final ∧
      session.directory = directory ∧ session.descriptor = observed.slot.description ∧
      session.phase = .ready opened.installed ∧ final.owners.Owns directory session.descriptor ∧
      retry.image.directory.active = pair ∧ final.image.directory.active = pair ∧ final.image.Ready layout.target ∧
      SelectedIntegrityCheckpoint published.durable pair.manifest checkpoint ∧
      sizes.readPrefix = observed.reads.readPrefix ∧
      ((opened.generation = before.installed.generation ∧ pair.manifest = before.wal.directory.active.manifest) ∨
        (opened.generation = SegmentedCheckpointReport.generation before ∧ pair.manifest = some cut.checkpoint.manifest)) ∧
      opened.walBytes.toNat = before.installed.walBytes ∧ opened.keeper = before.installed.activeFirst ∧
      recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode before.history) = .ok opened.table ∧
      opened.table.committed.toNat = before.history.length ∧ opened.table.RowBounds ∧ opened.table.Refines model ∧
      RepresentsWalHistory before.history model ∧
      ∃ after, CheckpointChunkWriter directory before published observed after ∧
        after.checkpoint = checkpoint ∧ after.installed = opened.installed ∧
        observedBy observed.toMarkedRetryChunkOperations admission := by
  obtain ⟨reached, executed, walLayout, valid, inputs, crash⟩ := cut.selectsAcknowledgedHistory ready
  have exactPublished : reached = published := Option.some.inj (executed.symm.trans projected)
  subst reached
  obtain ⟨loss, _, _, _, _, _, _, checkpoint, _, _, selected, generation, _, _, _, _⟩ := crash survives
  have lineage := failures.lineage (fun a b selectedPair => CheckpointRetryTarget.unique a b selectedPair)
  rw [physical_eq published ready] at lineage
  have crashDirectory : (published.segmentedCheckpointView before.wal).CheckpointReopenDirectory (.settled pair) :=
    .crash survives
  obtain ⟨layout, chosenPair, keeper, tail, descriptors, offsets, prepared, _, accepted⟩ :=
    published.checkpointRetryLayout walLayout valid crashDirectory inputs lineage
  obtain ⟨observed, admission, provenance⟩ := observes layout keeper tail descriptors
  have following := observed.selectedAfterWatermark offsets descriptors
  have recovered := runOpenWithInstallation_markedRetryFromChunks observed prepared.keeperPrefix prepared.newer
    following accepted ready.resumed.ordered
  obtain ⟨_, cutReady⟩ := recovered.readyForAppend accepted ready.resumed.ordered
  have sealed : retry.image.kept = (before.wal.checkpointReopenFiles before.wal.directory none).kept :=
    lineage.keepsSealed
  obtain ⟨writerSession, writerFinal, after, writerReturn, writerPath, writerDescription, writerPhase, writerFiles,
    writerOwners, writerWal, writerTarget, writerHistory, writerDurable, nextReady⟩ :=
    cutReady.writerCheckpointRetained walLayout valid ready.spans chosenPair rfl (congrArg WalSegment.first keeper) sealed
  obtain ⟨opened, loaded, model, session, final, returned, directoryExact, lock, phase, _, _, _, _, held,
    _, _, _, repaired, _, chosen, replayed, generationRead, bytes, keeperRead, committed, bounds, refines,
    represents, _⟩ := recovered
  have surviving := SegmentedCheckpointPowerLossReport.keepsSelectedPair rfl lineage
  have selectedRetry : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint :=
    surviving.symm ▸ selected
  have same := chosen.uniqueResult selectedRetry
  rw [same] at generationRead replayed
  have exactGeneration := generationRead.symm ▸ generation
  have exactBytes : opened.walBytes.toNat = before.installed.walBytes := by
    rw [bytes, ready.resumed.bytes, WAL.encode_size, Nat.mul_comm]
  have exactKeeper : opened.keeper = before.installed.activeFirst :=
    keeperRead.trans ((congrArg WalSegment.first keeper).trans (ready.resumed.keeper.trans ready.active).symm)
  have finalPair := repaired.selected.trans surviving
  let sizes := SizedCheckpointRunReports.ofChunkReads selectedRetry observed.reads observed.metadata observed.chunks
  have next : after.RetainedReady directory observed.slot.description := observed.inventoryDescription ▸ nextReady
  have writer : CheckpointChunkWriter directory before published observed after :=
    ⟨⟨writerSession, writerFinal, writerReturn, writerPath, writerDescription.trans observed.inventoryDescription,
      writerPhase, writerFiles, writerOwners⟩, writerTarget, keeper, tail, descriptors, writerHistory,
      by simpa only [writerFiles] using writerWal, writerDurable, next⟩
  have writerSelected := next.resumed.selected
  rw [writerTarget, writerDurable] at writerSelected
  have sameCheckpoint := writerSelected.uniqueResult selectedRetry
  have sameInstalled := Phase.ready.inj ((writer.atReopen returned).1.symm.trans phase)
  exact ⟨loss.trans failures, layout, observed, admission, sizes, opened, checkpoint, model, session, final,
    (observed.runWithAdmission_eq admission).trans returned, directoryExact,
    lock.trans observed.inventoryDescription, phase, held, surviving, finalPair, repaired, selected, rfl,
    exactGeneration, exactBytes, exactKeeper, replayed, committed, bounds, refines, represents,
    after, writer, sameCheckpoint, sameInstalled, provenance⟩

end Alvoki.Storage.DiskSession
