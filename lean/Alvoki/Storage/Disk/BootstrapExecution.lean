import Alvoki.Storage.Disk.BatchRecoveryPrefix
import Alvoki.Storage.Disk.BatchInterruptionDispatch
import Alvoki.Storage.Disk.BootstrapKeeperMarkerHandoff
import Alvoki.Storage.Disk.ClientSnapshotTransitions

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair WAL.Boundary

namespace BootstrapKeeperMarkerHandoff

private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat

variable {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {calls : BootstrapOpenCalls (Cache Handle) directory before}
  {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}
  {listed : BootstrapCheckedListing captured} {keeper : BootstrapZeroKeeperRoute listed}
  {marker : BootstrapMarkerCustody listed}

/-- The reported bootstrap from an empty managed image is the first
client session. Both the initial invariant and the ready installed writer
follow from the empty image and reached keeper and marker operations. -/
theorem startFromEmpty {input : FilePath} (observed : BootstrapKeeperMarkerHandoff keeper marker)
    (admission : OpenAdmissionReports input directory calls.slot)
    (empty : before.image = ⟨DirectoryPublication.Image.settled ⟨none, none⟩, .absent⟩) :
    ∃ start : BootstrapClientStart directory calls.slot.description (calls.run admission),
      start.final.image = marker.publishedState ∧ start.writer.history = [] ∧
      observed.afterMarkerNames (renderWalSegmentName 0) = [some keeper.keeperChild] ∧
      observed.afterMarkerNames "WAL.commit" = [some marker.stageChild.child] ∧
      ((marker.inodeState.completeFileSync marker.inodeState.active).settleBinding).crashBytes
        keeper.settledImage.active = [ByteArray.empty] ∧
      ((marker.inodeState.completeFileSync marker.inodeState.active).settleBinding).crashBytes
        marker.inodeState.active = [WAL.Boundary.encode 0] := by
  have valid : BootstrapValid before.image := empty.symm ▸ bootstrap_fresh
  obtain ⟨keeperName, markerName, keeperBytes, markerBytes, after, bootstrap, returned, image, ready, _⟩ :=
    observed.installs admission valid false
  exact ⟨⟨_, after, bootstrap, returned, rfl, rfl, rfl, ready.held⟩, image, rfl,
    keeperName, markerName, keeperBytes, markerBytes⟩

end BootstrapKeeperMarkerHandoff

/-- Start from the returned bootstrap session, acknowledge a batch, and
continue from an interruption of the next batch at the writer installed
by that acknowledgement. The first batch is in the ledger before the
interruption and the second enters as a single uncertain group. The
returned session acquires a pin at its actual latest sequence and uses it
for a point or range read in the same client trace. -/
theorem BootstrapClientStart.acknowledgesThenRecovers {handle : Type} {directory : DiskDirectory}
    {descriptor : Nat} {initialResult : EStateM.Result IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession}
    (start : BootstrapClientStart directory descriptor initialResult)
    (acknowledged : SegmentedBatchAppendReport directory start.writer)
    (written : ObservedBatchWrite acknowledged handle) {target : Target}
    (selection : acknowledged.Selects target)
    {cut : SegmentedBatchMarkerPowerLossReport directory (acknowledged.next target) descriptor}
    (observed : cut.Reached) {retry : LockedFileState FileImage}
    (retries : ReportedReopenPrefix directory (acknowledged.next target).wal.active.first cut.inFlight retry)
    {input : FilePath}
    (readAndFinish : ∀ history, ∀ layout : CanonicalKeeperLayout retry.image history,
      (history = (acknowledged.next target).history ∨
        history = (acknowledged.next target).history ++ cut.batch) →
      layout.target.first = (acknowledged.next target).wal.active.first →
      Nonempty (PrimitiveCheckpointHeldOpen input directory layout (acknowledged.next target).published)) :
    ∃ cacheAfter,
      runBatchWrite directory acknowledged.rows written.guard.lookup written.append written.stage written.sync written.rename
        (.ready start.writer.installed, ⟨(written.cache, WriteFiles.initial start.writer.history
          (start.writer.files.directory.staged .walBoundary)), start.writer.owners⟩) =
        .ok acknowledged.table.committed
          (.ready (acknowledged.next target).installed, ⟨(cacheAfter, acknowledged.written), start.writer.owners⟩) ∧
      (let before := acknowledged.next target
       let scratch := before.wal.directory.staged .walBoundary
       let reached := cut.cut.interrupt (WAL.Boundary.encode cut.nextBytes.toUInt64) cut.reached
       runBatchWriteWithInterruption directory cut.rows cut.activeMetadata cut.publishUntilIssue
         (.ready before.installed, ⟨WriteFiles.initial before.history scratch, before.owners⟩) =
           .error cut.cut.action (.poisoned, ⟨reached, before.owners⟩) ∧
       cut.inFlight = ⟨before.wal.appendReopenFiles
         (reached.reopenImage (before.history.drop before.wal.active.first)
           before.wal.directory.active.manifest (before.wal.directory.staged .manifest) before.files.keeper.staged)
         before.files.keeper.staged, before.owners⟩) ∧
      ∃ (description : Nat) (after : SegmentedWriterState) (history : List WAL.Write)
        (layout : CanonicalKeeperLayout retry.image history)
        (reported : MarkedRetryChunkReports (Cache CheckpointOpenHandle) directory layout (acknowledged.next target).published)
        (admission : OpenAdmissionReports input directory reported.slot) (session : SegmentedSession)
        (final : LockedFileState FileImage),
        reported.runWithAdmission admission = .ok session final ∧
        session.directory = directory ∧ session.descriptor = description ∧ session.phase = .ready after.installed ∧
        after.files = final.image ∧ after.owners = final.owners ∧ after.history = history ∧
        (history = acknowledged.batch ∨ history = acknowledged.batch ++ cut.batch) ∧
        SegmentedClientReadTrace directory descriptor start.writer false
          [.acknowledgedBatch acknowledged.batch, .uncertainBatch cut.batch] [] description after ∧
        GuardedClientReplay [.acknowledgedBatch acknowledged.batch, .uncertainBatch cut.batch] [] after session ∧
        let snapshot := after.installed.table.committed
        ∃ (reference : Sequential.SnapshotTable UInt64) (issued : Nat × Sequential.SnapshotPin)
          (acquired : SegmentedSession) (reader : SegmentedWriterState),
          SnapshotWalReplay .empty history reference ∧
          session.runAcquireAt snapshot = .ok (some issued) acquired ∧
          issued.1 = acquired.sessionRef ∧ issued.2.sequence = snapshot ∧
          acquired = { session with phase := .ready reader.installed } ∧
          ∀ (sameSession : Bool), sameSession = decide (issued.1 = acquired.sessionRef) →
            ∀ {α : Type} (request : SnapshotReadRequest α),
              acquired.runSnapshotRead sameSession (request.read issued.2.handle) =
                .ok (some (request.replay reference snapshot)) acquired ∧
              SegmentedClientReadTrace directory descriptor start.writer false
                [.acknowledgedBatch acknowledged.batch, .uncertainBatch cut.batch]
                [request.record snapshot (request.replay reference snapshot)] description reader := by
  obtain ⟨cacheAfter, returned⟩ := written.acknowledges
  have trace : SegmentedClientReadTrace directory descriptor start.writer false
      [.acknowledgedBatch acknowledged.batch] [] descriptor (acknowledged.next target) :=
    (start.starts false).advance (.acknowledgedBatch .start acknowledged selection)
  obtain ⟨description, after, history, layout, reported, admission, session, final, opened, path, lock, phase,
    files, owners, sameHistory, retained, continued, replay⟩ :=
    trace.reopenAfterReportedBatchMarker start observed retries readAndFinish
  have batchHistory : (acknowledged.next target).history = acknowledged.batch := rfl
  have initialReady := (start.bootstrap.writerReady start.held).toRetained
  have beforeReady := (trace.writes.preservesRetained initialReady).1
  have fileStop : cut.inFlight = ⟨(acknowledged.next target).wal.appendReopenFiles
      ((cut.cut.interrupt (WAL.Boundary.encode cut.nextBytes.toUInt64) cut.reached).reopenImage
        ((acknowledged.next target).history.drop (acknowledged.next target).wal.active.first)
        (acknowledged.next target).wal.directory.active.manifest
        ((acknowledged.next target).wal.directory.staged .manifest) (acknowledged.next target).files.keeper.staged)
      (acknowledged.next target).files.keeper.staged, (acknowledged.next target).owners⟩ := by
    unfold SegmentedBatchMarkerPowerLossReport.inFlight SegmentedBatchMarkerPowerLossReport.physical
    rw [(observed.preparedHistory beforeReady).1]
  have ready := (continued.writes.preservesRetained initialReady).1
  obtain ⟨model, refined, _⟩ := ready.resumed.canonical
  have floor : after.installed.table.pins.floor ≤ after.installed.table.committed := by
    rw [refined.pins, refined.committed]
    exact model.floor_committed
  have atSession : SegmentedClientReadTrace session.directory descriptor start.writer false
      [.acknowledgedBatch acknowledged.batch, .uncertainBatch cut.batch] [] session.descriptor after := by
    simpa only [List.cons_append, List.nil_append, path, lock] using continued
  obtain ⟨reference, issued, acquired, reader, replayed, _, pinned, localToken, sequence, exactPhase, readNext⟩ :=
    replay.acquireAndRead atSession phase _ floor (UInt64.le_refl _)
  refine ⟨cacheAfter, returned, ⟨observed.stopsBatchSchedule, fileStop⟩, description, after, history, layout, reported, admission, session, final,
    opened, path, lock, phase, files, owners, sameHistory, by simpa only [batchHistory] using retained, continued, replay,
    reference, issued, acquired, reader, sameHistory ▸ replayed, pinned, localToken, sequence, exactPhase, ?_⟩
  intro sameSession compared α request
  simpa only [List.cons_append, List.nil_append, path, lock] using readNext sameSession compared request

end Alvoki.Storage.DiskSession
