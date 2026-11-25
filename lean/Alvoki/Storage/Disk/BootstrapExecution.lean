import Alvoki.Storage.Disk.BatchRecoveryPrefix
import Alvoki.Storage.Disk.BootstrapKeeperMarkerHandoff

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
interruption and the second enters as a single uncertain group. -/
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
        GuardedClientReplay [.acknowledgedBatch acknowledged.batch, .uncertainBatch cut.batch] [] after session := by
  obtain ⟨cacheAfter, returned⟩ := written.acknowledges
  have trace : SegmentedClientReadTrace directory descriptor start.writer false
      [.acknowledgedBatch acknowledged.batch] [] descriptor (acknowledged.next target) :=
    (start.starts false).advance (.acknowledgedBatch .start acknowledged selection)
  obtain ⟨description, after, history, layout, reported, admission, session, final, opened, path, lock, phase,
    files, owners, sameHistory, retained, continued, replay⟩ :=
    trace.reopenAfterReportedBatchMarker start observed retries readAndFinish
  have batchHistory : (acknowledged.next target).history = acknowledged.batch := rfl
  exact ⟨cacheAfter, returned, description, after, history, layout, reported, admission, session, final,
    opened, path, lock, phase, files, owners, sameHistory, by simpa only [batchHistory] using retained, continued, replay⟩

end Alvoki.Storage.DiskSession
