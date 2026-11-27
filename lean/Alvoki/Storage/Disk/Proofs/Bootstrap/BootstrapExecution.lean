import Alvoki.Storage.Disk.BatchRecoveryPrefix
import Alvoki.Storage.Disk.BatchInterruptionDispatch
import Alvoki.Storage.Disk.Proofs.Bootstrap.BootstrapKeeperMarkerHandoff
import Alvoki.Storage.Disk.Proofs.Read.ClientSnapshotTransitions
import Alvoki.Storage.Disk.Proofs.Read.NativeReadyReadPrefix

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair WAL.Boundary

namespace BootstrapKeeperMarkerHandoff

private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat

variable {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {calls : BootstrapOpenCalls (Cache Handle) directory before}
  {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}
  {listed : BootstrapCheckedListing captured} {keeper : BootstrapZeroKeeperRoute listed}
  {marker : BootstrapMarkerCustody listed}

/-- A valid markerless bootstrap, including reuse of a surviving empty
keeper, installs the first logical client session after publishing zero. -/
theorem startFromValid {input : FilePath} (observed : BootstrapKeeperMarkerHandoff keeper marker)
    (admission : OpenAdmissionReports input directory calls.slot)
    (valid : BootstrapValid before.image) :
    ∃ start : BootstrapClientStart directory calls.slot.description (calls.run admission),
      start.session = ⟨directory, calls.slot.description, .ready (⟨.empty, 0, 0, 0⟩ : Reopened).installed,
        calls.nextRef, calls.nextRef + 1⟩ ∧
      start.final.owners = before.owners.set (directory.file .lock) (some calls.slot.description) ∧
      start.final.image = marker.publishedState ∧ start.writer.history = [] ∧
      observed.afterMarkerNames (renderWalSegmentName 0) = [some keeper.keeperChild] ∧
      observed.afterMarkerNames "WAL.commit" = [some marker.stageChild.child] ∧
      ((marker.inodeState.completeFileSync marker.inodeState.active).settleBinding).crashBytes
        keeper.settledImage.active = [ByteArray.empty] ∧
      ((marker.inodeState.completeFileSync marker.inodeState.active).settleBinding).crashBytes
        marker.inodeState.active = [WAL.Boundary.encode 0] := by
  obtain ⟨keeperName, markerName, keeperBytes, markerBytes, after, bootstrap, returned, image, ready, _⟩ :=
    observed.installs admission valid false
  have owned : after.owners = before.owners.set (directory.file .lock) (some calls.slot.description) := by
    have outcome := returned
    rw [calls.runMarkerless admission captured.captures.1, runOpenWithInstallation_outcome,
      runOpenWithImage_acquired] at outcome
    cases worker : calls.bootstrapAt directory captured.cache before.image with
    | error cause reached =>
      simp only [worker] at outcome
      cases unlock : calls.unlock <;> simp [unlock] at outcome
    | ok payload reached =>
      simp only [worker] at outcome
      exact ((congrArg LockedFileState.owners (EStateM.Result.ok.inj outcome).2).symm)
  exact ⟨⟨_, after, bootstrap, returned, rfl, rfl, rfl, ready.held⟩, rfl, owned, image, rfl,
    keeperName, markerName, keeperBytes, markerBytes⟩

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
  obtain ⟨start, _, _, rest⟩ := observed.startFromValid admission (empty.symm ▸ bootstrap_fresh)
  exact ⟨start, rest⟩

/-- The final marker close belongs to the observed file barrier. The
directory barrier then keeps the two live descriptors of this admission. -/
structure ReturnedCensus (marker : BootstrapMarkerCustody listed) where
  stageReleased : ∃ prior, marker.afterFile = prior ++ [marker.slot.closeEvent]
  directoryDrops : List LockReferenceDrop
  lockRetained : calls.slot ∈ (marker.inventory.afterDrops
    (marker.beforeFile ++ marker.afterFile ++ directoryDrops)).slots
  cacheRetained : captured.cached ∈ (marker.inventory.afterDrops
    (marker.beforeFile ++ marker.afterFile ++ directoryDrops)).slots

def ReturnedCensus.reached (effects : ReturnedCensus marker) : DescriptorInventory :=
  marker.inventory.afterDrops (marker.beforeFile ++ marker.afterFile ++ effects.directoryDrops)

theorem ReturnedCensus.stageClosed (effects : ReturnedCensus marker) :
    effects.reached.references marker.slot.description = [] := by
  obtain ⟨prior, finalized⟩ := effects.stageReleased
  unfold reached BootstrapMarkerStaging.inventory
  have ordered : marker.beforeFile ++ (prior ++ [marker.slot.closeEvent]) ++ effects.directoryDrops =
      (marker.beforeFile ++ prior ++ [marker.slot.closeEvent]) ++ effects.directoryDrops := by
    simp only [List.append_assoc]
  rw [finalized, ordered, ← DescriptorInventory.afterDrops_append, DescriptorInventory.insert_thenClose,
    DescriptorInventory.references_afterDrops, DescriptorInventory.references_afterDrops, marker.fresh]
  rfl

/-- A valid bootstrap supplies the session, file projection and empty
client ledger for the common ready prefix. The reached census includes
the actual marker allocation and its reported release. -/
theorem startsNativeReadPrefixFromValid {input : FilePath} (observed : BootstrapKeeperMarkerHandoff keeper marker)
    (admission : OpenAdmissionReports input directory calls.slot)
    (valid : BootstrapValid before.image)
    (effects : ReturnedCensus marker) :
    ∃ (start : BootstrapClientStart directory calls.slot.description (calls.run admission)),
      let state : NativeReadyState :=
        ⟨start.session, start.writer, effects.reached, captured.cache, calls.slot, captured.cached⟩
      calls.run admission = .ok state.session start.final ∧
      state.session = ⟨directory, calls.slot.description, .ready (⟨.empty, 0, 0, 0⟩ : Reopened).installed,
        calls.nextRef, calls.nextRef + 1⟩ ∧ start.final.image = marker.publishedState ∧
      start.final.owners = before.owners.set (directory.file .lock) (some calls.slot.description) ∧
      state.files.owners = start.final.owners ∧ state.files.image.directory = start.final.image.metadata ∧
      state.writer.history = [] ∧
      effects.reached.references marker.slot.description = [] ∧
      observed.afterMarkerNames (renderWalSegmentName 0) = [some keeper.keeperChild] ∧
      observed.afterMarkerNames "WAL.commit" = [some marker.stageChild.child] ∧
      ((marker.inodeState.completeFileSync marker.inodeState.active).settleBinding).crashBytes
        keeper.settledImage.active = [ByteArray.empty] ∧
      ((marker.inodeState.completeFileSync marker.inodeState.active).settleBinding).crashBytes
        marker.inodeState.active = [WAL.Boundary.encode 0] ∧
      NativeReadyReadPrefix (.ok state.session (state.census, state.files)) state [] [] [] state := by
  obtain ⟨start, session, owned, image, emptyHistory, keeperName, markerName, keeperBytes, markerBytes⟩ :=
    observed.startFromValid admission valid
  let state : NativeReadyState :=
    ⟨start.session, start.writer, effects.reached, captured.cache, calls.slot, captured.cached⟩
  have ready := (start.bootstrap.writerReady start.held).toRetained
  have readyValid : state.Valid :=
    ⟨start.installed, start.lockDescription.symm, effects.lockRetained, effects.cacheRetained,
      ⟨captured.reached, rfl⟩, start.canonicalDirectory.symm ▸ start.lockDescription.symm ▸ ready⟩
  have pending : PendingClientReplay [] [] [] := ⟨.empty, .nil _, .start, .slnil, .slnil, by simp⟩
  exact ⟨start, start.returned, session, image, owned, rfl, rfl, emptyHistory, effects.stageClosed,
    keeperName, markerName, keeperBytes, markerBytes, .installed rfl readyValid emptyHistory pending (by simp)⟩

theorem startsNativeReadPrefixFromEmpty {input : FilePath} (observed : BootstrapKeeperMarkerHandoff keeper marker)
    (admission : OpenAdmissionReports input directory calls.slot)
    (empty : before.image = ⟨DirectoryPublication.Image.settled ⟨none, none⟩, .absent⟩)
    (effects : ReturnedCensus marker) :
    ∃ (start : BootstrapClientStart directory calls.slot.description (calls.run admission)),
      let state : NativeReadyState :=
        ⟨start.session, start.writer, effects.reached, captured.cache, calls.slot, captured.cached⟩
      calls.run admission = .ok state.session start.final ∧
      state.files.owners = start.final.owners ∧ state.files.image.directory = start.final.image.metadata ∧
      state.writer.history = [] ∧
      effects.reached.references marker.slot.description = [] ∧
      observed.afterMarkerNames (renderWalSegmentName 0) = [some keeper.keeperChild] ∧
      observed.afterMarkerNames "WAL.commit" = [some marker.stageChild.child] ∧
      ((marker.inodeState.completeFileSync marker.inodeState.active).settleBinding).crashBytes
        keeper.settledImage.active = [ByteArray.empty] ∧
      ((marker.inodeState.completeFileSync marker.inodeState.active).settleBinding).crashBytes
        marker.inodeState.active = [WAL.Boundary.encode 0] ∧
      NativeReadyReadPrefix (.ok state.session (state.census, state.files)) state [] [] [] state := by
  obtain ⟨start, returned, _, _, _, rest⟩ := observed.startsNativeReadPrefixFromValid admission (empty.symm ▸ bootstrap_fresh) effects
  exact ⟨start, returned, rest⟩

end BootstrapKeeperMarkerHandoff

/-- Start from the returned bootstrap session, acknowledge a batch, and
continue from an interruption of the next single or batch write at the
writer installed by that acknowledgement. The first batch is in the ledger before the
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
    (observed : cut.Reached) (request : WriteRequest) (rows : request.rows = cut.rows)
    {retry : LockedFileState FileImage}
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
       request.runWithInterruption directory cut.activeMetadata cut.publishUntilIssue
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
  refine ⟨cacheAfter, returned, ⟨observed.stopsWriteRequest request rows, fileStop⟩, description, after, history, layout, reported, admission, session, final,
    opened, path, lock, phase, files, owners, sameHistory, by simpa only [batchHistory] using retained, continued, replay,
    reference, issued, acquired, reader, sameHistory ▸ replayed, pinned, localToken, sequence, exactPhase, ?_⟩
  intro sameSession compared α request
  simpa only [List.cons_append, List.nil_append, path, lock] using readNext sameSession compared request

end Alvoki.Storage.DiskSession
