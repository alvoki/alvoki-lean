import Alvoki.Storage.Disk.Proofs.Write.ReturnedWriteRecovery
import Alvoki.Storage.Disk.Proofs.Append.BatchAppendRecoveryPrefix

namespace Alvoki.Storage.DiskSession

open Sequential WalSegmentRepair
open scoped List

/-- A selected history accounts for every submitted group and explains
the prior client responses without needing a returned ready session. -/
def PendingClientReplay (log : List DatabaseSubmissions) (reads : List RecordedSnapshotRead)
    (history : List WAL.Write) : Prop :=
  ∃ reference : SnapshotTable UInt64,
    SnapshotWalReplay .empty history reference ∧ DatabaseBatchRetention log history ∧
    log.flatMap DatabaseSubmissions.acknowledged <+ history ∧
    history <+ log.flatMap DatabaseSubmissions.submitted ∧
    ∀ read ∈ reads, read.agrees reference

theorem SegmentedClientReadTrace.replaysUncertainSubmission
    {directory : DiskDirectory} {first writer : Nat}
    {initial : EStateM.Result IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession}
    (start : BootstrapClientStart directory first initial)
    (trace : SegmentedClientReadTrace directory first start.writer allowCollection log reads writer before)
    {history batch : List WAL.Write}
    (selected : history = before.history ∨ history = before.history ++ batch)
    (ordered : WAL.OrdinalsFrom 1 history) :
    PendingClientReplay (log ++ [.uncertainBatch batch]) reads history := by
  obtain ⟨_, _, previouslyRetained, _, _, _⟩ := trace.keyValueRefinement start.bootstrap start.held
  obtain ⟨reference, replayed⟩ := SnapshotWalReplay.fromEmpty history ordered
  have initialReady := (start.bootstrap.writerReady start.held).toRetained
  obtain ⟨trailing, equalHistory, retainedTail⟩ :
      ∃ trailing, history = before.history ++ trailing ∧
        (DatabaseSubmissions.uncertainBatch batch).Retains trailing := by
    rcases selected with old | whole
    · exact ⟨[], by simpa only [List.append_nil] using old, .inl rfl⟩
    · exact ⟨batch, whole, .inr rfl⟩
  subst history
  have retained := DatabaseBatchRetention.append previouslyRetained retainedTail
  exact ⟨reference, replayed, retained, retained.orderedSubmissions.1, retained.orderedSubmissions.2,
    trace.responsesForReplay initialReady replayed⟩

/-- The visible marker and exact retained prefix of an interrupted batch
already select a replay for the earlier reads, including when all the
reported reopen attempts so far have failed. -/
theorem SegmentedClientReadTrace.replaysPendingBatchMarker
    {directory : DiskDirectory} {first writer : Nat} {before : SegmentedWriterState}
    {initial : EStateM.Result IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession}
    (start : BootstrapClientStart directory first initial)
    (trace : SegmentedClientReadTrace directory first start.writer allowCollection log reads writer before)
    {cut : SegmentedBatchMarkerPowerLossReport directory before writer} (observed : cut.Reached)
    {retry : LockedFileState FileImage}
    (retries : ReportedReopenPrefix directory before.wal.active.first cut.inFlight retry) :
    retry.image.kept = cut.inFlight.image.kept ∧
    retry.image.directory.active.manifest = before.wal.directory.active.manifest ∧
    ∃ history, (history = before.history ∨ history = before.history ++ cut.batch) ∧
      retry.image.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64) ∧
      PendingClientReplay (log ++ [.uncertainBatch cut.batch]) reads history ∧
      ∃ layout : CanonicalKeeperLayout retry.image history,
        layout.target.first = before.wal.active.first ∧ Prepared retry.image layout.target layout.plan := by
  have ready := (trace.writes.preservesRetained (start.bootstrap.writerReady start.held).toRetained).1
  obtain ⟨_, kept, manifest, history, selected, marker, layout⟩ := observed.refinesReopenPrefix ready retries
  refine ⟨kept, manifest, history, selected, marker, trace.replaysUncertainSubmission start selected ?_, layout⟩
  rcases selected with rfl | rfl
  · exact ready.resumed.ordered
  · exact (observed.preparedHistory ready).2.2

/-- The reported write error supplies its exact held origin for later
retry events. The selected history already accounts for the whole
uncertain submission or none of it at that origin. -/
theorem SegmentedClientReadTrace.replaysPendingWriteError
    {handle : Type} {directory : DiskDirectory} {first writer : Nat} {before : SegmentedWriterState}
    {initial : EStateM.Result IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession}
    (start : BootstrapClientStart directory first initial)
    (trace : SegmentedClientReadTrace directory first start.writer allowCollection log reads writer before)
    (request : WriteRequest) (failure : SegmentedBatchFailure directory before)
    (observed : ObservedBatchFailure failure handle) (rows : request.rows = failure.rows)
    {retry : LockedFileState FileImage}
    (retries : ReportedReopenPrefix directory before.wal.active.first ⟨failure.released.image, before.owners⟩ retry) :
    ∃ cacheAfter, (WriteRequest.Calls.ofFailure observed).run request directory before =
      .error (.commitUnknown failure.cause) (.poisoned, ⟨(cacheAfter, failure.failed), before.owners⟩) ∧
    retry.image.kept = failure.released.image.kept ∧
    retry.image.directory.active.manifest = before.wal.directory.active.manifest ∧
    ∃ history, (history = before.history ∨ history = before.history ++ failure.batch) ∧
      retry.image.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64) ∧
      PendingClientReplay (log ++ [.uncertainBatch failure.batch]) reads history ∧
      ∃ layout : CanonicalKeeperLayout retry.image history,
        layout.target.first = before.wal.active.first ∧ Prepared retry.image layout.target layout.plan := by
  have ready := (trace.writes.preservesRetained (start.bootstrap.writerReady start.held).toRetained).1
  obtain ⟨cacheAfter, returned⟩ := observed.commitUnknown
  have same := request.runReported_eq_batch ready
    (WriteRequest.readyCall (handle := handle) before observed.cache).2
    observed.guard.lookup observed.append observed.stage observed.sync observed.rename
  change (WriteRequest.Calls.ofFailure observed).run request directory before = _ at same
  simp only [← ready.directoryFiles] at returned
  rw [rows] at same
  obtain ⟨_, kept, manifest, history, selected, marker, layout⟩ := failure.refinesReopenPrefix ready retries
  refine ⟨cacheAfter, same.trans returned, kept, manifest, history, selected, marker,
    trace.replaysUncertainSubmission start selected ?_, layout⟩
  rcases selected with rfl | rfl
  · exact ready.resumed.ordered
  · obtain ⟨_, refined, represented⟩ := ready.resumed.canonical
    have count : before.history.length = before.installed.table.committed.toNat :=
      represented.committed_count.symm.trans (congrArg UInt64.toNat refined.committed).symm
    exact (prepareBatch_extends_history ready.resumed.ordered count failure.prepared).2.1

/-- A stop during the first append keeps the earlier marker and replay.
The pending submission contributes no frames because its marker was never issued. -/
theorem SegmentedClientReadTrace.replaysPendingFirstAppend
    {directory : DiskDirectory} {first writer : Nat} {before : SegmentedWriterState}
    {initial : EStateM.Result IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession}
    (start : BootstrapClientStart directory first initial)
    (trace : SegmentedClientReadTrace directory first start.writer allowCollection log reads writer before)
    {report : BatchAppendInterruption directory before} (observed : report.Valid)
    (outer : report.runUntilAppend stage sync rename = .error tag reached)
    (stop : report.Stop writer) {retry : LockedFileState FileImage}
    (retries : ReportedReopenPrefix directory before.wal.active.first stop.origin retry) :
    tag = report.appendCall ∧ reached.1 = .poisoned ∧
    BoundedReopenTrace directory (fun target => target = before.target)
      ⟨FirstAppendCut.projectReached before reached.2.image, reached.2.owners⟩ retry ∧
    retry.image.directory.active = before.target.pair ∧
    PendingClientReplay (log ++ [.uncertainBatch report.batch]) reads before.history ∧
    ∃ layout : CanonicalKeeperLayout retry.image before.history, BatchAppendInterruption.PreparedRetry before layout := by
  have ready := (trace.writes.preservesRetained (start.bootstrap.writerReady start.held).toRetained).1
  obtain ⟨call, poisoned, initialFiles⟩ := observed.reachedFileState outer
  obtain ⟨attempts, stopped, pair, layout⟩ := stop.refinesReopenPrefix ready retries
  exact ⟨call, poisoned, initialFiles.symm ▸ stopped.trans attempts, pair,
    trace.replaysUncertainSubmission start (.inl rfl) ready.resumed.ordered, layout⟩

/-- The replay explaining the pending client history also explains
new guarded reads in this exact returned cached session. Both the
selected checkpoint and returned table refer to that same history. -/
theorem _root_.Alvoki.Storage.WalSegmentRepair.CachedRetryInstalled.refinesPendingClient
    {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout before.image history} {reported : CachedRetryReadReports directory layout}
    {descriptors slot bindings published liveRefs result}
    (installed : CachedRetryInstalled reported descriptors slot bindings published liveRefs result)
    (pending : PendingClientReplay log reads history) :
    ∃ (session : SegmentedSession) (final : LockedFileState FileImage)
      (ready : Installed) (checkpoint : Option (PackedTable × UInt64)),
      result = .ok session final ∧ session.phase = .ready ready ∧
      SelectedIntegrityCheckpoint published.durable before.image.directory.active.manifest checkpoint ∧
      recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode history) = .ok ready.table ∧
      InstalledClientReplay log reads history ready session := by
  obtain ⟨opened, checkpoint, model, session, final, returned, _, _, phase, _, _, _, _, _, _, _, _, _, _,
    selected, recovered, _, _, _, _, bounds, refined, represented, _⟩ := installed
  obtain ⟨reference, replayed, retained, acknowledged, submitted, priorReads⟩ := pending
  have guarded := session.guardedAcquireReads phase fun _ floor committed =>
    represented.acquireReads refined bounds replayed floor committed
  exact ⟨session, final, opened.installed, checkpoint, returned, phase, selected, recovered,
    reference, replayed, retained, acknowledged, submitted, priorReads, guarded⟩

end Alvoki.Storage.DiskSession
