import Alvoki.Storage.Disk.Proofs.Session.BatchRecoveryPrefix
import Alvoki.Storage.Disk.Proofs.Session.BatchInterruptionDispatch

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

namespace BatchAppendInterruption

variable {directory : DiskDirectory} {before : SegmentedWriterState} {writer : Nat}
  {report : BatchAppendInterruption directory before} {retry : LockedFileState FileImage}

/-- Every reached retry selects the prior marker's exact keeper prefix.
Neither a process exit nor a power loss during the first append publishes
any frames from the interrupted batch. -/
theorem Stop.refinesReopenPrefix
    (stop : report.Stop writer) (ready : before.RetainedReady directory writer)
    (reported : ReportedReopenPrefix directory before.wal.active.first stop.origin retry) :
    BoundedReopenTrace directory (fun target => target = before.target) stop.origin retry ∧
    BoundedReopenTrace directory (fun target => target = before.target)
      ⟨report.cut.physical before, before.owners⟩ stop.origin ∧
    retry.image.directory.active = before.target.pair ∧
    ∃ layout : CanonicalKeeperLayout retry.image before.history, PreparedRetry before layout := by
  have attempts : BoundedReopenTrace directory (fun target => target = before.target) stop.origin retry :=
    reported.refines fun earlier => by
      obtain ⟨_, layout, prepared⟩ := stop.preparesRetry ready earlier
      exact ⟨layout.target, layout.plan, prepared.target, prepared.first, prepared.prepared⟩
  obtain ⟨stopped, layout, prepared⟩ := stop.preparesRetry ready attempts
  exact ⟨attempts, stopped, prepared.prepared.pair.trans (congrArg Target.pair prepared.target), layout, prepared⟩

end BatchAppendInterruption

/-- Reopen after a reported first-append stop and finite retry prefix.
The outer batch schedule supplies the starting files and owner. The
chosen layout determines which primitive open reports to consume.
The exact returned session keeps the old history and continues the same
client ledger with one uncertain submission. -/
theorem SegmentedClientReadTrace.reopenAfterReportedBatchAppend
    {directory : DiskDirectory} {initialDescriptor writer : Nat}
    {initialResult : EStateM.Result IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession}
    (start : BootstrapClientStart directory initialDescriptor initialResult)
    {allowCollection : Bool} {log : List DatabaseSubmissions} {reads : List RecordedSnapshotRead}
    {before : SegmentedWriterState}
    (trace : SegmentedClientReadTrace directory initialDescriptor start.writer allowCollection log reads writer before)
    {report : BatchAppendInterruption directory before} (observed : report.Valid)
    (outer : report.runUntilAppend stage sync rename = .error tag reached)
    (stop : report.Stop writer) {retry : LockedFileState FileImage}
    (retries : ReportedReopenPrefix directory before.wal.active.first stop.origin retry)
    {input : FilePath}
    (readAndFinish : ∀ layout : CanonicalKeeperLayout retry.image before.history,
      BatchAppendInterruption.PreparedRetry before layout →
      Nonempty (PrimitiveCheckpointHeldOpen input directory layout before.published)) :
    tag = report.appendCall ∧ reached.1 = .poisoned ∧
    BoundedReopenTrace directory (fun target => target = before.target)
      ⟨FirstAppendCut.projectReached before reached.2.image, reached.2.owners⟩ retry ∧
    ∃ (layout : CanonicalKeeperLayout retry.image before.history)
      (primitive : PrimitiveCheckpointHeldOpen input directory layout before.published)
      (after : SegmentedWriterState) (session : SegmentedSession) (final : LockedFileState FileImage),
      primitive.toHeldOpen.chunkReports.runWithAdmission primitive.admission = .ok session final ∧
      session.directory = directory ∧ session.descriptor = primitive.calls.slot.description ∧
      session.phase = .ready after.installed ∧ final.owners.Owns directory session.descriptor ∧
      after.files = final.image ∧ after.owners = final.owners ∧ final.image.Ready before.target ∧
      after.history = before.history ∧
      SegmentedClientReadTrace directory initialDescriptor start.writer allowCollection
        (log ++ [.uncertainBatch report.batch]) reads session.descriptor after ∧
      GuardedClientReplay (log ++ [.uncertainBatch report.batch]) reads after session := by
  have ready := (trace.writes.preservesRetained (start.bootstrap.writerReady start.held).toRetained).1
  obtain ⟨attempts, stopped, _, layout, prepared⟩ := stop.refinesReopenPrefix ready retries
  obtain ⟨call, poisoned, initialFiles⟩ := observed.reachedFileState outer
  obtain ⟨primitive⟩ := readAndFinish layout prepared
  obtain ⟨after, endpoint, session, final, returned, path, lock, phase, held, files, owners, settled⟩ :=
    stop.reopensPrepared observed ready stopped attempts prepared primitive.toHeldOpen.chunkReports primitive.admission
  have continued := trace.advance (.batchAppendAdmitted .start report endpoint)
  exact ⟨call, poisoned, initialFiles.symm ▸ stopped.trans attempts, layout, primitive, after, session, final,
    returned, path, lock, phase, lock.symm ▸ held, files, owners, settled,
    endpoint.history, lock.symm ▸ continued, continued.guardedReplay start.bootstrap start.held phase⟩

end Alvoki.Storage.DiskSession
