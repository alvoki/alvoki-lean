import Alvoki.Storage.Disk.MarkedSessionTrace
import Alvoki.Storage.Disk.Proofs.Collection.SegmentedCollectionPowerLoss
import Alvoki.Storage.Disk.Proofs.Collection.SegmentedCollectionRetry
import Alvoki.Storage.Disk.Proofs.Collection.SegmentedCollectionLiveReopen
import Alvoki.Storage.Disk.Proofs.Collection.SegmentedCollectionCachedReopen
import Alvoki.Storage.Disk.Proofs.Collection.SegmentedRunCollection
import Alvoki.Storage.Disk.Proofs.Append.SegmentedAppendRecovery
import Alvoki.Storage.Disk.Proofs.Append.SegmentedAppendPowerLoss
import Alvoki.Storage.Disk.SegmentedCheckpointRecovery
import Alvoki.Storage.Disk.SegmentedCheckpointPowerLoss
import Alvoki.Storage.Disk.SegmentedCleanReopen
import Alvoki.Storage.Disk.Proofs.Append.SegmentedDelayedAppendReopen
import Alvoki.Storage.Disk.SegmentedDelayedKeeperPowerLoss
import Alvoki.Storage.Disk.SegmentedMarkerPowerLoss
import Alvoki.Storage.Disk.SegmentedReadyPowerLoss
import Alvoki.Storage.Disk.Proofs.Rotation.SegmentedRotationRecovery
import Alvoki.Storage.Disk.Proofs.Rotation.SegmentedRotationPowerLoss
import Alvoki.Storage.Disk.Proofs.Rotation.SegmentedRotationStep
import Alvoki.Storage.Disk.Proofs.Write.SegmentedWriterTrace
import Alvoki.Storage.Disk.SessionReadGuards
import Alvoki.Storage.Disk.WalSegmentCachedExtentReports

namespace Alvoki.Storage.DiskSession

open System WAL.Boundary WalSegmentRepair Sequential
open scoped List

/-- Completed stretches and reported reopenings of one directory. A
recovered writer is the exact predecessor of its next operation. The log
accounts for write submissions separately from ownership changes.
With WAL collection disabled, the trace also preserves the full WAL chain. -/
inductive SegmentedDatabaseTrace (directory : DiskDirectory) (initialDescriptor : Nat)
    (initial : SegmentedWriterState) (allowCollection : Bool) : List MarkedSessionWrites → Nat → SegmentedWriterState → Prop where
  | start : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection [] initialDescriptor initial
  | writes {log descriptor before after acknowledged checkpoints}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor before)
      (writer : SegmentedWriterTrace directory descriptor before acknowledged checkpoints after) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection (log ++ [⟨acknowledged, none⟩]) descriptor after
  | rotate {log descriptor before target}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor before)
      (report : SegmentedRotationReport directory before) (selected : report.Selects target) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor (report.next target)
  | close {log writer descriptor before after}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedCleanReopenReport directory before writer descriptor)
      (observed : report.Valid) (endpoint : report.Installs after) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after
  | powerLoss {log writer descriptor before after}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedReadyPowerLossReport directory before writer descriptor)
      (observed : report.Valid) (endpoint : report.Installs after) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after
  | appendError {log writer descriptor before after}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedAppendRecoveryReport directory before writer descriptor)
      (endpoint : report.Installs after) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection (log ++ [⟨[], some report.failure.event⟩]) descriptor after
  | delayedDirectoryAppend {log writer descriptor before after}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (failure : SegmentedAppendFailure directory before) (barrier : DelayedDirectorySync directory)
      (references : HeldLockReferences writer) (last : references.remaining barrier.drops = [])
      (handoff : barrier.AppendHandoff failure references last)
      {retry : LockedFileState FileImage}
      (attempts : BoundedReopenTrace directory (AppendRetryTarget before.history failure.event before.wal.active.first)
        (barrier.after failure.released) retry)
      {reopen : BoundedReopenAttempt} {recover : EStateM IO.Error FileImage Reopened}
      (reads : DelayedDirectorySync.CachedAppendReads (descriptor := descriptor) failure retry reopen recover)
      (endpoint : AppendRetryEndpoint directory before failure.event retry descriptor
        (runOpenWithInstallation directory reopen.descriptor reopen.nextRef reopen.acquired reopen.unlock recover retry) after)
      (ready : after.RetainedReady directory descriptor) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection (log ++ [⟨[], some failure.event⟩]) descriptor after
  | delayedKeeperPowerLoss {log writer descriptor before after}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (failure : SegmentedAppendFailure directory before) (release : SegmentedFailureRelease writer)
      (released : release.Observed (directory := directory) failure.poisoned
        ⟨failure.failed, before.owners.set (directory.file .lock) none⟩)
      (cut : DelayedKeeperReplacementPowerLoss directory failure.released
        (AppendRetryTarget before.history failure.event before.wal.active.first))
      {retry : LockedFileState FileImage}
      (attempts : BoundedReopenTrace directory (AppendRetryTarget before.history failure.event before.wal.active.first)
        cut.crashed retry)
      (pair : retry.image.directory.active = cut.pair)
      {nextRef : Nat} {unlock : UnlockReport}
      {removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit)}
      {write : FilePath → ByteArray → EStateM IO.Error FileImage Unit}
      {sync : Array FilePath → EStateM IO.Error FileImage Unit}
      {renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit}
      {history : List WAL.Write} {selected : CanonicalKeeperLayout retry.image history}
      {raw : HealthyBoundedWalReports directory (retry.owners.set (directory.file .lock) (some descriptor)) descriptor
        (before.wal.appendSelectedView retry.image.directory.active history) retry.image.directory.active
        selected.range.watermark before.published.durable selected.tail}
      {sizes : SizedCheckpointRunReports directory raw.reports retry.image.directory.active.manifest before.published.durable}
      {cached : CachedWalFileReports directory raw.reports (before.wal.appendSelectedView retry.image.directory.active history)
        selected.range.watermark selected.tail}
      (endpoint : AppendRetryEndpoint directory before failure.event retry descriptor
        (runOpenWithInstallation directory descriptor nextRef (.ok true) unlock
          (raw.reopenCached sizes cached removeFile write sync renameFile) retry) after)
      (selectedHistory : after.history = history)
      (ready : after.RetainedReady directory descriptor) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection (log ++ [⟨[], some failure.event⟩]) descriptor after
  | appendPowerLoss {log writer descriptor before after}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedAppendPowerLossReport directory before writer descriptor)
      (observed : report.Valid) (endpoint : report.Installs after) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection (log ++ [⟨[], some report.event⟩]) descriptor after
  | markerPowerLoss {log writer descriptor before after}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedMarkerPowerLossReport directory before writer descriptor)
      (observed : report.Valid) (endpoint : report.Installs after) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection (log ++ [⟨[], some report.event⟩]) descriptor after
  | checkpointError {log writer descriptor before after}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedCheckpointFailure directory before writer descriptor)
      (endpoint : report.Installs after) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after
  | checkpointPowerLoss {log writer descriptor before after}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedCheckpointPowerLossReport directory before writer descriptor)
      (observed : report.Valid) (endpoint : report.Installs after) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after
  | rotationError {log writer descriptor before after}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedRotationRecoveryReport directory before descriptor)
      (release : SegmentedFailureRelease writer)
      (observed : release.Observed (directory := directory) report.failure.poisoned report.failure.released)
      (endpoint : SegmentedRotationReopened directory descriptor before after report.run) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after
  | rotationPowerLoss {log writer descriptor before after}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedRotationPowerLossReport directory before descriptor)
      (endpoint : report.Installs after) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after
  | collectionPowerLoss {log writer descriptor before after}
      (enabled : allowCollection = true)
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedCollectionPowerLossReport directory before writer descriptor)
      (observed : report.Valid) (endpoint : report.Installs after) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after
  | collection {log descriptor before after}
      (enabled : allowCollection = true)
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor before)
      (report : SegmentedCollectionReport directory before) (endpoint : report.Installs after) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after
  | collectionRetry {log descriptor before reached remaining}
      (enabled : allowCollection = true)
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor before)
      (failed : SegmentedCollectionErrors directory before reached)
      (report : SegmentedCollectionReport directory before) (returned : report.runFrom reached = .ok () remaining) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor
        (before.afterWalCollection remaining)
  | collectionReopen {log writer descriptor before after}
      (enabled : allowCollection = true)
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedCollectionReopenReport directory before writer descriptor)
      (observed : report.Valid) (endpoint : report.Installs after) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after
  | collectRuns {log descriptor before} {runs : CheckpointPublication.RunUnlinkImage}
      (enabled : allowCollection = true)
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor before)
      (reports : SegmentedRunCollectionReports directory before runs) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor
        (before.afterRunCollection reports.reached.guaranteed)

private theorem retainsInterruptedAppend {initial before after : List WAL.Write} {log retained event}
    (history : before = initial ++ retained) (submitted : MarkedSessionRetention log retained)
    (survived : after = before ∨ after = before ++ [event]) :
    ∃ suffix, after = initial ++ suffix ∧ MarkedSessionRetention (log ++ [⟨[], some event⟩]) suffix := by
  rcases survived with lost | kept
  · exact ⟨retained ++ [], by simpa using lost.trans history, submitted.append (Or.inl rfl)⟩
  · refine ⟨retained ++ [event], by rw [kept, history, List.append_assoc], ?_⟩
    exact submitted.append (Or.inr ⟨event, rfl, rfl⟩)

private theorem AppendRetryEndpoint.preservesChain {directory before event retry descriptor result after}
    (endpoint : AppendRetryEndpoint directory before event retry descriptor result after)
    (layout : before.wal.ReadLayout before.history) (chain : WalSegment.Chain before.history 0 before.wal.segments) :
    WalSegment.Chain after.history 0 after.wal.segments := by
  rw [endpoint.wal]
  change WalSegment.Chain after.history 0 (before.wal.appendSelectedView retry.image.directory.active after.history).segments
  rcases endpoint.history with unchanged | extended
  · rw [unchanged]
    change WalSegment.Chain before.history 0 (before.wal.sealed ++
      [⟨before.wal.active.first, before.history.length, WAL.encode (before.history.drop before.wal.active.first)⟩])
    rw [← layout.activeEnd, ← layout.activeBytes]
    exact chain
  · rw [extended]
    exact (layout.afterAcknowledgedAppend chain retry.image.directory.active event).2.1

/-- Thread readiness and acknowledged history once. When collection is
disabled, the same steps also propagate evidence for the full chain. -/
private theorem SegmentedDatabaseTrace.preservesReadiness {directory initialDescriptor initial allowCollection log descriptor last}
    (trace : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor last)
    (ready : initial.RetainedReady directory initialDescriptor) :
    last.RetainedReady directory descriptor ∧
      (allowCollection = false → WalSegment.Chain initial.history 0 initial.wal.segments →
        WalSegment.Chain last.history 0 last.wal.segments) ∧
      ∃ retained, last.history = initial.history ++ retained ∧ MarkedSessionRetention log retained := by
  induction trace with
  | start => exact ⟨ready, fun _ chain => chain, [], by simp, .start⟩
  | writes _ writer ih =>
    obtain ⟨before, fullChain, retained, history, submitted⟩ := ih
    obtain ⟨ready, appended, _, _, appendedChain⟩ := writer.preservesRetainedWithChain before
    exact ⟨ready, fun disabled chain => appendedChain (fullChain disabled chain),
      _, by rw [appended, history, List.append_assoc], submitted.append (Or.inl rfl)⟩
  | rotate _ report selected ih =>
    obtain ⟨before, fullChain, retained, history, submitted⟩ := ih
    refine ⟨report.preservesRetainedReady before selected, ?_, retained, history, submitted⟩
    intro disabled initialChain
    have full := before.withChain (fullChain disabled initialChain)
    exact (report.preservesReady full selected).chain
  | close _ _ observed endpoint ih =>
    obtain ⟨before, fullChain, retained, history, submitted⟩ := ih
    refine ⟨endpoint.preservesRetained observed before, ?_, retained, endpoint.history.trans history, submitted⟩
    intro disabled initialChain
    exact endpoint.preservesChain (fullChain disabled initialChain)
  | powerLoss _ _ observed endpoint ih =>
    obtain ⟨before, fullChain, retained, history, submitted⟩ := ih
    refine ⟨endpoint.preservesRetained observed before, ?_, retained, endpoint.history.trans history, submitted⟩
    intro disabled initialChain
    exact endpoint.preservesChain (fullChain disabled initialChain)
  | appendError _ _ endpoint ih =>
    obtain ⟨before, fullChain, retained, history, submitted⟩ := ih
    refine ⟨endpoint.preservesRetained before, ?_, retainsInterruptedAppend history submitted endpoint.history⟩
    intro disabled initialChain
    have full := before.withChain (fullChain disabled initialChain)
    exact (endpoint.preservesReady full).chain
  | delayedDirectoryAppend _ _ _ _ _ _ _ _ endpoint next ih =>
    obtain ⟨before, fullChain, _, history, submitted⟩ := ih
    exact ⟨next, fun disabled initialChain => endpoint.preservesChain before.layout (fullChain disabled initialChain),
      retainsInterruptedAppend history submitted endpoint.history⟩
  | delayedKeeperPowerLoss _ _ _ _ _ _ _ endpoint _ next ih =>
    obtain ⟨before, fullChain, _, history, submitted⟩ := ih
    exact ⟨next, fun disabled initialChain => endpoint.preservesChain before.layout (fullChain disabled initialChain),
      retainsInterruptedAppend history submitted endpoint.history⟩
  | appendPowerLoss _ _ observed endpoint ih =>
    obtain ⟨before, fullChain, retained, history, submitted⟩ := ih
    refine ⟨endpoint.preservesRetained observed before, ?_, retainsInterruptedAppend history submitted (.inl endpoint.history)⟩
    intro disabled initialChain
    exact endpoint.preservesChain (fullChain disabled initialChain)
  | markerPowerLoss _ _ observed endpoint ih =>
    obtain ⟨before, fullChain, retained, history, submitted⟩ := ih
    refine ⟨endpoint.preservesRetained observed before, ?_, retainsInterruptedAppend history submitted endpoint.history⟩
    intro disabled initialChain
    have full := before.withChain (fullChain disabled initialChain)
    exact (endpoint.preservesReady observed full).chain
  | checkpointError _ _ endpoint ih =>
    obtain ⟨before, fullChain, retained, history, submitted⟩ := ih
    refine ⟨endpoint.preservesRetained before, ?_, retained, endpoint.history.trans history, submitted⟩
    intro disabled initialChain
    exact endpoint.toSegmentedCheckpointReopened.preservesChain (fullChain disabled initialChain)
  | checkpointPowerLoss _ _ observed endpoint ih =>
    obtain ⟨before, fullChain, retained, history, submitted⟩ := ih
    refine ⟨endpoint.preservesRetained observed before, ?_, retained, endpoint.history.trans history, submitted⟩
    intro disabled initialChain
    exact endpoint.toSegmentedCheckpointReopened.preservesChain (fullChain disabled initialChain)
  | rotationError _ _ _ _ endpoint ih =>
    obtain ⟨before, fullChain, retained, history, submitted⟩ := ih
    refine ⟨endpoint.preservesRetainedReady before, ?_, retained, endpoint.history.trans history, submitted⟩
    intro disabled initialChain
    have full := before.withChain (fullChain disabled initialChain)
    exact (endpoint.preservesReady full).chain
  | rotationPowerLoss _ _ endpoint ih =>
    obtain ⟨before, fullChain, retained, history, submitted⟩ := ih
    refine ⟨endpoint.preservesRetainedReady before, ?_, retained, endpoint.history.trans history, submitted⟩
    intro disabled initialChain
    have full := before.withChain (fullChain disabled initialChain)
    exact (endpoint.preservesReady full).chain
  | collectionPowerLoss enabled _ _ observed endpoint ih =>
    obtain ⟨before, _, retained, history, submitted⟩ := ih
    exact ⟨endpoint.preservesRetained observed before,
      (fun disabled => by simp [disabled] at enabled), retained, endpoint.history.trans history, submitted⟩
  | collection enabled _ _ endpoint ih =>
    obtain ⟨before, _, retained, history, submitted⟩ := ih
    exact ⟨endpoint.preservesRetained before,
      (fun disabled => by simp [disabled] at enabled), retained, endpoint.history.trans history, submitted⟩
  | collectionRetry enabled _ failed report returned ih =>
    obtain ⟨before, _, retained, history, submitted⟩ := ih
    exact ⟨(failed.settles before report returned).2,
      (fun disabled => by simp [disabled] at enabled), retained, history, submitted⟩
  | collectionReopen enabled _ _ observed endpoint ih =>
    obtain ⟨before, _, retained, history, submitted⟩ := ih
    exact ⟨endpoint.preservesRetained observed before,
      (fun disabled => by simp [disabled] at enabled), retained, endpoint.history.trans history, submitted⟩
  | collectRuns _ _ reports ih =>
    obtain ⟨before, fullChain, retained, history, submitted⟩ := ih
    exact ⟨(reports.preservesRetained before).1, fullChain, retained, history, submitted⟩

theorem SegmentedDatabaseTrace.preservesReady {directory initialDescriptor initial log descriptor last}
    (trace : SegmentedDatabaseTrace directory initialDescriptor initial false log descriptor last)
    (ready : initial.Ready directory initialDescriptor) :
    last.Ready directory descriptor ∧
      ∃ retained, last.history = initial.history ++ retained ∧ MarkedSessionRetention log retained := by
  obtain ⟨retained, fullChain, history⟩ := trace.preservesReadiness ready.toRetained
  exact ⟨retained.withChain (fullChain rfl ready.chain), history⟩

theorem SegmentedDatabaseTrace.preservesRetained {directory initialDescriptor initial allowCollection log descriptor last}
    (trace : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor last)
    (ready : initial.RetainedReady directory initialDescriptor) :
    last.RetainedReady directory descriptor ∧
      ∃ retained, last.history = initial.history ++ retained ∧ MarkedSessionRetention log retained := by
  obtain ⟨retained, _, history⟩ := trace.preservesReadiness ready
  exact ⟨retained, history⟩

/-- A history from the first installed empty writer retains all
acknowledgements in order. It may retain the uncertain append at a
session boundary, and every retained frame is one that was submitted. -/
theorem SegmentedDatabaseTrace.fromBootstrap {directory initialDescriptor allowCollection log descriptor last}
    {first : LockedFileState WalSegmentRotation.State} (bootstrap : BootstrapReady first.image)
    (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedDatabaseTrace directory initialDescriptor (bootstrap.writerState first.owners) allowCollection log descriptor last) :
    last.RetainedReady directory descriptor ∧ MarkedSessionRetention log last.history ∧
      log.flatMap MarkedSessionWrites.acknowledged <+ last.history ∧
      last.history <+ log.flatMap MarkedSessionWrites.submitted := by
  obtain ⟨ready, retained, exactHistory, history⟩ := trace.preservesRetained (bootstrap.writerReady held).toRetained
  change last.history = [] ++ retained at exactHistory
  simp only [List.nil_append] at exactHistory
  subst retained
  exact ⟨ready, history, history.orderedSubmissions⟩

/-- Extend the mixed history with the actual cached bounded opener after an
admitted WAL unlink cut. The successful installation follows from the reached
files and reports on that attempt. -/
theorem SegmentedDatabaseTrace.collectionPowerLossCached {directory initialDescriptor initial log writer descriptor before}
    (prior : SegmentedDatabaseTrace directory initialDescriptor initial true log writer before)
    (initialReady : initial.RetainedReady directory initialDescriptor)
    (report : SegmentedCollectionPowerLossReport directory before writer descriptor)
    (sizes : SizedCheckpointRunReports directory report.raw.reports report.pair.manifest before.published.durable)
    (cached : CachedWalFileReports directory report.raw.reports report.survivors before.target.range.watermark ByteArray.empty)
    (descriptorEq : report.reopen.descriptor = descriptor) (acquired : report.reopen.acquired = .ok true)
    (reads : report.reopen.recover directory = report.raw.reopenCached sizes cached
      report.reopen.removeFile report.reopen.write report.reopen.sync report.reopen.renameFile)
    (fresh : ∀ ref ∈ report.liveRefs, ref < report.reopen.nextRef)
    (syncDirectory : report.reopen.sync #[directory.path] report.crashed.image = .ok () report.crashed.image.syncDirectory)
    (syncKeeper : report.reopen.sync #[directory.file (.walSegment report.survivors.active.first)]
      report.crashed.image.syncDirectory = .ok () report.crashed.image.syncDirectory.syncKeeper) :
    ∃ after, report.Installs after ∧ SegmentedDatabaseTrace directory initialDescriptor initial true log descriptor after := by
  have ready := (prior.preservesRetained initialReady).1
  have sameAction := ready.collectionPowerLossCached_eq report.reached report.pairSurvives report.sealedSurvives
    report.raw sizes cached report.reopen.removeFile report.reopen.write report.reopen.sync report.reopen.renameFile
  have observed : report.Valid := ⟨descriptorEq, acquired, reads.trans sameAction, fresh, syncDirectory, syncKeeper⟩
  obtain ⟨after, installed, _⟩ := report.installs observed ready
  exact ⟨after, installed, .collectionPowerLoss rfl prior report observed installed⟩

/-- After reported WAL collection failures, use the cached session and
the namespace settled by its reached directory barrier in the mixed trace. -/
theorem SegmentedDatabaseTrace.collectionReopenCachedWithNamespace
    {directory initialDescriptor initial log writer descriptor before}
    (prior : SegmentedDatabaseTrace directory initialDescriptor initial true log writer before)
    (initialReady : initial.RetainedReady directory initialDescriptor)
    (report : SegmentedCollectionReopenReport directory before writer descriptor) (observed : report.Valid)
    (sizes : SizedCheckpointRunReports directory report.raw.reports
      report.pending.image.visible.directory.active.manifest before.published.durable)
    (cached : CachedWalFileReports directory report.raw.reports report.pending.image.visible
      before.target.range.watermark ByteArray.empty) :
    ∃ after session final,
      SegmentedDatabaseTrace directory initialDescriptor initial true log descriptor after ∧
      runOpenWithInstallation directory report.reopen.descriptor report.reopen.nextRef report.reopen.acquired
        report.reopen.unlock (report.reopenCachedWithNamespace sizes cached)
        ⟨(report.files.image, report.pending.image), report.pending.owners⟩ = .ok session final ∧
      session.phase = .ready after.installed ∧ final.image.1 = after.files ∧ final.owners = after.owners ∧
      final.image.2.crashSealed = [after.wal.sealed] ∧
      after.history = before.history ∧ after.checkpoint = before.checkpoint := by
  have ready := (prior.preservesRetained initialReady).1
  obtain ⟨_, after, session, final, installed, ran, phase, files, owners, _, seals, _, _, history, _, checkpoint, _, _, _, _⟩ :=
    report.installsCachedWithNamespace observed ready sizes cached
  exact ⟨after, session, final, .collectionReopen rfl prior report observed installed,
    ran, phase, files, owners, seals, history, checkpoint⟩

/-- Use the actual cached session after a successful close in the mixed trace. -/
theorem SegmentedDatabaseTrace.closeCached {directory initialDescriptor initial allowCollection log writer descriptor before}
    (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (initialReady : initial.RetainedReady directory initialDescriptor)
    (report : SegmentedCleanReopenReport directory before writer descriptor) (observed : report.Valid)
    (sizes : SizedCheckpointRunReports directory report.raw.reports before.wal.directory.active.manifest
      before.published.durable)
    (cached : CachedWalFileReports directory report.raw.reports before.wal before.target.range.watermark ByteArray.empty) :
    ∃ after session final,
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after ∧
      runOpenWithInstallation directory descriptor report.nextRef (.ok true) report.unlock
        (report.raw.reopenCached sizes cached report.removeFile report.write report.sync report.renameFile)
        (SegmentedCleanReopenReport.released directory before) = .ok session final ∧
      session.phase = .ready after.installed ∧ final.image = after.files ∧ final.owners = after.owners := by
  have ready := (prior.preservesRetained initialReady).1
  obtain ⟨after, session, final, installed, ran, phase, files, owners⟩ :=
    report.installsRetainedCached observed ready sizes cached
  exact ⟨after, session, final, .close prior report observed installed, ran, phase, files, owners⟩

/-- Use the actual cached session after losing power between writes. -/
theorem SegmentedDatabaseTrace.powerLossCached {directory initialDescriptor initial allowCollection log writer descriptor before}
    (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (initialReady : initial.RetainedReady directory initialDescriptor)
    (report : SegmentedReadyPowerLossReport directory before writer descriptor) (observed : report.Valid)
    (sizes : SizedCheckpointRunReports directory report.raw.reports report.retry.image.directory.active.manifest
      before.published.durable)
    (cached : CachedWalFileReports directory report.raw.reports before.wal before.target.range.watermark ByteArray.empty) :
    ∃ after session final,
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after ∧
      runOpenWithInstallation directory descriptor report.nextRef (.ok true) report.unlock
        (report.raw.reopenCached sizes cached report.removeFile report.write report.sync report.renameFile)
        report.retry = .ok session final ∧
      session.phase = .ready after.installed ∧ final.image = after.files ∧ final.owners = after.owners := by
  have ready := (prior.preservesRetained initialReady).1
  obtain ⟨after, session, final, installed, ran, phase, files, owners⟩ :=
    report.installsRetainedCached observed ready sizes cached
  exact ⟨after, session, final, .powerLoss prior report observed installed, ran, phase, files, owners⟩

/-- Extend the mixed history across power loss in the append callback with
the session and physical image returned by the cached recovery action. -/
theorem SegmentedDatabaseTrace.appendPowerLossCached {directory initialDescriptor initial allowCollection log writer descriptor before}
    (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (initialReady : initial.RetainedReady directory initialDescriptor)
    (report : SegmentedAppendPowerLossReport directory before writer descriptor) (observed : report.Valid)
    (sizes : SizedCheckpointRunReports directory report.read.reports report.retry.image.directory.active.manifest
      before.published.durable)
    (cached : CachedWalFileReports directory report.read.reports before.wal before.target.range.watermark report.currentTail) :
    ∃ after session final,
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [⟨[], some report.event⟩]) descriptor after ∧
      runOpenWithInstallation directory descriptor report.nextRef (.ok true) report.unlock
        (report.read.reopenCached sizes cached report.removeFile report.write report.sync report.renameFile)
        report.retry = .ok session final ∧
      session.phase = .ready after.installed ∧ final.image = after.files ∧ final.owners = after.owners := by
  have ready := (prior.preservesRetained initialReady).1
  obtain ⟨after, installed, session, final, ran, phase, image, owners⟩ :=
    report.installsRetainedCached observed ready sizes cached
  exact ⟨after, session, final, .appendPowerLoss prior report observed installed, ran, phase, image, owners⟩

/-- Extend the mixed trace after the failed append, last reference drop,
and delayed directory barrier. The next writer is the exact result of
cached recovery from the reached retry image and owner map. -/
theorem SegmentedDatabaseTrace.delayedDirectoryAppendCached
    {directory initialDescriptor initial allowCollection log writer descriptor before}
    (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (initialReady : initial.RetainedReady directory initialDescriptor)
    (barrier : DelayedDirectorySync directory) (failure : SegmentedAppendFailure directory before)
    (references : HeldLockReferences writer) (last : references.remaining barrier.drops = [])
    (separate : barrier.captured.description ≠ writer) {retry : LockedFileState FileImage}
    (attempts : BoundedReopenTrace directory (AppendRetryTarget before.history failure.event before.wal.active.first)
      (barrier.after failure.released) retry)
    (reopen : BoundedReopenAttempt) (descriptorEq : reopen.descriptor = descriptor)
    (acquired : reopen.acquired = .ok true) (acquisition : TryLockObserves retry.owners directory (.ok true))
    (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < reopen.nextRef)
    (recover : EStateM IO.Error FileImage Reopened)
    (reads : DelayedDirectorySync.CachedAppendReads (descriptor := descriptor) failure retry reopen recover)
    (settles : reopen.sync #[directory.path] retry.image = .ok () retry.image.syncDirectory)
    (healthy : ∀ history, ∀ selected : CanonicalKeeperLayout retry.image history,
      (history = before.history ∨ history = before.history ++ [failure.event]) →
      selected.target.first = before.wal.active.first →
      ∀ action prior next,
        ReachesAction selected.target retry.image.syncDirectory selected.plan.finishActions action prior →
        prior.effect selected.target action = some next →
        performPaths directory selected.plan reopen.removeFile throw reopen.write reopen.sync reopen.renameFile action prior =
          .ok () next) :
    ∃ after,
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [⟨[], some failure.event⟩]) descriptor after ∧
      AppendRetryEndpoint directory before failure.event retry descriptor
        (runOpenWithInstallation directory reopen.descriptor reopen.nextRef reopen.acquired reopen.unlock recover retry) after ∧
      retry.image.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode after.history).size.toUInt64) ∧
      after.checkpoint = before.checkpoint ∧ after.installed.generation = before.installed.generation := by
  have ready := (prior.preservesRetained initialReady).1
  obtain ⟨handoff, after, endpoint, retained, marker, checkpoint, generation⟩ :=
    barrier.reopensRetainedAppendErrorCached ready failure references last separate attempts reopen descriptorEq
      acquired acquisition liveRefs fresh recover reads settles healthy
  exact ⟨after, .delayedDirectoryAppend prior failure barrier references last handoff attempts reads endpoint retained,
    endpoint, marker, checkpoint, generation⟩

/-- Carry the cached writer returned after the delayed old keeper's effect,
power loss and retries into the mixed history. Only the interrupted append
adds a write submission to the trace. -/
theorem SegmentedDatabaseTrace.delayedKeeperPowerLossCached
    {directory initialDescriptor initial allowCollection log writer descriptor nextRef before}
    (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (initialReady : initial.RetainedReady directory initialDescriptor)
    (failure : SegmentedAppendFailure directory before) (release : SegmentedFailureRelease writer)
    (released : release.Observed (directory := directory) failure.poisoned
      ⟨failure.failed, before.owners.set (directory.file .lock) none⟩)
    (cut : DelayedKeeperReplacementPowerLoss directory failure.released
      (AppendRetryTarget before.history failure.event before.wal.active.first))
    {retry : LockedFileState FileImage}
    (attempts : BoundedReopenTrace directory (AppendRetryTarget before.history failure.event before.wal.active.first)
      cut.crashed retry)
    (acquisition : TryLockObserves retry.owners directory (.ok true))
    (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < nextRef) (unlock : UnlockReport)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit) :
    BoundedReopenTrace directory (AppendRetryTarget before.history failure.event before.wal.active.first)
      cut.during retry ∧
    ∃ history, (history = before.history ∨ history = before.history ++ [failure.event]) ∧
      ∃ selected : CanonicalKeeperLayout retry.image history,
        let wal := before.wal.appendSelectedView retry.image.directory.active history
        ∀ raw : HealthyBoundedWalReports directory (retry.owners.set (directory.file .lock) (some descriptor))
            descriptor wal retry.image.directory.active selected.range.watermark before.published.durable selected.tail,
          ∀ sizes : SizedCheckpointRunReports directory raw.reports retry.image.directory.active.manifest before.published.durable,
            ∀ cached : CachedWalFileReports directory raw.reports wal selected.range.watermark selected.tail,
              sync #[directory.path] retry.image = .ok () retry.image.syncDirectory →
              (∀ action prior next,
                ReachesAction selected.target retry.image.syncDirectory selected.plan.finishActions action prior →
                prior.effect selected.target action = some next →
                performPaths directory selected.plan removeFile throw write sync renameFile action prior = .ok () next) →
              ∃ after,
                SegmentedDatabaseTrace directory initialDescriptor initial allowCollection
                  (log ++ [⟨[], some failure.event⟩]) descriptor after ∧
                AppendRetryEndpoint directory before failure.event retry descriptor
                  (runOpenWithInstallation directory descriptor nextRef (.ok true) unlock
                    (raw.reopenCached sizes cached removeFile write sync renameFile) retry) after ∧
                after.target.pair = cut.pair ∧ after.checkpoint = before.checkpoint ∧
                after.installed.generation = before.installed.generation := by
  have ready := (prior.preservesRetained initialReady).1
  obtain ⟨timeline, pair, history, permitted, selected, install⟩ :=
    cut.reopensRetainedCachedAfter (nextDescriptor := descriptor) ready failure attempts acquisition
      liveRefs fresh unlock removeFile write sync renameFile
  refine ⟨timeline, history, permitted, selected, ?_⟩
  intro _ raw sizes cached settles healthy
  obtain ⟨after, endpoint, selectedHistory, retained, checkpoint, generation⟩ := install raw sizes cached settles healthy
  exact ⟨after, .delayedKeeperPowerLoss prior failure release released cut attempts pair
    (selected := selected) (raw := raw) (sizes := sizes) (cached := cached) endpoint selectedHistory retained,
    endpoint, endpoint.pair.trans pair, checkpoint, generation⟩

/-- Start the mixed history from the actual shared bootstrap attempt and
its returned session, using only the reached native callback reports. -/
theorem SegmentedDatabaseTrace.fromBootstrapRun (directory : DiskDirectory) (descriptor nextRef : Nat)
    (before : LockedFileState WalSegmentRotation.State) (valid : BootstrapValid before.image)
    (acquired : Except IO.Error Bool) (acquisition : TryLockObserves before.owners directory acquired)
    (unlock : UnlockReport) (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (readEmpty : FilePath → Except IO.Error (Option ByteArray))
    (metadata : FilePath → Except IO.Error (Option IO.FS.Metadata))
    (seen : ∀ empty, readEmpty (directory.file (.walSegment 0)) = .ok empty → before.image.observeSuccessor = empty)
    (createEmpty : FilePath → EStateM IO.Error WalSegmentRotation.State Unit)
    (write : FilePath → ByteArray → EStateM IO.Error WalSegmentRotation.State Unit)
    (sync : Array FilePath → EStateM IO.Error WalSegmentRotation.State Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error WalSegmentRotation.State Unit)
    (rotation : WalSegmentRotation.EffectReports
      (WalSegmentRotation.performPaths directory 0 createEmpty (fun path => sync #[path])))
    (marker : BootstrapMarkerReports (Publication.performReplacement (write · (WAL.Boundary.encode 0))
      sync renameFile (directory.file .stagedWalBoundary) directory.path (fun _ => directory.file .walBoundary) #[]))
    {session : SegmentedSession} {after : LockedFileState WalSegmentRotation.State} :
    let recover := bootstrapSegmentedWith directory
      (fun path => liftExcept (list path)) (fun path => liftExcept (readEmpty path))
      (fun path => liftExcept (metadata path)) createEmpty write sync renameFile
    runOpenWithInstallation directory descriptor nextRef acquired unlock recover before = .ok session after →
    ∃ bootstrap : BootstrapReady after.image,
      session = ⟨directory, descriptor, .ready (bootstrap.writerState after.owners).installed, nextRef, nextRef + 1⟩ ∧
      ∀ {allowCollection log next last},
        SegmentedDatabaseTrace directory descriptor (bootstrap.writerState after.owners) allowCollection log next last →
        last.RetainedReady directory next ∧ MarkedSessionRetention log last.history ∧
          log.flatMap MarkedSessionWrites.acknowledged <+ last.history ∧
          last.history <+ log.flatMap MarkedSessionWrites.submitted := by
  intro recover opened
  obtain ⟨returned, _, owners, _, bootstrap⟩ := runOpenWithInstallation_bootstrapReady directory descriptor nextRef
    before valid acquired acquisition unlock list readEmpty metadata seen createEmpty write sync renameFile rotation
    marker opened
  refine ⟨bootstrap, returned, fun trace => trace.fromBootstrap bootstrap ?_⟩
  simp [owners, LockOwners.Owns, LockOwners.set]

/-- The cached opener extends a mixed trace using the marker that
survived publication, with the interrupted write logged as submitted. -/
theorem SegmentedDatabaseTrace.markerPowerLossCached {directory initialDescriptor initial allowCollection log writer descriptor before}
    (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (initialReady : initial.RetainedReady directory initialDescriptor)
    (report : SegmentedMarkerPowerLossReport directory before writer descriptor) (observed : report.Valid)
    (recover : EStateM IO.Error FileImage Reopened) (reads : report.CachedReads recover)
    (sameAttempt : report.reopen.recover directory = recover) :
    ∃ after, SegmentedDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [⟨[], some report.event⟩]) descriptor after ∧
      AppendRetryEndpoint directory before report.event report.retry descriptor
        (runOpenWithInstallation directory report.reopen.descriptor report.reopen.nextRef report.reopen.acquired
          report.reopen.unlock recover report.retry) after ∧
      report.pair.walBoundary = some (WAL.Boundary.encode (WAL.encode after.history).size.toUInt64) ∧
      after.checkpoint = before.checkpoint := by
  have ready := (prior.preservesRetained initialReady).1
  obtain ⟨after, endpoint, _, marker, checkpoint, generation⟩ := report.installsRetainedCached observed ready recover reads
  have installed : report.Installs after := by
    refine ⟨?_, observed.powerLoss, marker, checkpoint, generation⟩
    simpa only [BoundedReopenAttempt.run, sameAttempt] using endpoint
  exact ⟨after, .markerPowerLoss prior report observed installed, endpoint, marker, checkpoint⟩

/-- Include the exact cached installation after a reported checkpoint
error in the mixed trace. The selected runs still come from the manifest
at the reached retry, and a checkpoint error adds no WAL submission. -/
theorem SegmentedDatabaseTrace.checkpointErrorCached
    {directory initialDescriptor initial allowCollection log writer descriptor before}
    (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (initialReady : initial.RetainedReady directory initialDescriptor)
    (failure : SegmentedCheckpointFailure directory before writer descriptor)
    (recover : EStateM IO.Error FileImage Reopened) (reads : failure.CachedReads recover) :
    ∃ after session final,
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after ∧
      SelectedIntegrityCheckpoint failure.published.durable failure.retry.image.directory.active.manifest after.checkpoint ∧
      recoverSelected (after.checkpoint.getD (.empty, 0)).1 (WAL.encode before.history) = .ok after.installed.table ∧
      runOpenWithInstallation directory failure.reopen.descriptor failure.reopen.nextRef failure.reopen.acquired
        failure.reopen.unlock recover failure.retry = .ok session final ∧
      session.phase = .ready after.installed ∧ after.files = final.image ∧ after.owners = final.owners := by
  have ready := (prior.preservesRetained initialReady).1
  obtain ⟨after, session, final, installed, _, selected, replay, ran, phase, files, owners⟩ :=
    failure.installsRetainedCached ready recover reads
  exact ⟨after, session, final, .checkpointError prior failure installed, selected, replay, ran, phase, files, owners⟩

/-- Extend the trace with the installed table from the exact durable runs
of the surviving checkpoint and replay of the unchanged WAL history. -/
theorem SegmentedDatabaseTrace.checkpointPowerLossCached
    {directory initialDescriptor initial allowCollection log writer descriptor before}
    (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (initialReady : initial.RetainedReady directory initialDescriptor)
    (report : SegmentedCheckpointPowerLossReport directory before writer descriptor) (observed : report.Valid)
    (recover : EStateM IO.Error FileImage Reopened) (reads : report.CachedReads recover) :
    ∃ after session final,
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after ∧
      SelectedIntegrityCheckpoint report.published.durable report.survivingPair.manifest after.checkpoint ∧
      recoverSelected (after.checkpoint.getD (.empty, 0)).1 (WAL.encode before.history) = .ok after.installed.table ∧
      runOpenWithInstallation directory report.reopen.descriptor report.reopen.nextRef report.reopen.acquired
        report.reopen.unlock recover report.retry = .ok session final ∧
      session.phase = .ready after.installed ∧ after.files = final.image ∧ after.owners = final.owners := by
  have ready := (prior.preservesRetained initialReady).1
  obtain ⟨after, session, final, installed, _, selected, replay, ran, phase, files, owners⟩ :=
    report.installsRetainedCached observed ready recover reads
  exact ⟨after, session, final, .checkpointPowerLoss prior report observed installed,
    selected, replay, ran, phase, files, owners⟩

/-- Use the released writer's reached rotation files to extend the mixed
history with the session installed by the cached opener. -/
theorem SegmentedDatabaseTrace.rotationErrorCached
    {directory initialDescriptor initial allowCollection log writer descriptor before}
    (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (initialReady : initial.RetainedReady directory initialDescriptor)
    (report : SegmentedRotationRecoveryReport directory before descriptor) (release : SegmentedFailureRelease writer)
    (sizes : SizedCheckpointRunReports directory report.read.reports
      (report.retry.image.settledReopenImage before.wal).directory.active.manifest before.published.durable)
    (cached : CachedWalFileReports directory report.read.reports
      (report.retry.image.settleForReopen.visible before.wal) before.target.range.watermark ByteArray.empty) :
    release.Observed (directory := directory) report.failure.poisoned report.failure.released ∧
    ∃ after,
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after ∧
      SegmentedRotationReopenEndpoint directory descriptor before after
        (runOpenWithInstallation directory descriptor report.nextRef (.ok true) report.unlock
          (report.read.reopenCachedWithState sizes cached report.removeFile report.write report.sync report.renameFile)
          report.retry) ∧
      after.wal.segments = (report.retry.image.visible before.wal).segments ∧
      after.wal.active = (report.retry.image.visible before.wal).active := by
  have ready := (prior.preservesRetained initialReady).1
  obtain ⟨_, released, after, installed, endpoint, _, segments, active⟩ :=
    report.installsRetainedCached ready release sizes cached
  exact ⟨released, after, .rotationError prior report release released installed, endpoint, segments, active⟩

/-- Extend the history using the exact segment layout installed by the
cached opener across a crash during WAL rotation. -/
theorem SegmentedDatabaseTrace.rotationPowerLossCached
    {directory initialDescriptor initial allowCollection log writer descriptor before}
    (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (initialReady : initial.RetainedReady directory initialDescriptor)
    (report : SegmentedRotationPowerLossReport directory before descriptor)
    (sizes : SizedCheckpointRunReports directory report.read.reports
      (report.retry.image.settledReopenImage before.wal).directory.active.manifest before.published.durable)
    (cached : CachedWalFileReports directory report.read.reports
      (report.retry.image.settleForReopen.visible before.wal) before.target.range.watermark ByteArray.empty) :
    ∃ after,
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after ∧
      SegmentedRotationReopenEndpoint directory descriptor before after
        (runOpenWithInstallation directory descriptor report.nextRef (.ok true) report.unlock
          (report.read.reopenCachedWithState sizes cached report.removeFile report.write report.sync report.renameFile)
          report.retry) ∧
      after.wal.segments = (report.retry.image.visible before.wal).segments ∧
      after.wal.active = (report.retry.image.visible before.wal).active := by
  have ready := (prior.preservesRetained initialReady).1
  obtain ⟨after, installed, endpoint, _, segments, active⟩ := report.installsRetainedCached ready sizes cached
  exact ⟨after, .rotationPowerLoss prior report installed, endpoint, segments, active⟩

/-- Reads with a pin belonging to the current writer match replay of the
retained history from the empty abstract table. -/
theorem SegmentedDatabaseTrace.pinnedReads {directory initialDescriptor initial allowCollection log descriptor last}
    (trace : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor last)
    (initialReady : initial.RetainedReady directory initialDescriptor) :
    ∃ reference : SnapshotTable UInt64, SnapshotWalReplay .empty last.history reference ∧
      ∀ pin ∈ last.installed.table.pins.active,
        (∀ key, last.installed.table.lookup pin.handle key = some (reference.table.lookup key pin.sequence)) ∧
        ∀ start stop, last.installed.table.range pin.handle start stop =
          some (reference.table.range start stop pin.sequence) :=
  (trace.preservesRetained initialReady).1.pinnedReads

/-- Interpret the adapter's reported session comparison on the installed
writer. A foreign token yields no result even if its handle number is in use. -/
theorem SegmentedDatabaseTrace.guardedPinnedReads {directory initialDescriptor initial allowCollection log descriptor last}
    (trace : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor last)
    (initialReady : initial.RetainedReady directory initialDescriptor) {sameSession : Bool} {issuer current : Nat}
    (compared : sameSession = decide (issuer = current)) :
    ∃ reference : SnapshotTable UInt64, SnapshotWalReplay .empty last.history reference ∧
      ∀ pin ∈ last.installed.table.pins.active,
        (∀ key, readWithHandle (.ready last.installed.table) sameSession (·.lookup pin.handle key) =
          .ok (if issuer = current then some (reference.table.lookup key pin.sequence) else none)) ∧
        ∀ start stop, readWithHandle (.ready last.installed.table) sameSession (·.range pin.handle start stop) =
          .ok (if issuer = current then some (reference.table.range start stop pin.sequence) else none) := by
  obtain ⟨reference, replayed, pinned⟩ := trace.pinnedReads initialReady
  refine ⟨reference, replayed, ?_⟩
  intro pin active
  by_cases localHandle : issuer = current
  · simp only [compared.trans (decide_eq_true localHandle), ite_eq_left localHandle]
    obtain ⟨lookup, range⟩ := pinned pin active
    exact ⟨fun key => congrArg Except.ok (lookup key), fun start stop => congrArg Except.ok (range start stop)⟩
  · simp only [ite_eq_right localHandle]
    exact ⟨fun key => readWithHandle_foreign _ (·.lookup pin.handle key) compared localHandle,
      fun start stop => readWithHandle_foreign _ (·.range pin.handle start stop) compared localHandle⟩

/-- After any covered reopen, every supported sequence can be acquired
against the returned table and reads the same snapshot as abstract replay. -/
theorem SegmentedDatabaseTrace.acquireReads {directory initialDescriptor initial allowCollection log descriptor last}
    (trace : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor last)
    (initialReady : initial.RetainedReady directory initialDescriptor) {snapshot : UInt64}
    (retained : last.installed.table.pins.floor ≤ snapshot) (committed : snapshot ≤ last.installed.table.committed) :
    ∃ reference : SnapshotTable UInt64, SnapshotWalReplay .empty last.history reference ∧
      ∃ pin pinned, last.installed.table.acquireAt snapshot = some (pin, pinned) ∧
        (∀ key, pinned.lookup pin.handle key = some (reference.table.lookup key snapshot)) ∧
        ∀ start stop, pinned.range pin.handle start stop = some (reference.table.range start stop snapshot) :=
  (trace.preservesRetained initialReady).1.acquireReads retained committed

/-- One abstract history explains both durability and every supported
snapshot of the last installed writer in an admitted trace from bootstrap. -/
theorem SegmentedDatabaseTrace.keyValueRefinement
    {directory initialDescriptor allowCollection log descriptor last}
    {first : LockedFileState WalSegmentRotation.State} (bootstrap : BootstrapReady first.image)
    (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedDatabaseTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log descriptor last) :
    ∃ reference : SnapshotTable UInt64,
      SnapshotWalReplay .empty last.history reference ∧
      MarkedSessionRetention log last.history ∧
      log.flatMap MarkedSessionWrites.acknowledged <+ last.history ∧
      last.history <+ log.flatMap MarkedSessionWrites.submitted ∧
      ∀ snapshot, last.installed.table.pins.floor ≤ snapshot → snapshot ≤ last.installed.table.committed →
        ∃ pin pinned, last.installed.table.acquireAt snapshot = some (pin, pinned) ∧
          (∀ key, pinned.lookup pin.handle key = some (reference.table.lookup key snapshot)) ∧
          ∀ start stop, pinned.range pin.handle start stop = some (reference.table.range start stop snapshot) := by
  obtain ⟨ready, retained, acknowledgements, submissions⟩ := trace.fromBootstrap bootstrap held
  obtain ⟨reference, replayed⟩ := SnapshotWalReplay.fromEmpty last.history ready.resumed.ordered
  refine ⟨reference, replayed, retained, acknowledgements, submissions, ?_⟩
  intro snapshot floor committed
  obtain ⟨other, sameReplay, pin, pinned, acquired, lookup, range⟩ := ready.acquireReads floor committed
  have same := replayed.deterministic sameReplay
  cases same
  exact ⟨pin, pinned, acquired, lookup, range⟩

/-- An earlier pin's sequence reads the same values after reacquiring it
in the final session, provided the final writer still retains it. -/
theorem SegmentedDatabaseTrace.reacquireReadsStable {directory initialDescriptor initial allowCollection log descriptor last}
    (trace : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor last)
    (initialReady : initial.RetainedReady directory initialDescriptor) {oldPin : SnapshotPin}
    (active : oldPin ∈ initial.installed.table.pins.active)
    (retained : last.installed.table.pins.floor ≤ oldPin.sequence) :
    ∃ newPin pinned, last.installed.table.acquireAt oldPin.sequence = some (newPin, pinned) ∧
      newPin.sequence = oldPin.sequence ∧
      (∀ key, pinned.lookup newPin.handle key = initial.installed.table.lookup oldPin.handle key) ∧
      ∀ start stop, pinned.range newPin.handle start stop = initial.installed.table.range oldPin.handle start stop := by
  obtain ⟨ready, _, history, _⟩ := trace.preservesRetained initialReady
  exact initialReady.reacquireReadsStable ready history active retained

end Alvoki.Storage.DiskSession
