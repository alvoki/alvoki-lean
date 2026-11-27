import Alvoki.Storage.Disk.Proofs.Checkpoint.CheckpointManifestStageFailureReopen
import Alvoki.Storage.Disk.Proofs.Checkpoint.CheckpointManifestDirectoryFailureReopen
import Alvoki.Storage.Disk.Proofs.Checkpoint.CheckpointManifestRenameFailure
import Alvoki.Storage.Disk.Proofs.Checkpoint.CheckpointRunErrorReopen
import Alvoki.Storage.Disk.SegmentedDatabaseTrace
import Alvoki.Storage.Disk.Proofs.Collection.SegmentedRunCollectionPowerLoss
import Alvoki.Storage.Disk.DiskCleanReopenAdmission
import Alvoki.Storage.Disk.SegmentedCheckpointObservedReopen
import Alvoki.Storage.Disk.SessionReadGuards
import Alvoki.Storage.Disk.SegmentedWriterMaintenance
import Alvoki.Storage.Disk.SegmentedBatchAppend
import Alvoki.Storage.Disk.SegmentedBatchAppendProcessExit
import Alvoki.Storage.Disk.BatchAppendReopenAdmission
import Alvoki.Storage.Disk.SegmentedBatchCachedPowerLoss
import Alvoki.Storage.Disk.WalBatchSession
import Alvoki.Storage.Disk.Proofs.Rotation.RotationReopenAdmission

namespace Alvoki.Storage.DiskSession

open WalSegmentRepair WAL.Boundary Sequential
open scoped List

/-- Preserve the boundary of an uncertain batch in the trace index. A run
of ordinary database operations keeps its existing submission log. -/
inductive DatabaseSubmissions where
  | ordinary (log : List MarkedSessionWrites)
  | acknowledgedBatch (batch : List WAL.Write)
  | uncertainBatch (batch : List WAL.Write)

def DatabaseSubmissions.Retains : DatabaseSubmissions → List WAL.Write → Prop
  | .ordinary log, suffix => MarkedSessionRetention log suffix
  | .acknowledgedBatch batch, suffix => suffix = batch
  | .uncertainBatch batch, suffix => suffix = [] ∨ suffix = batch

/-- Every entry accounts for its own suffix before proceeding to the next
entry. An uncertain batch has one retention choice for all of its frames. -/
inductive DatabaseBatchRetention : List DatabaseSubmissions → List WAL.Write → Prop where
  | start : DatabaseBatchRetention [] []
  | append (prior : DatabaseBatchRetention log retained) (one : entry.Retains suffix) :
      DatabaseBatchRetention (log ++ [entry]) (retained ++ suffix)

def DatabaseSubmissions.acknowledged : DatabaseSubmissions → List WAL.Write
  | .ordinary log => log.flatMap MarkedSessionWrites.acknowledged
  | .acknowledgedBatch batch => batch
  | .uncertainBatch _ => []

def DatabaseSubmissions.submitted : DatabaseSubmissions → List WAL.Write
  | .ordinary log => log.flatMap MarkedSessionWrites.submitted
  | .acknowledgedBatch batch | .uncertainBatch batch => batch

theorem DatabaseBatchRetention.orderedSubmissions (retention : DatabaseBatchRetention log retained) :
    log.flatMap DatabaseSubmissions.acknowledged <+ retained ∧
      retained <+ log.flatMap DatabaseSubmissions.submitted := by
  induction retention with
  | start => exact ⟨.slnil, .slnil⟩
  | @append log retained entry suffix _ one ih =>
    have bounds : entry.acknowledged <+ suffix ∧ suffix <+ entry.submitted := by
      cases entry with
      | ordinary log => exact MarkedSessionRetention.orderedSubmissions one
      | acknowledgedBatch batch =>
        change suffix = batch at one
        subst suffix
        exact ⟨List.Sublist.refl _, List.Sublist.refl _⟩
      | uncertainBatch batch =>
        change suffix = [] ∨ suffix = batch at one
        rcases one with rfl | rfl <;> simp [DatabaseSubmissions.acknowledged, DatabaseSubmissions.submitted]
    exact ⟨by simpa using ih.1.append bounds.1, by simpa using ih.2.append bounds.2⟩

private theorem sameTarget {left right : Target} (pair : left.pair = right.pair)
    (first : left.first = right.first) (contents : left.trimmed = right.trimmed) : left = right := by
  have range := Option.some.inj (left.decoded.symm.trans (pair ▸ right.decoded))
  cases left
  cases right
  cases pair
  cases range
  cases first
  cases contents
  rfl

/-- A returned error during manifest publication and an admitted reopen
from its exact released image. Each branch fixes the returned slot,
session and final files through its own native reports. -/
inductive CheckpointManifestErrorReopened {directory : DiskDirectory} {before : SegmentedWriterState}
    (writer : Nat) : Nat → SegmentedSession → LockedFileState FileImage → SegmentedWriterState → Prop where
  | rename {input : System.FilePath} {cut : CheckpointPowerCut directory before} {report : ObservedManifestRenameFailure cut}
      {retry : LockedFileState FileImage} {layout : CanonicalKeeperLayout retry.image before.history}
      {release : SegmentedFailureRelease writer}
      {opened : CheckpointHeldOpen input directory layout report.publication} {session final}
      (endpoint : report.Reopened release opened session final after) :
      CheckpointManifestErrorReopened writer opened.calls.slot.description session final after
  | directorySync {input : System.FilePath}
      {cut : CheckpointPowerCut directory before} {report : ObservedManifestDirectoryFailure cut}
      {retry : LockedFileState FileImage} {layout : CanonicalKeeperLayout retry.image before.history}
      {release : SegmentedFailureRelease writer}
      {opened : CheckpointHeldOpen input directory layout report.publication} {session final}
      (endpoint : report.Reopened release opened session final after) :
      CheckpointManifestErrorReopened writer opened.calls.slot.description session final after

/-- The two returned-error paths preserve the acknowledged history and
retained segments in the concrete writer installed by the retry. -/
theorem CheckpointManifestErrorReopened.preservesWriter
    (opened : CheckpointManifestErrorReopened (directory := directory) (before := before) writer descriptor session final after) :
    after.RetainedReady directory descriptor ∧ after.history = before.history ∧
      after.wal = { before.wal with directory := after.files.directory } := by
  cases opened with
  | rename endpoint => exact ⟨endpoint.ready, endpoint.history, endpoint.wal⟩
  | directorySync endpoint => exact ⟨endpoint.ready, endpoint.history, endpoint.wal⟩

inductive SegmentedBatchDatabaseTrace (directory : DiskDirectory) (initialDescriptor : Nat)
    (initial : SegmentedWriterState) (allowCollection : Bool) :
    List DatabaseSubmissions → Nat → SegmentedWriterState → Prop where
  | start : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection [] initialDescriptor initial
  | ordinary (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (step : SegmentedDatabaseTrace directory writer before allowCollection submissions descriptor after) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.ordinary submissions]) descriptor after
  | table (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (step : SegmentedTableStep before.installed.table table) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer (before.withTable table)
  | checkpoint
      (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      {attempt : SegmentedCheckpointReport directory before} (observed : attempt.Valid)
      (installed : attempt.Installs after) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer after
  | cleanReopenObserved {files : Type} {input : System.FilePath}
      (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (closed : CleanUnlockReports directory writer)
      {retry : LockedFileState FileImage} {layout : CanonicalKeeperLayout retry.image before.history}
      {observed : MarkedRetryChunkReports files directory layout before.published}
      {admission : OpenAdmissionReports input directory observed.slot}
      (endpoint : AdmittedCleanReopen closed observed admission after) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log observed.slot.description after
  | readyProcessExit {files : Type} {input : System.FilePath} {inventory : DescriptorInventory}
      {cached : DescriptorSlot} {retry : LockedFileState FileImage}
      {layout : CanonicalKeeperLayout retry.image before.history}
      {observed : MarkedRetryChunkReports files directory layout before.published}
      {admission : OpenAdmissionReports input directory observed.slot}
      (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (exit : ReadyProcessExit inventory writer cached)
      (attempts : BoundedReopenTrace directory (· = before.target)
        (exit.reached directory ⟨before.files, before.owners⟩) retry)
      (sameLock : observed.descriptors.inode observed.slot.description = inventory.inode exit.lock.description)
      (distinct : observed.slot.description ≠ writer)
      (installed : ReadyReopenInstallation observed admission after) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log observed.slot.description after
  | checkpointManifestStageError {input : System.FilePath}
      {attempt : SegmentedCheckpointReport directory before}
      {report : ObservedManifestStageFailure attempt} {manifest runs}
      {retry : LockedFileState FileImage} {layout : CanonicalKeeperLayout retry.image before.history}
      {release : SegmentedFailureRelease writer}
      {opened : CheckpointHeldOpen input directory layout (report.reachedPublication manifest runs)} {session final}
      (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (endpoint : ManifestStageFailureReopened (report := report) release opened session final after) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log opened.calls.slot.description after
  | checkpointManifestError {session final}
      (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (endpoint : CheckpointManifestErrorReopened (directory := directory) (before := before) writer descriptor session final after) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after
  | checkpointRunError {session final}
      (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (endpoint : PriorCheckpointErrorReopened (directory := directory) (before := before) writer descriptor session final after) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after
  | checkpointPowerLossObserved {files : Type}
      (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (cut : CheckpointPowerCut directory before) {published : CheckpointPublication.Image}
      (projected : before.published.executeVersioned cut.checkpoint.plan cut.checkpoint.cut = some published)
      {pair : DirectoryPublication.Bindings}
      (survives : pair ∈ (published.segmentedCheckpointView before.wal).directory.crashImages)
      {retry : LockedFileState FileImage}
      (failures : BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
        ⟨(CheckpointPowerCut.physical before published).crash pair (some before.wal.active.bytes) [],
          before.owners.set (directory.file .lock) none⟩ retry)
      (selected : retry.image.directory.active = pair)
      {layout : CanonicalKeeperLayout retry.image before.history}
      {observed : MarkedRetryChunkReports files directory layout published}
      (installed : CheckpointChunkWriter directory before published observed after) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log observed.slot.description after
  | acknowledgedBatch
      (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedBatchAppendReport directory before) (selected : report.Selects target) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.acknowledgedBatch report.batch]) writer (report.next target)
  | batchError
      (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedBatchRecoveryReport directory before writer descriptor)
      (installed : report.Installs after) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch report.failure.batch]) descriptor after
  | batchErrorAdmitted {files handle : Type} {input : System.FilePath} {retry : LockedFileState FileImage}
      (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (failure : SegmentedBatchFailure directory before) (observed : ObservedBatchFailure failure handle)
      {release : SegmentedFailureRelease writer}
      (installed : observed.AdmittedReopen (files := files) release input retry descriptor after) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch failure.batch]) descriptor after
  | batchPowerLoss
      (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (cut : SegmentedBatchMarkerPowerLossReport directory before writer) (observed : cut.Valid)
      (report : cut.CachedReopenReports descriptor) (installed : report.Installs after) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch cut.batch]) descriptor after
  | batchMarkerProcessExit
      (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (cut : SegmentedBatchMarkerPowerLossReport directory before writer) (observed : cut.Reached)
      (report : cut.ProcessExitCachedReopenReports descriptor) (installed : report.reopen.InstallsFromCut after) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch cut.batch]) descriptor after
  | batchMarkerAdmitted {files : Type} {input : System.FilePath} {retry : LockedFileState FileImage}
      (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (cut : SegmentedBatchMarkerPowerLossReport directory before writer) (observed : cut.Reached)
      (installed : cut.AdmittedRetry (files := files) input retry descriptor after) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch cut.batch]) descriptor after
  | batchAppendPowerLoss
      (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedBatchAppendPowerLossReport directory before descriptor) (observed : report.Valid)
      (installed : report.Installs after) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch report.reopen.batch]) descriptor after
  | batchAppendProcessExit
      (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedBatchAppendProcessExitReport directory before writer descriptor) (observed : report.reopen.Valid)
      (installed : report.reopen.Installs after) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch report.reopen.batch]) descriptor after
  | batchAppendAdmitted {files : Type} {input : System.FilePath} {retry : LockedFileState FileImage}
      (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : BatchAppendInterruption directory before) {stop : report.Stop writer}
      (installed : report.AdmittedReopen (files := files) stop input retry descriptor after) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch report.batch]) descriptor after
  | collectRuns {runs : CheckpointPublication.RunUnlinkImage}
      (enabled : allowCollection = true)
      (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (reports : SegmentedRunCollectionReports directory before runs) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer
        (before.afterRunCollection reports.reached.guaranteed)
  | collectRunsPowerLoss {files : Type} {input : System.FilePath} {retry : LockedFileState FileImage}
      {runs : CheckpointPublication.RunUnlinkImage}
      (enabled : allowCollection = true)
      (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      {reports : SegmentedRunCollectionReports directory before runs} (loss : SegmentedRunCollectionPowerLoss reports)
      (installed : loss.Installs (files := files) input retry descriptor after) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after
  | rotationPowerLossAdmitted {files : Type} {input : System.FilePath} {retry : LockedFileState FileImage}
      {pair : DirectoryPublication.Bindings} {present : Bool}
      (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (cut : RotationInFlightCut directory before)
      (installed : cut.AdmittedReopen (files := files) pair present input retry descriptor after) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after

private theorem appendUncertainBatch {initial before after batch retained : List WAL.Write}
    {log : List DatabaseSubmissions} (retention : DatabaseBatchRetention log retained)
    (history : before = initial ++ retained) (selected : after = before ∨ after = before ++ batch) :
    ∃ suffix, after = initial ++ suffix ∧ DatabaseBatchRetention (log ++ [.uncertainBatch batch]) suffix := by
  rcases selected with lost | kept
  · exact ⟨retained ++ [], by simpa using lost.trans history, .append retention (.inl rfl)⟩
  · exact ⟨retained ++ batch, by rw [kept, history, List.append_assoc], .append retention (.inr rfl)⟩

theorem SegmentedBatchDatabaseTrace.preservesRetained
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log descriptor last)
    (ready : initial.RetainedReady directory initialDescriptor) :
    last.RetainedReady directory descriptor ∧
      ∃ retained, last.history = initial.history ++ retained ∧ DatabaseBatchRetention log retained := by
  induction trace with
  | start => exact ⟨ready, [], by simp, .start⟩
  | ordinary _ step ih =>
    obtain ⟨beforeReady, retained, beforeHistory, retention⟩ := ih
    obtain ⟨afterReady, suffix, extended, kept⟩ := step.preservesRetained beforeReady
    exact ⟨afterReady, retained ++ suffix, by rw [extended, beforeHistory, List.append_assoc],
      .append retention kept⟩
  | table _ step ih =>
    exact ⟨step.preservesRetained ih.1, ih.2⟩
  | checkpoint _ observed installed ih =>
    obtain ⟨beforeReady, retained, history, retention⟩ := ih
    exact ⟨(installed.preservesRetained observed beforeReady).1, retained, installed.history.trans history, retention⟩
  | cleanReopenObserved _ _ endpoint ih =>
    obtain ⟨_, retained, history, retention⟩ := ih
    exact ⟨endpoint.writer.retained, retained, endpoint.writer.history.trans history, retention⟩
  | readyProcessExit _ _ _ _ _ installed ih =>
    obtain ⟨_, retained, history, retention⟩ := ih
    exact ⟨installed.writer.retained, retained, installed.writer.history.trans history, retention⟩
  | checkpointManifestStageError _ endpoint ih =>
    obtain ⟨_, retained, history, retention⟩ := ih
    exact ⟨endpoint.retained, retained, endpoint.history.trans history, retention⟩
  | checkpointManifestError _ endpoint ih =>
    obtain ⟨_, retained, history, retention⟩ := ih
    obtain ⟨ready, unchanged, _⟩ := endpoint.preservesWriter
    exact ⟨ready, retained, unchanged.trans history, retention⟩
  | checkpointRunError _ endpoint ih =>
    obtain ⟨_, retained, history, retention⟩ := ih
    obtain ⟨ready, unchanged, _⟩ := endpoint.preservesWriter
    exact ⟨ready, retained, unchanged.trans history, retention⟩
  | checkpointPowerLossObserved _ _ _ _ _ _ installed ih =>
    obtain ⟨_, retained, history, retention⟩ := ih
    exact ⟨installed.retained, retained, installed.history.trans history, retention⟩
  | acknowledgedBatch _ report selected ih =>
    obtain ⟨beforeReady, retained, beforeHistory, retention⟩ := ih
    obtain ⟨chosen, selectedChosen, afterReady⟩ := report.preservesRetained beforeReady
    have first := selected.2.1.trans selectedChosen.2.1.symm
    have contents := selected.2.2.trans ((congrArg (fun first => WAL.encode (List.drop first _)) first).trans
      selectedChosen.2.2.symm)
    have same := sameTarget (selected.1.trans selectedChosen.1.symm) first contents
    cases same
    refine ⟨afterReady, _, ?_, .append retention rfl⟩
    change _ ++ _ = _
    rw [beforeHistory, List.append_assoc]
  | batchError _ _ installed ih
  | batchPowerLoss _ _ _ _ installed ih
  | batchMarkerProcessExit _ _ _ _ installed ih
  | batchMarkerAdmitted _ _ _ installed ih =>
    obtain ⟨_, _, history, retention⟩ := ih
    exact ⟨installed.retained, appendUncertainBatch retention history installed.history⟩
  | batchErrorAdmitted _ _ _ installed ih =>
    obtain ⟨_, _, history, retention⟩ := ih
    exact ⟨installed.installation.retained, appendUncertainBatch retention history installed.installation.history⟩
  | batchAppendPowerLoss _ _ _ installed ih
  | batchAppendProcessExit _ _ _ installed ih
  | batchAppendAdmitted _ _ installed ih =>
    obtain ⟨_, _, history, retention⟩ := ih
    exact ⟨installed.retained, appendUncertainBatch retention history (.inl installed.history)⟩
  | collectRuns _ _ reports ih =>
    obtain ⟨ready, retained, history, retention⟩ := ih
    exact ⟨(reports.preservesRetained ready).1, retained, history, retention⟩
  | collectRunsPowerLoss _ _ _ installed ih =>
    obtain ⟨_, retained, history, retention⟩ := ih
    exact ⟨installed.retained, retained, installed.history.trans history, retention⟩
  | rotationPowerLossAdmitted _ _ installed ih =>
    obtain ⟨_, retained, history, retention⟩ := ih
    exact ⟨installed.retained, retained, installed.history.trans history, retention⟩

/-- Keep the submission log, installed table and lock across a reported
run collection outcome. A crash run map retains the same strict checkpoint
under the still-settled manifest used by the unchanged WAL. -/
theorem SegmentedBatchDatabaseTrace.collectObsoleteRuns
    {runs : CheckpointPublication.RunUnlinkImage}
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (initialReady : initial.RetainedReady directory initialDescriptor) (enabled : allowCollection = true)
    (reports : SegmentedRunCollectionReports directory before runs) :
    SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer
      (before.afterRunCollection reports.reached.guaranteed) ∧
    ∀ survived ∈ reports.reached.crashImages,
      SelectedIntegrityCheckpoint survived before.target.pair.manifest before.checkpoint :=
  ⟨.collectRuns enabled trace reports, (reports.preservesRetained (trace.preservesRetained initialReady).1).2⟩

/-- Continue at the exact marked open after a crash during obsolete-run
collection. Surviving run bytes and the unchanged WAL determine replay. -/
theorem SegmentedBatchDatabaseTrace.collectObsoleteRunsPowerLoss {files : Type} {input : System.FilePath}
    {retry : LockedFileState FileImage} {runs : CheckpointPublication.RunUnlinkImage}
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (initialReady : initial.RetainedReady directory initialDescriptor) (enabled : allowCollection = true)
    {reports : SegmentedRunCollectionReports directory before runs} (loss : SegmentedRunCollectionPowerLoss reports)
    (attempts : BoundedReopenTrace directory (fun target => target = before.target) loss.crashed retry)
    (reads : loss.ReopenObservations files input retry) :
    ∃ descriptor after, loss.Installs (files := files) input retry descriptor after ∧
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after := by
  obtain ⟨descriptor, after, installed⟩ := loss.reopensAdmitted (trace.preservesRetained initialReady).1 attempts reads
  exact ⟨descriptor, after, installed, .collectRunsPowerLoss enabled trace loss installed⟩

/-- Continue the mixed history at the exact reported clean reopen. Explicit
unlock and reacquisition change the session while the checkpoint binding
and the submission log stay fixed. -/
theorem SegmentedBatchDatabaseTrace.reopenAfterCleanCloseAdmission {files : Type} {input : System.FilePath}
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (ready : initial.RetainedReady directory initialDescriptor) (closed : CleanUnlockReports directory writer)
    (observes : closed.ReopenObservations files input before) :
    ∃ (layout : CanonicalKeeperLayout (SegmentedCleanReopenReport.released directory before).image before.history)
      (observed : MarkedRetryChunkReports files directory layout before.published)
      (admission : OpenAdmissionReports input directory observed.slot) (after : SegmentedWriterState),
      AdmittedCleanReopen closed observed admission after ∧
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log observed.slot.description after := by
  obtain ⟨layout, observed, admission, after, endpoint⟩ :=
    (trace.preservesRetained ready).1.closeWithAdmission closed observes
  exact ⟨layout, observed, admission, after, endpoint, .cleanReopenObserved trace closed endpoint⟩

/-- A nonempty reported batch extends the mixed trace at the same ready
writer and owner returned by the complete native batch schedule. The
reported operations determine the next cache and the durable WAL selection. -/
theorem SegmentedBatchDatabaseTrace.acknowledgeObservedBatch {handle : Type}
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (initialReady : initial.RetainedReady directory initialDescriptor)
    (report : SegmentedBatchAppendReport directory before) (observed : ObservedBatchWrite report handle) :
    ∃ target cacheAfter,
      runBatchWrite directory report.rows observed.guard.lookup observed.append observed.stage observed.sync observed.rename
        (.ready before.installed, ⟨(observed.cache, WriteFiles.initial before.history
          (before.files.directory.staged .walBoundary)), before.owners⟩) =
        .ok report.table.committed (.ready (report.next target).installed,
          ⟨(cacheAfter, report.written), (report.next target).owners⟩) ∧
      (report.next target).RetainedReady directory writer ∧
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.acknowledgedBatch report.batch]) writer (report.next target) := by
  obtain ⟨cacheAfter, returned⟩ := observed.acknowledges
  obtain ⟨target, selected, ready⟩ := report.preservesRetained (trace.preservesRetained initialReady).1
  exact ⟨target, cacheAfter, returned, ready, .acknowledgedBatch trace report selected⟩

/-- The admitted reopen after checkpoint recovery returns the exact next
writer in the mixed trace. The run map can change without a write submission. -/
theorem SegmentedBatchDatabaseTrace.reopenAfterCheckpointPowerLossChunks {files : Type} {input : System.FilePath}
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (ready : initial.RetainedReady directory initialDescriptor) (cut : CheckpointPowerCut directory before)
    (published : CheckpointPublication.Image)
    (projected : before.published.executeVersioned cut.checkpoint.plan cut.checkpoint.cut = some published)
    (pair : DirectoryPublication.Bindings) (survives : pair ∈ (published.segmentedCheckpointView before.wal).directory.crashImages)
    (retry : LockedFileState FileImage)
    (failures : BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
      ⟨(CheckpointPowerCut.physical before published).crash pair (some before.wal.active.bytes) [],
        before.owners.set (directory.file .lock) none⟩ retry)
    (observes : ∀ layout : CanonicalKeeperLayout retry.image before.history,
      layout.keeper = before.wal.active → layout.tail = ByteArray.empty →
      layout.sealed ++ [layout.keeper] = (published.segmentedCheckpointView before.wal).readDescriptors layout.range.watermark →
      ∃ observed : MarkedRetryChunkReports files directory layout published,
        Nonempty (OpenAdmissionReports input directory observed.slot)) :
    ∃ (layout : CanonicalKeeperLayout retry.image before.history)
      (observed : MarkedRetryChunkReports files directory layout published) (after : SegmentedWriterState),
      CheckpointChunkWriter directory before published observed after ∧
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log observed.slot.description after ∧
      after.target.pair = pair ∧
      ((after.installed.generation = before.installed.generation ∧ pair.manifest = before.wal.directory.active.manifest) ∨
        (after.installed.generation = SegmentedCheckpointReport.generation before ∧ pair.manifest = some cut.checkpoint.manifest)) ∧
      ∃ (admission : OpenAdmissionReports input directory observed.slot)
        (session : SegmentedSession) (final : LockedFileState FileImage),
        observed.runWithAdmission admission = .ok session final ∧
        session.directory = directory ∧ session.descriptor = observed.slot.description ∧
        session.phase = .ready after.installed ∧ final.owners.Owns directory session.descriptor ∧
        final.image.directory.active = pair ∧ after.files = final.image ∧ after.owners = final.owners := by
  have beforeReady := (trace.preservesRetained ready).1
  obtain ⟨_, layout, observed, admission, _, _, _, _, session, final, returned, path, lock, _, held, selected,
    finalPair, _, _, _, generation,
    _, _, _, _, _, _, _, after, installed, _, installedPayload, _⟩ :=
    cut.reopensFromChunks beforeReady published projected pair survives retry failures (fun _ _ => True)
      (fun layout keeper aligned descriptors => by
        obtain ⟨observed, ⟨admission⟩⟩ := observes layout keeper aligned descriptors
        exact ⟨observed, admission, trivial⟩)
  obtain ⟨phase, afterFiles, afterOwners⟩ :=
    installed.atReopen ((observed.runWithAdmission_eq admission).symm.trans returned)
  exact ⟨layout, observed, after, installed,
    .checkpointPowerLossObserved trace cut projected survives failures selected installed,
    (congrArg Target.pair installed.target).trans selected, installedPayload.symm ▸ generation,
    admission, session, final, returned, path, lock, phase, held, finalPair, afterFiles, afterOwners⟩

/-- Extend the trace using the actual failed commit, lock release and
bounded reopen reports. Retained readiness is derived from the prior trace. -/
theorem SegmentedBatchDatabaseTrace.reopenAfterBatchError
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (ready : initial.RetainedReady directory initialDescriptor)
    (report : SegmentedBatchRecoveryReport directory before writer descriptor) :
    ∃ after, report.Installs after ∧
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch report.failure.batch]) descriptor after := by
  obtain ⟨after, installed, _⟩ := report.installsRetained (trace.preservesRetained ready).1
  exact ⟨after, installed, .batchError trace report installed⟩

/-- The batch schedule returns the exact poisoned state that is released.
The healthy retry continues from the same projected file cut and records
one uncertain submission. -/
theorem SegmentedBatchDatabaseTrace.reopenAfterObservedBatchError {handle : Type}
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (initialReady : initial.RetainedReady directory initialDescriptor)
    (report : SegmentedBatchRecoveryReport directory before writer descriptor)
    (observed : ObservedBatchFailure report.failure handle) :
    ∃ cacheAfter after,
      let poisoned : Phase Installed × LockedFileState (SyncHandleRouting.Cache handle × WriteFiles) :=
        (.poisoned, ⟨(cacheAfter, report.failure.failed), before.owners⟩)
      runBatchWrite directory report.failure.rows observed.guard.lookup observed.append observed.stage
        observed.sync observed.rename (.ready before.installed, ⟨(observed.cache, WriteFiles.initial
          before.history (before.wal.directory.staged .walBoundary)), before.owners⟩) =
        .error (.commitUnknown report.failure.cause) poisoned ∧
      report.release.Observed (directory := directory) poisoned
        ⟨poisoned.2.image, report.failure.released.owners⟩ ∧
      report.Installs after ∧
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch report.failure.batch]) descriptor after := by
  obtain ⟨cacheAfter, returned⟩ := observed.commitUnknown
  obtain ⟨after, installed, continued⟩ := trace.reopenAfterBatchError initialReady report
  have held := (trace.preservesRetained initialReady).1.held
  obtain ⟨closed, dropped, _⟩ := runCloseWithFiles_handoff
    (phase := (.poisoned : Phase Installed)) (before := ⟨(cacheAfter, report.failure.failed), before.owners⟩)
    (by simp) held
  refine ⟨cacheAfter, after, returned, ?_, installed, continued⟩
  cases report.release with
  | closed => exact closed
  | references held drops last => exact dropped held drops last

/-- Continue from the exact poisoned result through the admitted native
open and record one uncertain batch. -/
theorem SegmentedBatchDatabaseTrace.reopenAfterObservedBatchErrorWithAdmission {files handle : Type}
    {input : System.FilePath} {retry : LockedFileState FileImage}
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (initialReady : initial.RetainedReady directory initialDescriptor)
    (failure : SegmentedBatchFailure directory before) (observed : ObservedBatchFailure failure handle)
    (release : SegmentedFailureRelease writer)
    (attempts : BoundedReopenTrace directory (BatchRetryTarget before.history failure.batch before.wal.active.first)
      failure.released retry)
    (reads : BatchCutReopenObservations directory before failure.batch files input retry) :
    ∃ descriptor after, observed.AdmittedReopen (files := files) release input retry descriptor after ∧
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch failure.batch]) descriptor after := by
  obtain ⟨descriptor, after, installed⟩ :=
    observed.reopensAdmitted (trace.preservesRetained initialReady).1 release attempts reads
  exact ⟨descriptor, after, installed, .batchErrorAdmitted trace failure observed installed⟩

/-- Extend the mixed trace through a batch interrupted by machine power
loss and the next healthy cached installation. The batch contributes one
uncertain submission even when none of its frames survive selection. -/
theorem SegmentedBatchDatabaseTrace.reopenAfterBatchPowerLoss
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (ready : initial.RetainedReady directory initialDescriptor)
    (cut : SegmentedBatchMarkerPowerLossReport directory before writer) (observed : cut.Valid)
    (report : cut.CachedReopenReports descriptor) :
    ∃ after, report.Installs after ∧
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch cut.batch]) descriptor after := by
  obtain ⟨after, installed⟩ := report.installs observed (trace.preservesRetained ready).1
  exact ⟨after, installed, .batchPowerLoss trace cut observed report installed⟩

/-- Process exit during marker publication records one uncertain batch.
The exact final cached installation supplies the next writer in the trace. -/
theorem SegmentedBatchDatabaseTrace.reopenAfterBatchMarkerProcessExit
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (ready : initial.RetainedReady directory initialDescriptor)
    (cut : SegmentedBatchMarkerPowerLossReport directory before writer) (observed : cut.Reached)
    (report : cut.ProcessExitCachedReopenReports descriptor) :
    ∃ after, report.reopen.InstallsFromCut after ∧
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch cut.batch]) descriptor after := by
  obtain ⟨after, installed⟩ := report.installs observed (trace.preservesRetained ready).1
  exact ⟨after, installed, .batchMarkerProcessExit trace cut observed report installed⟩

/-- Extend the trace by a reached marker-publication cut, its admitted
retry lineage, and the exact marked open of the selected files. -/
theorem SegmentedBatchDatabaseTrace.reopenAfterBatchMarkerWithAdmission {files : Type}
    {input : System.FilePath} {retry : LockedFileState FileImage}
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (ready : initial.RetainedReady directory initialDescriptor)
    (cut : SegmentedBatchMarkerPowerLossReport directory before writer) (observed : cut.Reached)
    (attempts : BoundedReopenTrace directory (BatchRetryTarget before.history cut.batch before.wal.active.first)
      cut.inFlight retry)
    (reads : ∀ history, ∀ layout : CanonicalKeeperLayout retry.image history,
      (history = before.history ∨ history = before.history ++ cut.batch) →
      layout.target.first = before.wal.active.first →
      ∃ reported : MarkedRetryChunkReports files directory layout before.published,
        Nonempty (OpenAdmissionReports input directory reported.slot)) :
    ∃ descriptor after, cut.AdmittedRetry (files := files) input retry descriptor after ∧
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch cut.batch]) descriptor after := by
  obtain ⟨descriptor, after, installed⟩ :=
    observed.installsAdmitted (trace.preservesRetained ready).1 attempts reads
  exact ⟨descriptor, after, installed, .batchMarkerAdmitted trace cut observed installed⟩

/-- A batch interrupted before marker publication contributes one uncertain
submission and no retained frames. The next cached open installs the old
history and supports the same remaining trace operations. -/
theorem SegmentedBatchDatabaseTrace.reopenAfterBatchAppendPowerLoss
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (ready : initial.RetainedReady directory initialDescriptor)
    (report : SegmentedBatchAppendPowerLossReport directory before descriptor) (observed : report.Valid) :
    ∃ after, report.Installs after ∧
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch report.reopen.batch]) descriptor after := by
  obtain ⟨after, installed⟩ := report.installs observed (trace.preservesRetained ready).1
  exact ⟨after, installed, .batchAppendPowerLoss trace report observed installed⟩

/-- Process exit before marker publication records an uncertain batch and
installs the old history from the live WAL and observed lock transitions. -/
theorem SegmentedBatchDatabaseTrace.reopenAfterBatchAppendProcessExit
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (ready : initial.RetainedReady directory initialDescriptor)
    (report : SegmentedBatchAppendProcessExitReport directory before writer descriptor)
    (observed : report.reopen.Valid) :
    ∃ after, report.reopen.Installs after ∧
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch report.reopen.batch]) descriptor after := by
  obtain ⟨after, installed⟩ := report.installs observed (trace.preservesRetained ready).1
  exact ⟨after, installed, .batchAppendProcessExit trace report observed installed⟩

/-- A first-append interruption and the admitted marked reopen continue
the mixed trace at the exact returned writer, with no retained frames
from the uncertain batch. -/
theorem SegmentedBatchDatabaseTrace.reopenAfterBatchAppendWithAdmission {files : Type}
    {input : System.FilePath} {retry : LockedFileState FileImage}
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (ready : initial.RetainedReady directory initialDescriptor)
    (report : BatchAppendInterruption directory before) (observed : report.Valid) (stop : report.Stop writer)
    (attempts : BoundedReopenTrace directory (fun target => target = before.target) stop.origin retry)
    (reads : BatchAppendInterruption.ReopenObservations directory before files input retry) :
    ∃ descriptor after, report.AdmittedReopen (files := files) stop input retry descriptor after ∧
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch report.batch]) descriptor after := by
  obtain ⟨descriptor, after, installed⟩ := stop.reopensAdmitted observed (trace.preservesRetained ready).1 attempts reads
  exact ⟨descriptor, after, installed, .batchAppendAdmitted trace report installed⟩

/-- Continue at the exact admitted reopen after power loss interrupted
rotation. The survivor changes the keeper layout while the submission log
and retained history carry over to the reopened writer. -/
theorem SegmentedBatchDatabaseTrace.reopenAfterRotationWithAdmission {files : Type}
    {input : System.FilePath} {retry : LockedFileState FileImage}
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (ready : initial.RetainedReady directory initialDescriptor) (cut : RotationInFlightCut directory before)
    {pair : DirectoryPublication.Bindings} {present : Bool}
    (metadata : pair ∈ cut.image.metadata.crashImages) (survives : cut.image.successor.MaySurvive present)
    (attempts : BoundedReopenTrace directory (CheckpointRetryTarget before.history (cut.survivingWal pair present).active.first)
      (cut.crashedFiles pair present) retry)
    (reads : cut.ReopenObservations pair present files input retry) :
    ∃ descriptor after, cut.AdmittedReopen (files := files) pair present input retry descriptor after ∧
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after := by
  obtain ⟨descriptor, after, installed⟩ :=
    cut.reopensAdmitted (trace.preservesRetained ready).1 metadata survives retry attempts reads
  exact ⟨descriptor, after, installed, .rotationPowerLossAdmitted trace cut installed⟩

/-- Reads through active snapshot pins in the current session agree with
replay of the retained history, including after an uncertain batch. -/
theorem SegmentedBatchDatabaseTrace.pinnedReads
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log descriptor last)
    (ready : initial.RetainedReady directory initialDescriptor) :
    ∃ reference : SnapshotTable UInt64, SnapshotWalReplay .empty last.history reference ∧
      ∀ pin ∈ last.installed.table.pins.active,
        (∀ key, last.installed.table.lookup pin.handle key = some (reference.table.lookup key pin.sequence)) ∧
        ∀ start stop, last.installed.table.range pin.handle start stop =
          some (reference.table.range start stop pin.sequence) :=
  (trace.preservesRetained ready).1.pinnedReads

/-- A supported snapshot can be acquired against the installed table and
reads the corresponding version of the retained history. -/
theorem SegmentedBatchDatabaseTrace.acquireReads
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log descriptor last)
    (ready : initial.RetainedReady directory initialDescriptor) {snapshot : UInt64}
    (retained : last.installed.table.pins.floor ≤ snapshot) (committed : snapshot ≤ last.installed.table.committed) :
    ∃ reference : SnapshotTable UInt64, SnapshotWalReplay .empty last.history reference ∧
      ∃ pin pinned, last.installed.table.acquireAt snapshot = some (pin, pinned) ∧
        (∀ key, pinned.lookup pin.handle key = some (reference.table.lookup key snapshot)) ∧
        ∀ start stop, pinned.range pin.handle start stop = some (reference.table.range start stop snapshot) :=
  (trace.preservesRetained ready).1.acquireReads retained committed

/-- From the installed empty writer, one abstract replay explains the retained
history and every supported snapshot. Each acknowledged batch is retained in
full, and each uncertain batch contributes all its frames or none. -/
theorem SegmentedBatchDatabaseTrace.keyValueRefinement
    {directory initialDescriptor allowCollection log descriptor last}
    {first : LockedFileState WalSegmentRotation.State} (bootstrap : BootstrapReady first.image)
    (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log descriptor last) :
    ∃ reference : SnapshotTable UInt64,
      SnapshotWalReplay .empty last.history reference ∧
      DatabaseBatchRetention log last.history ∧
      log.flatMap DatabaseSubmissions.acknowledged <+ last.history ∧
      last.history <+ log.flatMap DatabaseSubmissions.submitted ∧
      ∀ snapshot, last.installed.table.pins.floor ≤ snapshot → snapshot ≤ last.installed.table.committed →
        ∃ pin pinned, last.installed.table.acquireAt snapshot = some (pin, pinned) ∧
          (∀ key, pinned.lookup pin.handle key = some (reference.table.lookup key snapshot)) ∧
          ∀ start stop, pinned.range pin.handle start stop = some (reference.table.range start stop snapshot) := by
  obtain ⟨ready, retained, history, retention⟩ := trace.preservesRetained (bootstrap.writerReady held).toRetained
  change last.history = [] ++ retained at history
  simp only [List.nil_append] at history
  subst retained
  obtain ⟨acknowledged, submitted⟩ := retention.orderedSubmissions
  obtain ⟨reference, replayed⟩ := SnapshotWalReplay.fromEmpty last.history ready.resumed.ordered
  refine ⟨reference, replayed, retention, acknowledged, submitted, ?_⟩
  intro snapshot floor committed
  obtain ⟨other, sameReplay, pin, pinned, acquired, lookup, range⟩ := ready.acquireReads floor committed
  have same := replayed.deterministic sameReplay
  cases same
  exact ⟨pin, pinned, acquired, lookup, range⟩

/-- The final writer uses the same snapshot guard as the adapter. The
observed session comparison determines whether the newly acquired pin
can read its exact abstract snapshot through that guard. -/
theorem SegmentedBatchDatabaseTrace.guardedKeyValueRefinement
    {directory initialDescriptor allowCollection log descriptor last}
    {first : LockedFileState WalSegmentRotation.State} (bootstrap : BootstrapReady first.image)
    (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log descriptor last) :
    ∃ reference : SnapshotTable UInt64,
      SnapshotWalReplay .empty last.history reference ∧
      DatabaseBatchRetention log last.history ∧
      log.flatMap DatabaseSubmissions.acknowledged <+ last.history ∧
      last.history <+ log.flatMap DatabaseSubmissions.submitted ∧
      ∀ snapshot, last.installed.table.pins.floor ≤ snapshot → snapshot ≤ last.installed.table.committed →
        ∃ pin pinned, last.installed.table.acquireAt snapshot = some (pin, pinned) ∧
          ∀ (sameSession : Bool) (issuer current : Nat), sameSession = decide (issuer = current) →
            (∀ key, readWithHandle (.ready pinned) sameSession (fun table => table.lookup pin.handle key) =
              .ok (if issuer = current then some (reference.table.lookup key snapshot) else none)) ∧
            ∀ start stop, readWithHandle (.ready pinned) sameSession (fun table => table.range pin.handle start stop) =
              .ok (if issuer = current then some (reference.table.range start stop snapshot) else none) := by
  obtain ⟨reference, replayed, retained, acknowledged, submitted, reads⟩ :=
    trace.keyValueRefinement bootstrap held
  refine ⟨reference, replayed, retained, acknowledged, submitted, ?_⟩
  intro snapshot floor committed
  obtain ⟨pin, pinned, acquired, lookup, range⟩ := reads snapshot floor committed
  refine ⟨pin, pinned, acquired, ?_⟩
  intro sameSession issuer current compared
  by_cases localToken : issuer = current
  · rw [compared.trans (decide_eq_true localToken)]
    simp only [localToken, ↓reduceIte]
    exact ⟨fun key => congrArg Except.ok (lookup key), fun start stop => congrArg Except.ok (range start stop)⟩
  · simp only [localToken, ↓reduceIte]
    exact ⟨fun key => readWithHandle_foreign pinned _ compared localToken,
      fun start stop => readWithHandle_foreign pinned _ compared localToken⟩

/-- One retained history explains the acknowledged writes and the guarded
point and range reads of every supported snapshot. The reached ready cell
registers the pin and issues its own session token. -/
theorem SegmentedBatchDatabaseTrace.guardedAcquireReads
    {directory initialDescriptor allowCollection log descriptor last}
    {first : LockedFileState WalSegmentRotation.State} (bootstrap : BootstrapReady first.image)
    (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log descriptor last)
    {session : SegmentedSession} (readyPhase : session.phase = .ready last.installed) :
    ∃ reference : SnapshotTable UInt64,
      SnapshotWalReplay .empty last.history reference ∧
      DatabaseBatchRetention log last.history ∧
      log.flatMap DatabaseSubmissions.acknowledged <+ last.history ∧
      last.history <+ log.flatMap DatabaseSubmissions.submitted ∧
      GuardedAcquireReads last.installed session reference := by
  obtain ⟨reference, replayed, retained, acknowledged, submitted, reads⟩ := trace.keyValueRefinement bootstrap held
  exact ⟨reference, replayed, retained, acknowledged, submitted, session.guardedAcquireReads readyPhase reads⟩

/-- Reacquiring an earlier pin's sequence preserves its reads while the
final writer still retains that sequence. -/
theorem SegmentedBatchDatabaseTrace.reacquireReadsStable
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log descriptor last)
    (initialReady : initial.RetainedReady directory initialDescriptor) {oldPin : SnapshotPin}
    (active : oldPin ∈ initial.installed.table.pins.active)
    (retained : last.installed.table.pins.floor ≤ oldPin.sequence) :
    ∃ newPin pinned, last.installed.table.acquireAt oldPin.sequence = some (newPin, pinned) ∧
      newPin.sequence = oldPin.sequence ∧
      (∀ key, pinned.lookup newPin.handle key = initial.installed.table.lookup oldPin.handle key) ∧
      ∀ start stop, pinned.range newPin.handle start stop = initial.installed.table.range oldPin.handle start stop := by
  obtain ⟨ready, _, history, _⟩ := trace.preservesRetained initialReady
  exact initialReady.reacquireReadsStable ready history active retained

/-- In a freshly installed session, reacquiring a still-supported sequence
issues a local pin whose guarded reads equal the earlier snapshot. The old
token stays foreign even if the new pin reuses its local handle number. -/
theorem SegmentedBatchDatabaseTrace.reacquireGuardedReadsStable
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log descriptor last)
    (initialReady : initial.RetainedReady directory initialDescriptor) {oldPin : SnapshotPin}
    (active : oldPin ∈ initial.installed.table.pins.active)
    (retained : last.installed.table.pins.floor ≤ oldPin.sequence)
    {earlier session : SegmentedSession} (earlierReady : earlier.phase = .ready initial.installed)
    (readyPhase : session.phase = .ready last.installed)
    {liveRefs : List Nat} (oldLive : earlier.sessionRef ∈ liveRefs)
    (fresh : session.sessionRef ∉ liveRefs) :
    ∃ (newPin : SnapshotPin) (pinned : PackedTable) (after : SegmentedSession),
      SegmentedSession.runAcquireAt oldPin.sequence session = .ok (some (after.sessionRef, newPin)) after ∧
      after.phase = .ready { last.installed with table := pinned } ∧
      newPin.sequence = oldPin.sequence ∧ newPin ∈ pinned.pins.active ∧ earlier.sessionRef ≠ after.sessionRef ∧
      ∀ localCompared oldCompared : Bool,
        localCompared = decide (session.sessionRef = after.sessionRef) →
        oldCompared = decide (earlier.sessionRef = after.sessionRef) →
        (∀ key, readWithHandle (.ready pinned) localCompared (fun table => table.lookup newPin.handle key) =
          withLocalHandle (m := Except IO.Error) earlier.phase.installed (.ok true) none
            (fun state => pure (state.table.lookup oldPin.handle key))) ∧
        (∀ start stop, readWithHandle (.ready pinned) localCompared (fun table => table.range newPin.handle start stop) =
          withLocalHandle (m := Except IO.Error) earlier.phase.installed (.ok true) none
            (fun state => pure (state.table.range oldPin.handle start stop))) ∧
        (∀ key, readWithHandle (.ready pinned) oldCompared (fun table => table.lookup oldPin.handle key) = .ok none) ∧
        ∀ start stop, readWithHandle (.ready pinned) oldCompared
          (fun table => table.range oldPin.handle start stop) = .ok none := by
  obtain ⟨newPin, pinned, acquired, sequence, lookup, range⟩ := trace.reacquireReadsStable initialReady active retained
  let after := { session with phase := .ready { last.installed with table := pinned } }
  have different : earlier.sessionRef ≠ after.sessionRef := by
    intro same
    exact fresh (same ▸ oldLive)
  refine ⟨newPin, pinned, after, SegmentedSession.runAcquireAt_ready readyPhase acquired,
    rfl, sequence, (PackedTable.acquireAt_spec acquired).active, different, ?_⟩
  intro localCompared oldCompared localReport oldReport
  have localToken : localCompared = true := localReport.trans (decide_eq_true rfl)
  rw [localToken, earlierReady]
  exact ⟨fun key => congrArg Except.ok (lookup key), fun start stop => congrArg Except.ok (range start stop),
    fun key => readWithHandle_foreign pinned _ oldReport different,
    fun start stop => readWithHandle_foreign pinned _ oldReport different⟩

end Alvoki.Storage.DiskSession
