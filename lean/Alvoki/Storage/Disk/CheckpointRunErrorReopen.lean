import Alvoki.Storage.Disk.CheckpointRunGuardFailure
import Alvoki.Storage.Disk.CheckpointRunOpenFailure
import Alvoki.Storage.Disk.CheckpointRunDataFailure
import Alvoki.Storage.Disk.CheckpointRunDirectoryFailure

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair
open WAL.Boundary (WalInodeImage)

private abbrev RunState := SyncHandleRouting.Cache (DescriptorInventory × DescriptorSlot) × WalInodeImage

variable {directory : DiskDirectory} {before : SegmentedWriterState}
  {attempt : SegmentedCheckpointReport directory before}

/-- The guarded run callback or its own file sync returns an error.
Each constructor fixes the same checkpoint prefix, error and reached image
that the corresponding native-shaped report supplies. -/
inductive CheckpointRunError : ObservedCheckpointRunPrefix attempt → IO.Error → RunState → Prop where
  | guard {runs : ObservedCheckpointRunPrefix attempt} (report : ObservedCheckpointRunGuardFailure runs) :
      CheckpointRunError runs report.cause (runs.atRun runs.index)
  | writeOpen {runs : ObservedCheckpointRunPrefix attempt} (report : ObservedCheckpointRunOpenFailure runs) :
      CheckpointRunError runs report.cause report.reachedFiles
  | writeData {runs : ObservedCheckpointRunPrefix attempt} (report : ObservedCheckpointRunDataFailure runs) :
      CheckpointRunError runs report.cause report.reached
  | fileSync (report : ObservedCheckpointRunSyncFailure attempt) :
      CheckpointRunError report.toObservedCheckpointRunPrefix report.error report.reached

namespace CheckpointRunError

variable {runs : ObservedCheckpointRunPrefix attempt} {cause : IO.Error} {reached : RunState}

theorem returns (reported : CheckpointRunError runs cause reached) :
    CheckpointPublication.run attempt.table.runs.length runs.perform (runs.atRun 0) = .error cause reached := by
  cases reported with
  | guard report => exact report.returns
  | writeOpen report => exact report.returns
  | writeData report => exact report.returns
  | fileSync report => exact report.returns

theorem priorRuns (reported : CheckpointRunError runs cause reached) {writer : Nat}
    (ready : before.RetainedReady directory writer) (entry : CheckpointRunPrefix.EntrySelection before (runs.view 0)) :
    SelectedRunsAgree before.wal.directory.active.manifest (runs.runs reached).guaranteed before.published.durable := by
  cases reported with
  | guard =>
    intro bytes metadata binding decoded index inside
    obtain ⟨_, _, stored, stable, _⟩ := runs.priorStable ready entry binding decoded inside
    exact stable.guaranteed.trans stored.symm
  | writeOpen report => exact report.priorRuns ready entry
  | writeData report => exact report.priorRuns ready entry
  | fileSync report => exact report.priorRuns ready entry

def publication (_reported : CheckpointRunError runs cause reached) (manifest : RunState → Publication.Image) : Image :=
  (runs.runs reached).project (manifest reached)

/-- The reported failed run and admitted retry share one exact released
physical image, including the unchanged selected manifest and run bytes. -/
structure Reopened (reported : CheckpointRunError runs cause reached) {writer : Nat} {input : FilePath}
    {manifest : RunState → Publication.Image} {retry : LockedFileState FileImage}
    {layout : CanonicalKeeperLayout retry.image before.history} (release : SegmentedFailureRelease writer)
    (opened : CheckpointHeldOpen input directory layout (reported.publication manifest))
    (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState) : Prop extends
      PriorCheckpointReopened opened session final after where
  entry : CheckpointRunPrefix.EntrySelection before (runs.view 0)
  frames : RunPrefixManifestFrames runs reached manifest
  poisoned : runPreparedCheckpoint attempt.prepared runs.perform (.ready before.installed, ⟨runs.atRun 0, before.owners⟩) =
    .error cause (.poisoned, ⟨reached, before.owners⟩)
  handoff : release.Observed (directory := directory) (.poisoned, ⟨reached, before.owners⟩)
    ⟨reached, before.owners.set (directory.file .lock) none⟩
  attempts : BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
    ⟨CheckpointPowerCut.physical before (reported.publication manifest), before.owners.set (directory.file .lock) none⟩ retry

/-- The raw branch supplies the reached error and the old run guarantees.
The common installer derives the actual returned session and unchanged WAL. -/
theorem reopens (reported : CheckpointRunError runs cause reached) {writer : Nat} {input : FilePath}
    (ready : before.RetainedReady directory writer) (entry : CheckpointRunPrefix.EntrySelection before (runs.view 0))
    {manifest : RunState → Publication.Image} (frames : RunPrefixManifestFrames runs reached manifest)
    (release : SegmentedFailureRelease writer) (retry : LockedFileState FileImage) :
    let publication := reported.publication manifest
    let released := ⟨CheckpointPowerCut.physical before publication, before.owners.set (directory.file .lock) none⟩
    BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first) released retry →
    CheckpointHeldOpen.Reports input directory before retry publication publication →
    ∃ (layout : CanonicalKeeperLayout retry.image before.history)
      (opened : CheckpointHeldOpen input directory layout publication)
      (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState),
      reported.Reopened release opened session final after := by
  intro publication released attempts reads
  obtain ⟨layout, opened, session, final, after, poisoned, handoff, installed⟩ :=
    runs.reopensPrior reported.returns ready frames (reported.priorRuns ready entry) release retry attempts reads
  exact ⟨layout, opened, session, final, after, installed, entry, frames, poisoned, handoff, attempts⟩

end CheckpointRunError

/-- An admitted reopen following one of the proved errors before manifest
staging. The returned slot and session are fixed by its exact endpoint. -/
inductive PriorCheckpointErrorReopened (writer : Nat) :
    Nat → SegmentedSession → LockedFileState FileImage → SegmentedWriterState → Prop where
  | runError {attempt : SegmentedCheckpointReport directory before} {runs : ObservedCheckpointRunPrefix attempt}
      {cause : IO.Error} {reached : RunState} {reported : CheckpointRunError runs cause reached} {input : FilePath}
      {retry : LockedFileState FileImage} {layout : CanonicalKeeperLayout retry.image before.history}
      {manifest : RunState → Publication.Image} {release : SegmentedFailureRelease writer}
      {opened : CheckpointHeldOpen input directory layout (reported.publication manifest)} {session final}
      (endpoint : reported.Reopened release opened session final after) :
      PriorCheckpointErrorReopened writer opened.calls.slot.description session final after
  | directorySync {cut : CheckpointPowerCut directory before} {reported : ObservedCheckpointRunDirectoryFailure cut}
      {input : FilePath} {retry : LockedFileState FileImage} {layout : CanonicalKeeperLayout retry.image before.history}
      {release : SegmentedFailureRelease writer}
      {opened : CheckpointHeldOpen input directory layout reported.publication} {session final}
      (endpoint : reported.Reopened release opened session final after) :
      PriorCheckpointErrorReopened writer opened.calls.slot.description session final after

/-- The two early routes keep the same prior checkpoint and acknowledged
WAL in the exact ready writer that recovery installed. -/
theorem PriorCheckpointErrorReopened.preservesWriter
    (opened : PriorCheckpointErrorReopened (directory := directory) (before := before) writer descriptor session final after) :
    after.RetainedReady directory descriptor ∧ after.history = before.history ∧
      after.wal = { before.wal with directory := after.files.directory } ∧ after.checkpoint = before.checkpoint := by
  cases opened with
  | runError endpoint => exact ⟨endpoint.retained, endpoint.history, endpoint.wal, endpoint.checkpoint⟩
  | directorySync endpoint => exact ⟨endpoint.retained, endpoint.history, endpoint.wal, endpoint.checkpoint⟩

end Alvoki.Storage.DiskSession
