import Alvoki.Storage.Disk.CheckpointRunFileSyncFailure
import Alvoki.Storage.Disk.PriorCheckpointLiveReopen

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair
open WAL.Boundary (WalInodeImage)

private abbrev Handle := DescriptorInventory × DescriptorSlot
private abbrev State := SyncHandleRouting.Cache Handle × WalInodeImage

variable {directory : DiskDirectory} {before : SegmentedWriterState}
  {attempt : SegmentedCheckpointReport directory before}

/-- The off-target manifest projection at the initial run prefix, each
successfully returned pair, and the selected pair's reached error. -/
structure RunPrefixManifestFrames (report : ObservedCheckpointRunPrefix attempt)
    (reached : State) (manifest : State → Publication.Image) : Prop where
  entry : manifest (report.atRun 0) = before.published.manifest
  earlier : ∀ index < report.index, manifest (report.atRun (index + 1)) = manifest (report.atRun index)
  failed : manifest reached = manifest (report.atRun report.index)

theorem RunPrefixManifestFrames.preserves {report : ObservedCheckpointRunPrefix attempt} {reached : State}
    {manifest : State → Publication.Image} (frames : RunPrefixManifestFrames report reached manifest) :
    manifest reached = before.published.manifest := by
  have preserved (through : Nat) (within : through ≤ report.index) :
      manifest (report.atRun through) = before.published.manifest := by
    induction through with
    | zero => exact frames.entry
    | succ previous ih => exact (frames.earlier previous within).trans (ih (Nat.le_trans (Nat.le_succ _) within))
  exact frames.failed.trans (preserved report.index (Nat.le_refl _))

theorem ObservedCheckpointRunPrefix.reopensPrior {input : FilePath} {writer : Nat}
    (report : ObservedCheckpointRunPrefix attempt) {reached : State} {cause : IO.Error}
    (failure : CheckpointPublication.run attempt.table.runs.length report.perform (report.atRun 0) = .error cause reached)
    (ready : before.RetainedReady directory writer)
    {manifest : State → Publication.Image} (frames : RunPrefixManifestFrames report reached manifest)
    (selected : SelectedRunsAgree before.wal.directory.active.manifest (report.runs reached).guaranteed before.published.durable)
    (release : SegmentedFailureRelease writer) (retry : LockedFileState FileImage) :
    let publication := (report.runs reached).project (manifest reached)
    BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
      ⟨CheckpointPowerCut.physical before publication, before.owners.set (directory.file .lock) none⟩ retry →
    CheckpointHeldOpen.Reports input directory before retry publication publication →
    ∃ (layout : CanonicalKeeperLayout retry.image before.history)
      (opened : CheckpointHeldOpen input directory layout publication)
      (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState),
      runPreparedCheckpoint attempt.prepared report.perform (.ready before.installed, ⟨report.atRun 0, before.owners⟩) =
        .error cause (.poisoned, ⟨reached, before.owners⟩) ∧
      release.Observed (directory := directory) (.poisoned, ⟨reached, before.owners⟩)
        ⟨reached, before.owners.set (directory.file .lock) none⟩ ∧
      PriorCheckpointReopened opened session final after := by
  intro publication attempts reads
  have unchanged : publication.manifest = before.published.manifest := frames.preserves
  have active : publication.manifest.active = before.wal.directory.active.manifest := by
    rw [unchanged, ready.manifestFiles, ready.directoryFiles]
    rfl
  have choices : publication.manifest.crashImages = [before.wal.directory.active.manifest] := by
    rw [unchanged, ready.manifestFiles, ready.directoryFiles]
    simp [DirectoryPublication.Image.project, DirectoryPublication.Bindings.get, ready.walDirectorySettled]
  obtain ⟨layout, opened, session, final, after, installed⟩ :=
    ready.reopensPriorCheckpointLive publication active choices selected retry attempts reads
  obtain ⟨poisoned, released, _⟩ := report.poisonsAndReleases failure ready.held release
  exact ⟨layout, opened, session, final, after, poisoned, released, installed⟩

abbrev RunSyncFailureManifestFrames (report : ObservedCheckpointRunSyncFailure attempt)
    (manifest : State → Publication.Image) : Prop :=
  RunPrefixManifestFrames report.toObservedCheckpointRunPrefix report.reached manifest

namespace ObservedCheckpointRunSyncFailure

/-- Preserve the reached physical run guarantees. A file's own fsync can
settle its bytes while its new directory binding remains uncertain. -/
def reachedPublication (report : ObservedCheckpointRunSyncFailure attempt)
    (manifest : State → Publication.Image) : Image :=
  ⟨manifest report.reached, (report.runs report.reached).guaranteed⟩

theorem priorManifest (report : ObservedCheckpointRunSyncFailure attempt)
    {manifest : State → Publication.Image} (frames : RunSyncFailureManifestFrames report manifest) :
    (report.reachedPublication manifest).manifest = before.published.manifest := frames.preserves

/-- The old manifest remains selected after the failed private run sync.
Release leaves exactly the reached files. The same reported admitted
retry installs the old checkpoint and retained WAL replay. -/
theorem reopens {input : FilePath} {writer : Nat}
    (report : ObservedCheckpointRunSyncFailure attempt)
    (ready : before.RetainedReady directory writer)
    (entry : CheckpointRunPrefix.EntrySelection before (report.view 0))
    {manifest : State → Publication.Image} (frames : RunSyncFailureManifestFrames report manifest)
    (release : SegmentedFailureRelease writer) (retry : LockedFileState FileImage) :
    let publication := report.reachedPublication manifest
    BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
      ⟨CheckpointPowerCut.physical before publication, before.owners.set (directory.file .lock) none⟩ retry →
    CheckpointHeldOpen.Reports input directory before retry publication publication →
    ∃ (layout : CanonicalKeeperLayout retry.image before.history)
      (opened : CheckpointHeldOpen input directory layout publication)
      (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState),
      runPreparedCheckpoint attempt.prepared report.perform (.ready before.installed, ⟨report.atRun 0, before.owners⟩) =
        .error report.error (.poisoned, ⟨report.reached, before.owners⟩) ∧
      release.Observed (directory := directory) (.poisoned, ⟨report.reached, before.owners⟩)
        ⟨report.reached, before.owners.set (directory.file .lock) none⟩ ∧
      PriorCheckpointReopened opened session final after :=
  report.toObservedCheckpointRunPrefix.reopensPrior report.returns ready frames (report.priorRuns ready entry) release retry

end ObservedCheckpointRunSyncFailure

end Alvoki.Storage.DiskSession
