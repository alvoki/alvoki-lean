import Alvoki.Storage.Disk.Proofs.Checkpoint.CheckpointManifestStageFailure
import Alvoki.Storage.Disk.Proofs.Checkpoint.PriorCheckpointLiveReopen

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair

private abbrev Handle := DescriptorInventory × DescriptorSlot
private abbrev State := SyncHandleRouting.Cache Handle × WAL.Boundary.WalInodeImage

variable {directory : DiskDirectory} {before : SegmentedWriterState}
  {attempt : SegmentedCheckpointReport directory before}

/-- Only the manifest scratch may change after the run-directory sync.
The selected old run bytes are observed in the exact reached namespace.
The settled map can also include new durable orphan files. -/
structure ManifestStageFailureBindings (report : ObservedManifestStageFailure attempt)
    (manifest : State → Publication.Image) (runs : State → RunUnlinkImage) : Prop where
  namesSettled :
    let runState := report.atRun attempt.table.runs.length
    runs (runState.1, report.directorySettled) = (runs runState).syncDirectory
  namesPreserved :
    let runState := report.atRun attempt.table.runs.length
    runs report.reached = runs (runState.1, report.directorySettled)
  active : (manifest report.reached).active = before.wal.directory.active.manifest
  choices : (manifest report.reached).crashImages = [before.wal.directory.active.manifest]
  oldRuns :
    SelectedRunsAgree before.wal.directory.active.manifest
      (runs (report.atRun attempt.table.runs.length)).visible before.published.durable

/-- The reached manifest, including scratch, and the durable run map
returned by the same failed checkpoint callbacks. -/
def ObservedManifestStageFailure.reachedPublication (report : ObservedManifestStageFailure attempt)
    (manifest : State → Publication.Image) (runs : State → RunUnlinkImage) : Image :=
  ⟨manifest report.reached, (runs report.reached).guaranteed⟩

/-- Evidence for one returned checkpoint error, its lock handoff, and
the exact final admitted reopen from the reached live publication. -/
structure ManifestStageFailureReopened {writer : Nat} {input : FilePath}
    {report : ObservedManifestStageFailure attempt}
    {manifest : State → Publication.Image} {runs : State → RunUnlinkImage}
    {retry : LockedFileState FileImage} {layout : CanonicalKeeperLayout retry.image before.history}
    (release : SegmentedFailureRelease writer)
    (opened : CheckpointHeldOpen input directory layout (report.reachedPublication manifest runs))
    (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState) : Prop where
  bindings : ManifestStageFailureBindings report manifest runs
  attempts : BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
    ⟨CheckpointPowerCut.physical before (report.reachedPublication manifest runs),
      before.owners.set (directory.file .lock) none⟩ retry
  poisoned :
    runCheckpointWithEffects (report.callbacks.perform directory)
      (.ready before.installed, ⟨report.atRun 0, before.owners⟩) =
      .error report.cause (.poisoned, ⟨report.reached, before.owners⟩)
  released : release.Observed (directory := directory) (.poisoned, ⟨report.reached, before.owners⟩)
    ⟨report.reached, before.owners.set (directory.file .lock) none⟩
  returned : opened.wal.operations.runWithAdmission opened.admission = .ok session final
  path : session.directory = directory
  descriptor : session.descriptor = opened.calls.slot.description
  phase : session.phase = .ready after.installed
  files : after.files = final.image
  owners : after.owners = final.owners
  retained : after.RetainedReady directory opened.calls.slot.description
  history : after.history = before.history
  wal : after.wal = { before.wal with directory := after.files.directory }
  durable : after.published.durable = (report.reachedPublication manifest runs).durable
  selected : after.target.pair = before.wal.directory.active
  checkpoint : after.checkpoint = before.checkpoint
  replay : recoverSelected (before.checkpoint.getD (.empty, 0)).1 (WAL.encode before.history) = .ok after.installed.table

namespace ManifestStageFailureBindings

variable {report : ObservedManifestStageFailure attempt} {manifest : State → Publication.Image}
  {runs : State → RunUnlinkImage}

private theorem selectedRuns (bindings : ManifestStageFailureBindings report manifest runs) :
    SelectedRunsAgree before.wal.directory.active.manifest (report.reachedPublication manifest runs).durable before.published.durable := by
  have settled : runs report.reached = (runs (report.atRun attempt.table.runs.length)).syncDirectory :=
    bindings.namesPreserved.trans bindings.namesSettled
  intro bytes metadata visible decoded index inside
  change (runs report.reached).guaranteed metadata.header.generation index = _
  rw [settled]
  exact (congrFun (congrFun (congrArg Image.durable
    (RunUnlinkImage.project_settled (runs (report.atRun attempt.table.runs.length)).visible (.settled none)))
    metadata.header.generation) index).trans (bindings.oldRuns bytes metadata visible decoded index inside)

/-- The live retry begins at the exact run map and manifest scratch left
by the returned failure. The admitted opener reads the same old checkpoint
and WAL, yielding a ready writer with the actual retained run map. -/
theorem reopens {input : FilePath} {writer : Nat}
    (bindings : ManifestStageFailureBindings report manifest runs)
    (ready : before.RetainedReady directory writer)
    (release : SegmentedFailureRelease writer) (retry : LockedFileState FileImage) :
    let publication := report.reachedPublication manifest runs
    let released := ⟨CheckpointPowerCut.physical before publication, before.owners.set (directory.file .lock) none⟩
    BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first) released retry →
    CheckpointHeldOpen.Reports input directory before retry publication publication →
    ∃ (layout : CanonicalKeeperLayout retry.image before.history)
      (opened : CheckpointHeldOpen input directory layout publication)
      (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState),
      ManifestStageFailureReopened release opened session final after := by
  intro publication released failures reads
  obtain ⟨layout, opened, session, final, after, reached⟩ :=
    ready.reopensPriorCheckpointLive publication bindings.active bindings.choices bindings.selectedRuns retry failures reads
  obtain ⟨poisoned, handoff, _⟩ := report.poisonsAndReleases ready.held release
  have preflight := attempt.preflight report.flushed report.generationFits report.runCountFits report.encoded
  exact ⟨layout, opened, session, final, after, bindings, failures,
    preflight.publicationError report.callbacks directory poisoned, handoff, reached.returned, reached.path,
    reached.descriptor, reached.phase, reached.files, reached.owners, reached.retained, reached.history, reached.wal,
    reached.durable, reached.selected, reached.checkpoint, reached.replay⟩

end ManifestStageFailureBindings

end Alvoki.Storage.DiskSession
