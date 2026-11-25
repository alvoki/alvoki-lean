import Alvoki.Storage.Disk.CheckpointManifestStageFailure

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

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

private theorem acceptance (bindings : ManifestStageFailureBindings report manifest runs) {writer : Nat}
    (ready : before.RetainedReady directory writer) :
    (report.reachedPublication manifest runs).AcceptsVersioned before.history.length.toUInt64
      (CheckpointRepresentsPrefix before.history) before.wal.directory.active.manifest := by
  have accepted := ready.resumed.accepted
  have selected := ready.resumed.selected
  rw [← ready.walPair] at accepted selected
  have agrees := bindings.selectedRuns
  generalize before.wal.directory.active.manifest = binding at accepted selected agrees ⊢
  generalize before.checkpoint = checkpoint at selected
  cases selected with
  | absent => trivial
  | @present bytes metadata files table decoded stored loaded =>
    obtain ⟨payloads, exactRuns⟩ := (Image.acceptsVersioned_integrity_iff decoded).mp accepted
    exact (Image.acceptsVersioned_integrity_iff decoded).mpr ⟨payloads, exactRuns.withKeptRuns (fun index inside =>
      agrees bytes metadata rfl decoded index (exactRuns.count ▸ inside))⟩

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
      runPreparedCheckpoint attempt.prepared report.perform (.ready before.installed, ⟨report.atRun 0, before.owners⟩) =
        .error report.cause (.poisoned, ⟨report.reached, before.owners⟩) ∧
      release.Observed (directory := directory) (.poisoned, ⟨report.reached, before.owners⟩)
        ⟨report.reached, released.owners⟩ ∧
      opened.wal.operations.runWithAdmission opened.admission = .ok session final ∧
      session.directory = directory ∧ session.descriptor = opened.calls.slot.description ∧
      session.phase = .ready after.installed ∧ after.files = final.image ∧ after.owners = final.owners ∧
      after.RetainedReady directory session.descriptor ∧ after.history = before.history ∧
      after.published.durable = publication.durable ∧
      after.target.pair = before.wal.directory.active ∧ after.checkpoint = before.checkpoint ∧
      recoverSelected (before.checkpoint.getD (.empty, 0)).1 (WAL.encode before.history) = .ok after.installed.table := by
  intro publication released failures reads
  let wal := publication.segmentedCheckpointView before.wal
  have active : wal.directory.active = before.wal.directory.active := by
    change ⟨(manifest report.reached).active, before.wal.directory.active.walBoundary⟩ = before.wal.directory.active
    rw [bindings.active]
  have choices : wal.directory.crashImages = [before.wal.directory.active] := by
    change (manifest report.reached).crashImages.map
      (fun manifest => DirectoryPublication.Bindings.mk manifest before.wal.directory.active.walBoundary) = _
    rw [bindings.choices]
    rfl
  have selected (pair : DirectoryPublication.Bindings) (found : wal.Selects pair) : pair = before.wal.directory.active := by
    simpa [WalSegmentImage.Selects, active, choices] using found
  obtain ⟨layout, valid⟩ := Image.segmentedCheckpointView_retained (published := publication) ready.layout ready.valid
    (fun pair found => .inl (selected pair found))
  have inputs : ∀ pair, wal.Selects pair →
      publication.AcceptsVersioned before.history.length.toUInt64 (CheckpointRepresentsPrefix before.history) pair.manifest ∧
      ∃ range, pair.walRange = some range ∧ range.through = before.history.length := by
    intro pair found
    rw [selected pair found]
    exact ⟨bindings.acceptance ready, before.target.range, ready.walPair.symm ▸ before.target.decoded,
      ready.resumed.through⟩
  have lineage := failures.lineage (fun a b exact => CheckpointRetryTarget.unique a b exact)
  change ReopenLineage (CheckpointPowerCut.physical before publication) _ retry.image at lineage
  rw [CheckpointPowerCut.physical_eq publication ready] at lineage
  obtain ⟨keeperLayout, chosen, keeper, tail, descriptions, offsets, prepared, _, accepted⟩ :=
    publication.checkpointRetryLayout layout valid (.visible (wal := wal)) inputs lineage
  obtain ⟨opened⟩ := reads keeperLayout keeper tail descriptions
  let chunks := opened.chunkReports
  have following := chunks.selectedAfterWatermark offsets descriptions
  have installed := runOpenWithInstallation_markedRetryFromChunks chunks prepared.keeperPrefix prepared.newer following
    accepted ready.resumed.ordered
  obtain ⟨_, appendReady⟩ := installed.readyForAppend accepted ready.resumed.ordered
  have kept : retry.image.kept = (before.wal.checkpointReopenFiles before.wal.directory none).kept :=
    lineage.keepsSealed
  obtain ⟨session, final, after, returned, path, descriptor, phase, files, owners, _, target, history, durable, next⟩ :=
    appendReady.writerCheckpointRetained layout valid ready.spans chosen rfl (congrArg WalSegment.first keeper) kept
  have runtime : opened.wal.operations.runWithAdmission opened.admission = .ok session final :=
    (chunks.runWithAdmission_eq opened.admission).trans returned
  have pair : after.target.pair = before.wal.directory.active := (congrArg Target.pair target).trans
    (prepared.pair.symm.trans (selected retry.image.directory.active chosen))
  have afterCheckpoint := next.resumed.selected
  rw [durable, pair] at afterCheckpoint
  have oldSelected := ready.resumed.selected
  rw [← ready.walPair] at oldSelected
  have sameCheckpoint := (SelectedIntegrityCheckpoint.withRunMap afterCheckpoint bindings.selectedRuns).uniqueResult oldSelected
  obtain ⟨replayed, replayCheckpoint, _, replaySession, _, returnedAgain, _, _, phaseAgain, _, _, _, _, _, _, _,
    _, _, _, chosenCheckpoint, replay, _⟩ := installed
  obtain ⟨sameSession, _⟩ := EStateM.Result.ok.inj (returnedAgain.symm.trans returned)
  have sameTable : replayed.table = after.installed.table :=
    congrArg Installed.table (Phase.ready.inj (phaseAgain.symm.trans (sameSession ▸ phase)))
  have exactReplay : replayCheckpoint = before.checkpoint := by
    have observed : retry.image.directory.active.manifest = before.wal.directory.active.manifest :=
      congrArg DirectoryPublication.Bindings.manifest (selected retry.image.directory.active chosen)
    rw [observed] at chosenCheckpoint
    exact (SelectedIntegrityCheckpoint.withRunMap chosenCheckpoint bindings.selectedRuns).uniqueResult oldSelected
  rw [exactReplay, sameTable] at replay
  obtain ⟨poisoned, handoff, _⟩ := report.poisonsAndReleases ready.held release
  exact ⟨keeperLayout, opened, session, final, after, poisoned, handoff, runtime, path,
    descriptor.trans chunks.inventoryDescription, phase, files, owners, descriptor ▸ next, history, durable,
    pair, sameCheckpoint, replay⟩

end ManifestStageFailureBindings

end Alvoki.Storage.DiskSession
