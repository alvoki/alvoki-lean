import Alvoki.Storage.Disk.CheckpointManifestDirectoryFailure

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

namespace ObservedManifestDirectoryFailure

variable {directory : DiskDirectory} {before : SegmentedWriterState} {cut : CheckpointPowerCut directory before}

private theorem acceptsPhysicalRuns {logical actual : Image} {history : List WAL.Write}
    {pair : DirectoryPublication.Bindings} {range : MarkedWalRange} (decoded : pair.walRange = some range)
    (accepts : logical.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history) pair.manifest)
    (agrees : SelectedRunsAgree pair.manifest actual.durable logical.durable) :
    actual.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history) pair.manifest := by
  cases found : pair.manifest with
  | none => trivial
  | some bytes =>
    have watermark := (DirectoryPublication.Bindings.walRange_accounting decoded).1
    rw [found] at watermark
    obtain ⟨metadata, parsed, _⟩ := selectedCheckpointWatermark_present_iff.mp watermark
    obtain ⟨files, stored⟩ := (Image.acceptsVersioned_integrity_iff parsed).mp (found ▸ accepts)
    exact (Image.acceptsVersioned_integrity_iff parsed).mpr ⟨files, stored.withKeptRuns (fun index within =>
      agrees bytes metadata found parsed index (stored.count ▸ within))⟩

/-- The successful admitted open of the exact image left by the returned
manifest-directory error. It retains the chosen physical checkpoint, the
replay of the same WAL, and the actual ready session and writer. -/
structure Reopened (report : ObservedManifestDirectoryFailure cut) {writer : Nat} {input : FilePath}
    {retry : LockedFileState FileImage} {layout : CanonicalKeeperLayout retry.image before.history}
    (released : SegmentedFailureRelease writer) (opened : CheckpointHeldOpen input directory layout report.publication)
    (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState) : Prop where
  poisoned : runPreparedCheckpoint cut.checkpoint.prepared (report.calls.perform cut)
      (.ready before.installed, ⟨report.atRun 0, before.owners⟩) =
    .error report.error (.poisoned, ⟨report.after, before.owners⟩)
  handoff : released.Observed (directory := directory) (.poisoned, ⟨report.after, before.owners⟩)
    ⟨report.after, before.owners.set (directory.file .lock) none⟩
  attempts : BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
    ⟨CheckpointPowerCut.physical before report.publication, before.owners.set (directory.file .lock) none⟩ retry
  returned : opened.wal.operations.runWithAdmission opened.admission = .ok session final
  path : session.directory = directory
  slot : session.descriptor = opened.calls.slot.description
  phase : session.phase = .ready after.installed
  files : after.files = final.image
  owners : after.owners = final.owners
  ready : after.RetainedReady directory opened.calls.slot.description
  history : after.history = before.history
  wal : after.wal = { before.wal with directory := after.files.directory }
  durable : after.published.durable = report.publication.durable
  pair : after.target.pair = retry.image.directory.active
  finalPair : final.image.directory.active = retry.image.directory.active
  admitted : (report.publication.segmentedCheckpointView before.wal).Selects retry.image.directory.active
  checkpoint : SelectedIntegrityCheckpoint report.publication.durable retry.image.directory.active.manifest after.checkpoint
  choice : retry.image.directory.active.manifest = some cut.checkpoint.manifest ∨
    (cut.tookEffect = false ∧ retry.image.directory.active.manifest = before.wal.directory.active.manifest)
  replay : recoverSelected (after.checkpoint.getD (.empty, 0)).1 (WAL.encode before.history) = .ok after.installed.table

/-- With the newly renamed manifest live, a returned final sync error
hands the exact reached files to the bounded retry. A later crash before
repair authorization may select the old manifest only if the final sync
had left that binding possible. Both choices use the same physical run
map and preserve the acknowledged history. -/
theorem reopens (report : ObservedManifestDirectoryFailure cut) {writer : Nat} {input : FilePath}
    (ready : before.RetainedReady directory writer) (release : SegmentedFailureRelease writer)
    (retry : LockedFileState FileImage) :
    let publication := report.publication
    let released := ⟨CheckpointPowerCut.physical before publication, before.owners.set (directory.file .lock) none⟩
    BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first) released retry →
    CheckpointHeldOpen.Reports input directory before retry publication publication →
    ∃ (layout : CanonicalKeeperLayout retry.image before.history)
      (opened : CheckpointHeldOpen input directory layout publication)
      (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState),
      report.Reopened release opened session final after := by
  intro publication released attempts reads
  obtain ⟨_, _, _, _, logical, observed⟩ := cut.atManifestDirectory ready report.calls report.atRun report.runs
    report.runPrefix report.reached report.completed
  let wal := publication.segmentedCheckpointView before.wal
  let modelWal := logical.segmentedCheckpointView before.wal
  have active : wal.directory.active = modelWal.directory.active := by
    change ⟨report.publication.manifest.active, before.wal.directory.active.walBoundary⟩ =
      (⟨logical.manifest.active, before.wal.directory.active.walBoundary⟩ : DirectoryPublication.Bindings)
    rw [report.liveManifest, observed.liveManifest]
  have modeled (pair : DirectoryPublication.Bindings) (found : wal.Selects pair) : modelWal.Selects pair := by
    rcases List.mem_cons.mp found with visible | survivors
    · exact List.mem_cons.mpr (.inl (visible.trans active))
    · change pair ∈ report.publication.manifest.crashImages.map
        (fun manifest => DirectoryPublication.Bindings.mk manifest before.wal.directory.active.walBoundary) at survivors
      obtain ⟨binding, included, rfl⟩ := List.mem_map.mp survivors
      exact List.mem_cons.mpr (.inr (List.mem_map.mpr ⟨binding, observed.admitted binding included, rfl⟩))
  have choice (pair : DirectoryPublication.Bindings) (found : modelWal.Selects pair) :
      pair.manifest = some cut.checkpoint.manifest ∨
        (cut.tookEffect = false ∧ pair.manifest = before.wal.directory.active.manifest) := by
    rcases List.mem_cons.mp found with visible | survived
    · rw [visible]
      exact .inl observed.liveManifest
    · change pair ∈ logical.manifest.crashImages.map
        (fun manifest => DirectoryPublication.Bindings.mk manifest before.wal.directory.active.walBoundary) at survived
      obtain ⟨binding, included, rfl⟩ := List.mem_map.mp survived
      rw [observed.manifestChoices] at included
      cases took : cut.tookEffect <;> simp_all
  obtain ⟨published, executed, layoutModel, validModel, inputsModel, _⟩ := cut.selectsAcknowledgedHistory ready
  have same := Option.some.inj (executed.symm.trans observed.executed)
  subst published
  have layout : wal.ReadLayout before.history :=
    ⟨layoutModel.ordered, layoutModel.forward, layoutModel.activeEnd, layoutModel.activeBytes⟩
  have valid : wal.Valid before.history := fun pair found => validModel pair (modeled pair found)
  have inputs : ∀ pair, wal.Selects pair →
      publication.AcceptsVersioned before.history.length.toUInt64 (CheckpointRepresentsPrefix before.history) pair.manifest ∧
      ∃ range, pair.walRange = some range ∧ range.through = before.history.length := by
    intro pair found
    have admitted := modeled pair found
    obtain ⟨accepted, range, decoded, through⟩ := inputsModel pair admitted
    have origin : pair.manifest = before.wal.directory.active.manifest ∨ pair.manifest = some cut.checkpoint.manifest :=
      (choice pair admitted).elim Or.inr (fun ⟨_, old⟩ => Or.inl old)
    have agrees := cut.selectedRunAgreement ready logical pair.manifest origin publication.durable
      observed.newRuns observed.priorRuns
    exact ⟨acceptsPhysicalRuns decoded accepted agrees, range, decoded, through⟩
  have lineage := attempts.lineage (fun a b exact => CheckpointRetryTarget.unique a b exact)
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
  have kept : retry.image.kept = (before.wal.checkpointReopenFiles before.wal.directory none).kept := lineage.keepsSealed
  obtain ⟨session, final, after, returned, path, descriptor, phase, files, owners, reportedWal, target, history, durable, next⟩ :=
    appendReady.writerCheckpointRetained layout valid ready.spans chosen rfl (congrArg WalSegment.first keeper) kept
  have runtime : opened.wal.operations.runWithAdmission opened.admission = .ok session final :=
    (chunks.runWithAdmission_eq opened.admission).trans returned
  have pair : after.target.pair = retry.image.directory.active := (congrArg Target.pair target).trans prepared.pair.symm
  have finalPair : final.image.directory.active = retry.image.directory.active :=
    (congrArg (fun image : FileImage => image.directory.active) files.symm).trans (next.resumed.ready.selected.trans pair)
  have selectedCheckpoint := next.resumed.selected
  rw [durable, pair] at selectedCheckpoint
  obtain ⟨replayed, _, _, replaySession, _, returnedAgain, _, _, phaseAgain, _, _, _, _, _, _, _, _, _, _,
    chosenCheckpoint, replay, _⟩ := installed
  obtain ⟨sameSession, _⟩ := EStateM.Result.ok.inj (returnedAgain.symm.trans returned)
  have sameTable : replayed.table = after.installed.table :=
    congrArg Installed.table (Phase.ready.inj (phaseAgain.symm.trans (sameSession ▸ phase)))
  rw [chosenCheckpoint.uniqueResult selectedCheckpoint, sameTable] at replay
  obtain ⟨poisoned, handoff, _⟩ := report.poisonsAndReleases ready release
  refine ⟨keeperLayout, opened, session, final, after, poisoned, handoff, attempts, runtime, path,
    descriptor.trans chunks.inventoryDescription, phase, files, owners, chunks.inventoryDescription ▸ next,
    history, ?_, durable, pair, finalPair, chosen, selectedCheckpoint, choice _ (modeled _ chosen), replay⟩
  rw [files]
  exact reportedWal

end ObservedManifestDirectoryFailure

end Alvoki.Storage.DiskSession
