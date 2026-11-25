import Alvoki.Storage.Disk.CheckpointHeldOpen
import Alvoki.Storage.Disk.SegmentedCheckpointRecovery

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

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

/-- A held reopen from a live checkpoint failure uses the actual physical
publication and retains its exact admitted session and writer. -/
structure CheckpointLiveHeldReopened {directory : DiskDirectory} {before : SegmentedWriterState} {input : FilePath}
    {publication : Image} {retry : LockedFileState FileImage} {layout : CanonicalKeeperLayout retry.image before.history}
    (opened : CheckpointHeldOpen input directory layout publication)
    (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState) : Prop where
  returned : opened.wal.operations.runWithAdmission opened.admission = .ok session final
  path : session.directory = directory
  slot : session.descriptor = opened.calls.slot.description
  phase : session.phase = .ready after.installed
  files : after.files = final.image
  owners : after.owners = final.owners
  ready : after.RetainedReady directory opened.calls.slot.description
  history : after.history = before.history
  wal : after.wal = { before.wal with directory := after.files.directory }
  durable : after.published.durable = publication.durable
  pair : after.target.pair = retry.image.directory.active
  finalPair : final.image.directory.active = retry.image.directory.active
  admitted : (publication.segmentedCheckpointView before.wal).Selects retry.image.directory.active
  checkpoint : SelectedIntegrityCheckpoint publication.durable retry.image.directory.active.manifest after.checkpoint
  selectedManifest : retry.image.directory.active.manifest = publication.manifest.active ∨
    retry.image.directory.active.manifest ∈ publication.manifest.crashImages
  replay : recoverSelected (after.checkpoint.getD (.empty, 0)).1 (WAL.encode before.history) = .ok after.installed.table

/-- Transfer the proved checkpoint's accepted metadata and WAL read plan to
its reported live image. The active manifest is identical, every physical
crash choice is modeled, and selected indices agree on the actual bytes. -/
theorem CheckpointPowerCut.reopensFromLive {directory : DiskDirectory} {before : SegmentedWriterState}
    {writer : Nat} {input : FilePath} (cut : CheckpointPowerCut directory before)
    (ready : before.RetainedReady directory writer) (logical publication : Image)
    (projected : before.published.executeVersioned cut.checkpoint.plan cut.checkpoint.cut = some logical)
    (live : publication.manifest.active = logical.manifest.active)
    (choices : ∀ binding ∈ publication.manifest.crashImages, binding ∈ logical.manifest.crashImages)
    (agrees : ∀ binding, (binding = publication.manifest.active ∨ binding ∈ publication.manifest.crashImages) →
      SelectedRunsAgree binding publication.durable logical.durable)
    (retry : LockedFileState FileImage)
    (attempts : BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
      ⟨CheckpointPowerCut.physical before publication, before.owners.set (directory.file .lock) none⟩ retry)
    (reads : CheckpointHeldOpen.Reports input directory before retry publication publication) :
    ∃ (layout : CanonicalKeeperLayout retry.image before.history)
      (opened : CheckpointHeldOpen input directory layout publication)
      (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState),
      CheckpointLiveHeldReopened opened session final after := by
  let wal := publication.segmentedCheckpointView before.wal
  let modelWal := logical.segmentedCheckpointView before.wal
  have active : wal.directory.active = modelWal.directory.active :=
    congrArg (fun manifest => DirectoryPublication.Bindings.mk manifest before.wal.directory.active.walBoundary) live
  have modeled (pair : DirectoryPublication.Bindings) (found : wal.Selects pair) :
      modelWal.Selects pair ∧ (pair.manifest = publication.manifest.active ∨ pair.manifest ∈ publication.manifest.crashImages) := by
    rcases List.mem_cons.mp found with visible | survived
    · exact ⟨List.mem_cons.mpr (.inl (visible.trans active)), .inl (congrArg DirectoryPublication.Bindings.manifest visible)⟩
    · change pair ∈ publication.manifest.crashImages.map
        (fun manifest => DirectoryPublication.Bindings.mk manifest before.wal.directory.active.walBoundary) at survived
      obtain ⟨binding, included, rfl⟩ := List.mem_map.mp survived
      exact ⟨List.mem_cons.mpr (.inr (List.mem_map.mpr ⟨binding, choices binding included, rfl⟩)), .inr included⟩
  obtain ⟨published, executed, layoutModel, validModel, inputsModel, _⟩ := cut.selectsAcknowledgedHistory ready
  have same := Option.some.inj (executed.symm.trans projected)
  subst published
  have layout : wal.ReadLayout before.history :=
    ⟨layoutModel.ordered, layoutModel.forward, layoutModel.activeEnd, layoutModel.activeBytes⟩
  have valid : wal.Valid before.history := fun pair found => validModel pair (modeled pair found).1
  have inputs : ∀ pair, wal.Selects pair →
      publication.AcceptsVersioned before.history.length.toUInt64 (CheckpointRepresentsPrefix before.history) pair.manifest ∧
      ∃ range, pair.walRange = some range ∧ range.through = before.history.length := by
    intro pair found
    have admitted := (modeled pair found).1
    obtain ⟨accepted, range, decoded, through⟩ := inputsModel pair admitted
    exact ⟨acceptsPhysicalRuns decoded accepted (agrees pair.manifest (modeled pair found).2), range, decoded, through⟩
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
  refine ⟨keeperLayout, opened, session, final, after, runtime, path,
    descriptor.trans chunks.inventoryDescription, phase, files, owners, chunks.inventoryDescription ▸ next,
    history, ?_, durable, pair, finalPair, chosen, selectedCheckpoint, (modeled _ chosen).2, replay⟩
  rw [files]
  exact reportedWal

end Alvoki.Storage.DiskSession
