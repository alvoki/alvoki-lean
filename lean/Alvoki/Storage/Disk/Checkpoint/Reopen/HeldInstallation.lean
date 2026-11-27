import Alvoki.Storage.Disk.CheckpointHeldOpen
import Alvoki.Storage.Disk.Proofs.Recovery.SegmentedCheckpointRecovery

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

theorem SelectedRunsAgree.acceptsVersioned {logical actual : Image} {history : List WAL.Write}
    {pair : DirectoryPublication.Bindings} {range : MarkedWalRange}
    (agrees : SelectedRunsAgree pair.manifest actual.durable logical.durable) (decoded : pair.walRange = some range)
    (accepts : logical.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history) pair.manifest) :
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

theorem Image.selectedManifest {publication : Image} {wal : WalSegmentImage} {pair : DirectoryPublication.Bindings}
    (selected : (publication.segmentedCheckpointView wal).Selects pair) :
    pair.manifest = publication.manifest.active ∨ pair.manifest ∈ publication.manifest.crashImages := by
  rcases List.mem_cons.mp selected with live | survived
  · exact .inl (congrArg DirectoryPublication.Bindings.manifest live)
  · obtain ⟨binding, included, rfl⟩ := List.mem_map.mp survived
    exact .inr included

/-- Use the reported selected manifest and retained WAL to choose the
retry layout, then return the session installed by the same held open. -/
theorem CheckpointHeldOpen.installsAfterRetry {directory : DiskDirectory} {before : SegmentedWriterState}
    {writer : Nat} {input : FilePath} (ready : before.RetainedReady directory writer) (publication : Image)
    (layout : (publication.segmentedCheckpointView before.wal).ReadLayout before.history)
    (valid : (publication.segmentedCheckpointView before.wal).Valid before.history)
    (inputs : ∀ pair, (publication.segmentedCheckpointView before.wal).Selects pair →
      publication.AcceptsVersioned before.history.length.toUInt64 (CheckpointRepresentsPrefix before.history) pair.manifest ∧
      ∃ range, pair.walRange = some range ∧ range.through = before.history.length)
    (retry : LockedFileState FileImage)
    (attempts : BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
      ⟨CheckpointPowerCut.physical before publication, before.owners.set (directory.file .lock) none⟩ retry)
    (evidence : ∀ {layout : CanonicalKeeperLayout retry.image before.history},
      CheckpointHeldOpen input directory layout publication → Prop)
    (reads : ∀ layout : CanonicalKeeperLayout retry.image before.history,
      layout.keeper = before.wal.active → layout.tail = ByteArray.empty →
      layout.sealed ++ [layout.keeper] =
        (publication.segmentedCheckpointView before.wal).readDescriptors layout.range.watermark →
      ∃ opened : CheckpointHeldOpen input directory layout publication, evidence opened) :
    ∃ (layout : CanonicalKeeperLayout retry.image before.history)
      (opened : CheckpointHeldOpen input directory layout publication)
      (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState),
      CheckpointLiveHeldReopened opened session final after ∧ evidence opened := by
  let wal := publication.segmentedCheckpointView before.wal
  have lineage : ReopenLineage (CheckpointPowerCut.physical before publication) _ retry.image :=
    attempts.lineage CheckpointRetryTarget.unique
  rw [CheckpointPowerCut.physical_eq publication ready] at lineage
  obtain ⟨keeperLayout, chosen, keeper, tail, descriptions, offsets, prepared, _, accepted⟩ :=
    publication.checkpointRetryLayout layout valid (.visible (wal := wal)) inputs lineage
  obtain ⟨opened, observed⟩ := reads keeperLayout keeper tail descriptions
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
  obtain ⟨replayed, _, _, _, _, returnedAgain, _, _, phaseAgain, _, _, _, _, _, _, _, _, _, _,
    chosenCheckpoint, replay, _⟩ := installed
  obtain ⟨sameSession, _⟩ := EStateM.Result.ok.inj (returnedAgain.symm.trans returned)
  have sameTable : replayed.table = after.installed.table :=
    congrArg Installed.table (Phase.ready.inj (phaseAgain.symm.trans (sameSession ▸ phase)))
  rw [chosenCheckpoint.uniqueResult selectedCheckpoint, sameTable] at replay
  refine ⟨keeperLayout, opened, session, final, after, ⟨runtime, path,
    descriptor.trans chunks.inventoryDescription, phase, files, owners, chunks.inventoryDescription ▸ next,
    history, ?_, durable, pair, finalPair, chosen, selectedCheckpoint, Image.selectedManifest chosen, replay⟩, observed⟩
  simpa only [files] using reportedWal

end Alvoki.Storage.DiskSession
