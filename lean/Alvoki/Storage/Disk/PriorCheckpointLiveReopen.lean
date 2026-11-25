import Alvoki.Storage.Disk.CheckpointHeldOpen
import Alvoki.Storage.Disk.SegmentedCheckpointRecovery

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

private theorem priorCheckpointAcceptance {directory : DiskDirectory} {before : SegmentedWriterState}
    (publication : Image)
    (agrees : SelectedRunsAgree before.wal.directory.active.manifest publication.durable before.published.durable)
    {writer : Nat} (ready : before.RetainedReady directory writer) :
    publication.AcceptsVersioned before.history.length.toUInt64
      (CheckpointRepresentsPrefix before.history) before.wal.directory.active.manifest := by
  have accepted := ready.resumed.accepted
  have selected := ready.resumed.selected
  rw [← ready.walPair] at accepted selected
  generalize before.wal.directory.active.manifest = binding at accepted selected agrees ⊢
  generalize before.checkpoint = checkpoint at selected
  cases selected with
  | absent => trivial
  | @present bytes metadata files table decoded stored loaded =>
    obtain ⟨payloads, exactRuns⟩ := (Image.acceptsVersioned_integrity_iff decoded).mp accepted
    exact (Image.acceptsVersioned_integrity_iff decoded).mpr ⟨payloads, exactRuns.withKeptRuns (fun index inside =>
      agrees bytes metadata rfl decoded index (exactRuns.count ▸ inside))⟩

/-- Exact admitted reopening of a live checkpoint image that still
selects the original manifest. The physical run map is retained. -/
structure PriorCheckpointReopened {directory : DiskDirectory} {before : SegmentedWriterState} {input : FilePath}
    {retry : LockedFileState FileImage} {layout : CanonicalKeeperLayout retry.image before.history}
    {publication : Image} (opened : CheckpointHeldOpen input directory layout publication)
    (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState) : Prop where
  returned : opened.wal.operations.runWithAdmission opened.admission = .ok session final
  path : session.directory = directory
  descriptor : session.descriptor = opened.calls.slot.description
  phase : session.phase = .ready after.installed
  files : after.files = final.image
  owners : after.owners = final.owners
  retained : after.RetainedReady directory opened.calls.slot.description
  history : after.history = before.history
  wal : after.wal = { before.wal with directory := after.files.directory }
  durable : after.published.durable = publication.durable
  selected : after.target.pair = before.wal.directory.active
  checkpoint : after.checkpoint = before.checkpoint
  replay : recoverSelected (before.checkpoint.getD (.empty, 0)).1 (WAL.encode before.history) = .ok after.installed.table

/-- From the released live image, the old manifest and its stable run
bytes determine the exact successful held retry. Other run names may
still have different physical crash choices. -/
theorem SegmentedWriterState.RetainedReady.reopensPriorCheckpointLiveWith
    {directory : DiskDirectory} {before : SegmentedWriterState} {input : FilePath} {writer : Nat}
    (ready : before.RetainedReady directory writer) (publication : Image)
    (manifestActive : publication.manifest.active = before.wal.directory.active.manifest)
    (manifestChoices : publication.manifest.crashImages = [before.wal.directory.active.manifest])
    (agrees : SelectedRunsAgree before.wal.directory.active.manifest publication.durable before.published.durable)
    (retry : LockedFileState FileImage)
    (evidence : ∀ {layout : CanonicalKeeperLayout retry.image before.history},
      CheckpointHeldOpen input directory layout publication → Prop) :
    let released := ⟨CheckpointPowerCut.physical before publication, before.owners.set (directory.file .lock) none⟩
    BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first) released retry →
    (∀ layout : CanonicalKeeperLayout retry.image before.history,
      layout.keeper = before.wal.active → layout.tail = ByteArray.empty →
      layout.sealed ++ [layout.keeper] =
        (publication.segmentedCheckpointView before.wal).readDescriptors layout.range.watermark →
      ∃ opened : CheckpointHeldOpen input directory layout publication, evidence opened) →
    ∃ (layout : CanonicalKeeperLayout retry.image before.history)
      (opened : CheckpointHeldOpen input directory layout publication)
      (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState),
      PriorCheckpointReopened opened session final after ∧ evidence opened := by
  intro released failures reads
  let wal := publication.segmentedCheckpointView before.wal
  have active : wal.directory.active = before.wal.directory.active := by
    change ⟨publication.manifest.active, before.wal.directory.active.walBoundary⟩ = before.wal.directory.active
    rw [manifestActive]
  have choices : wal.directory.crashImages = [before.wal.directory.active] := by
    change publication.manifest.crashImages.map
      (fun manifest => DirectoryPublication.Bindings.mk manifest before.wal.directory.active.walBoundary) = _
    rw [manifestChoices]
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
    exact ⟨priorCheckpointAcceptance publication agrees ready, before.target.range, ready.walPair.symm ▸ before.target.decoded,
      ready.resumed.through⟩
  have lineage := failures.lineage (fun a b exact => CheckpointRetryTarget.unique a b exact)
  change ReopenLineage (CheckpointPowerCut.physical before publication) _ retry.image at lineage
  rw [CheckpointPowerCut.physical_eq publication ready] at lineage
  obtain ⟨keeperLayout, chosen, keeper, tail, descriptions, offsets, prepared, _, accepted⟩ :=
    publication.checkpointRetryLayout layout valid (.visible (wal := wal)) inputs lineage
  obtain ⟨opened, observed⟩ := reads keeperLayout keeper tail descriptions
  let chunks := opened.chunkReports
  have following := chunks.selectedAfterWatermark offsets descriptions
  have installed := runOpenWithInstallation_markedRetryFromChunks chunks prepared.keeperPrefix prepared.newer following
    accepted ready.resumed.ordered
  obtain ⟨_, appendReady⟩ := installed.readyForAppend accepted ready.resumed.ordered
  have kept : retry.image.kept = (before.wal.checkpointReopenFiles before.wal.directory none).kept :=
    lineage.keepsSealed
  obtain ⟨session, final, after, returned, path, descriptor, phase, files, owners, reportedWal, target, history, durable, next⟩ :=
    appendReady.writerCheckpointRetained layout valid ready.spans chosen rfl (congrArg WalSegment.first keeper) kept
  have runtime : opened.wal.operations.runWithAdmission opened.admission = .ok session final :=
    (chunks.runWithAdmission_eq opened.admission).trans returned
  have pair : after.target.pair = before.wal.directory.active := (congrArg Target.pair target).trans
    (prepared.pair.symm.trans (selected retry.image.directory.active chosen))
  have afterCheckpoint := next.resumed.selected
  rw [durable, pair] at afterCheckpoint
  have oldSelected := ready.resumed.selected
  rw [← ready.walPair] at oldSelected
  have sameCheckpoint := (SelectedIntegrityCheckpoint.withRunMap afterCheckpoint agrees).uniqueResult oldSelected
  obtain ⟨replayed, replayCheckpoint, _, replaySession, _, returnedAgain, _, _, phaseAgain, _, _, _, _, _, _, _,
    _, _, _, chosenCheckpoint, replay, _⟩ := installed
  obtain ⟨sameSession, _⟩ := EStateM.Result.ok.inj (returnedAgain.symm.trans returned)
  have sameTable : replayed.table = after.installed.table :=
    congrArg Installed.table (Phase.ready.inj (phaseAgain.symm.trans (sameSession ▸ phase)))
  have exactReplay : replayCheckpoint = before.checkpoint := by
    have observed : retry.image.directory.active.manifest = before.wal.directory.active.manifest :=
      congrArg DirectoryPublication.Bindings.manifest (selected retry.image.directory.active chosen)
    rw [observed] at chosenCheckpoint
    exact (SelectedIntegrityCheckpoint.withRunMap chosenCheckpoint agrees).uniqueResult oldSelected
  rw [exactReplay, sameTable] at replay
  refine ⟨keeperLayout, opened, session, final, after, ⟨runtime, path,
    descriptor.trans chunks.inventoryDescription, phase, files, owners, chunks.inventoryDescription ▸ next, history, ?_,
    durable, pair, sameCheckpoint, replay⟩, observed⟩
  rw [files]
  exact reportedWal

/-- The held reopen from the reached live image preserves the old
checkpoint and the physical run map. -/
theorem SegmentedWriterState.RetainedReady.reopensPriorCheckpointLive
    {directory : DiskDirectory} {before : SegmentedWriterState} {input : FilePath} {writer : Nat}
    (ready : before.RetainedReady directory writer) (publication : Image)
    (manifestActive : publication.manifest.active = before.wal.directory.active.manifest)
    (manifestChoices : publication.manifest.crashImages = [before.wal.directory.active.manifest])
    (agrees : SelectedRunsAgree before.wal.directory.active.manifest publication.durable before.published.durable)
    (retry : LockedFileState FileImage) :
    let released := ⟨CheckpointPowerCut.physical before publication, before.owners.set (directory.file .lock) none⟩
    BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first) released retry →
    CheckpointHeldOpen.Reports input directory before retry publication publication →
    ∃ (layout : CanonicalKeeperLayout retry.image before.history)
      (opened : CheckpointHeldOpen input directory layout publication)
      (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState),
      PriorCheckpointReopened opened session final after := by
  intro released failures reads
  obtain ⟨layout, opened, session, final, after, endpoint, _⟩ :=
    ready.reopensPriorCheckpointLiveWith publication manifestActive manifestChoices agrees retry (fun _ => True)
      failures (fun layout keeper tail descriptors => by
        obtain ⟨opened⟩ := reads layout keeper tail descriptors
        exact ⟨opened, trivial⟩)
  exact ⟨layout, opened, session, final, after, endpoint⟩

end Alvoki.Storage.DiskSession
