import Alvoki.Storage.Disk.Proofs.Checkpoint.Reopen.HeldInstallation

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

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
    have accepted := ready.resumed.accepted
    rw [← ready.walPair] at accepted
    have decoded : before.wal.directory.active.walRange = some before.target.range :=
      ready.walPair.symm ▸ before.target.decoded
    exact ⟨agrees.acceptsVersioned decoded accepted, before.target.range, decoded, ready.resumed.through⟩
  obtain ⟨keeperLayout, opened, session, final, after, installed, observed⟩ :=
    CheckpointHeldOpen.installsAfterRetry ready publication layout valid inputs retry failures evidence reads
  have selectedPair := selected retry.image.directory.active installed.admitted
  have physical := installed.checkpoint
  rw [congrArg DirectoryPublication.Bindings.manifest selectedPair] at physical
  have oldSelected := ready.resumed.selected
  rw [← ready.walPair] at oldSelected
  have sameCheckpoint := (SelectedIntegrityCheckpoint.withRunMap physical agrees).uniqueResult oldSelected
  refine ⟨keeperLayout, opened, session, final, after, ⟨installed.returned, installed.path, installed.slot,
    installed.phase, installed.files, installed.owners, installed.ready, installed.history, installed.wal,
    installed.durable, installed.pair.trans selectedPair, sameCheckpoint, ?_⟩, observed⟩
  simpa only [sameCheckpoint] using installed.replay

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
