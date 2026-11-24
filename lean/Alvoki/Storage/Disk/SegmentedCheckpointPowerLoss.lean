import Alvoki.Storage.Disk.SegmentedCheckpointRecovery
import Alvoki.Storage.Disk.WalSegmentCheckpointPowerLoss

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- Reports for a checkpoint interrupted before its current primitive
returns. The machine loss releases the old writer and selects one
durable manifest and its ordered runs. Failed opens precede the final
attempt from that surviving image. -/
structure SegmentedCheckpointPowerLossReport (directory : DiskDirectory) (before : SegmentedWriterState)
    (writer descriptor : Nat) where
  cut : CheckpointPowerCut directory before
  published : CheckpointPublication.Image
  survivingPair : DirectoryPublication.Bindings
  retry : LockedFileState FileImage
  failures : BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
    ⟨(CheckpointPowerCut.physical before published).crash survivingPair (some before.wal.active.bytes) [],
      before.owners.set (directory.file .lock) none⟩ retry
  reopen : BoundedReopenAttempt
  liveRefs : List Nat

namespace SegmentedCheckpointPowerLossReport

variable {directory : DiskDirectory} {before : SegmentedWriterState} {writer descriptor : Nat}

structure Valid (report : SegmentedCheckpointPowerLossReport directory before writer descriptor) : Prop where
  projected : before.published.executeVersioned report.cut.checkpoint.plan report.cut.checkpoint.cut =
    some report.published
  survives : report.survivingPair ∈ (report.published.segmentedCheckpointView before.wal).directory.crashImages
  reopenDescriptor : report.reopen.descriptor = descriptor
  acquired : report.reopen.acquired = .ok true
  acquisition : TryLockObserves report.retry.owners directory (.ok true)
  fresh : ∀ ref ∈ report.liveRefs, ref < report.reopen.nextRef
  reads : ∀ selected : CanonicalKeeperLayout report.retry.image before.history,
    selected.target.first = before.wal.active.first → selected.tail = ByteArray.empty →
    ∃ raw : HealthyBoundedWalReports directory (report.retry.owners.set (directory.file .lock) (some descriptor))
        descriptor (report.published.segmentedCheckpointView before.wal) report.retry.image.directory.active
        selected.range.watermark report.published.durable selected.tail,
      report.reopen.recover directory =
        raw.reopen report.reopen.removeFile report.reopen.write report.reopen.sync report.reopen.renameFile
  settles : report.reopen.sync #[directory.path] report.retry.image = .ok () report.retry.image.syncDirectory
  healthy : ∀ selected : CanonicalKeeperLayout report.retry.image before.history,
    selected.target.first = before.wal.active.first → selected.tail = ByteArray.empty →
    ∀ action prior next,
      ReachesAction selected.target report.retry.image.syncDirectory selected.plan.finishActions action prior →
      prior.effect selected.target action = some next →
      performPaths directory selected.plan report.reopen.removeFile throw report.reopen.write report.reopen.sync
        report.reopen.renameFile action prior = .ok () next

structure Installs (report : SegmentedCheckpointPowerLossReport directory before writer descriptor)
    (after : SegmentedWriterState) : Prop extends
      SegmentedCheckpointReopened directory before descriptor report.published report.retry report.reopen after where
  initialLoss : BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
    ⟨CheckpointPowerCut.physical before report.published, before.owners⟩
    ⟨(CheckpointPowerCut.physical before report.published).crash
      report.survivingPair (some before.wal.active.bytes) [], before.owners.set (directory.file .lock) none⟩
  surviving : after.target.pair = report.survivingPair
  generation : (after.installed.generation = before.installed.generation ∧
      after.target.pair.manifest = before.wal.directory.active.manifest) ∨
    (after.installed.generation = SegmentedCheckpointReport.generation before ∧
      after.target.pair.manifest = some report.cut.checkpoint.manifest)

private theorem keepsSelectedPair {origin current : FileImage} {admits : Target → Prop}
    {pair : DirectoryPublication.Bindings} (settled : origin.directory = .settled pair)
    (lineage : ReopenLineage origin admits current) : current.directory.active = pair := by
  have beforeBarrier {image : FileImage} (observed : BeforeReopenBarrier origin image) :
      image.directory.active = pair := by
    cases observed with
    | live => exact congrArg DirectoryPublication.Image.active settled
    | crash found _ _ metadata _ _ =>
      change found = pair
      rw [settled] at metadata
      exact List.mem_singleton.mp metadata
  cases lineage with
  | before observed => exact beforeBarrier observed
  | repairing observed _ prepared trace =>
    exact (trace.valid prepared.pair prepared.keeperPrefix prepared.newer).selected.trans
      (prepared.pair.symm.trans (beforeBarrier observed))

/-- Recover through any number of subsequent failed opens. The final
healthy bounded open loads exactly the surviving checkpoint and the
unchanged acknowledged history. -/
theorem installs (report : SegmentedCheckpointPowerLossReport directory before writer descriptor)
    (observed : report.Valid) (ready : before.Ready directory writer) :
    ∃ after, report.Installs after ∧ after.Ready directory descriptor := by
  obtain ⟨published, projected, layout, chain, valid, inputs, crash⟩ :=
    report.cut.selectsAcknowledgedHistory ready
  have exactPublished : published = report.published := Option.some.inj (projected.symm.trans observed.projected)
  subst published
  obtain ⟨initialLoss, _, _, _, _, _, _, _, _, _, loaded, generationChoice, _⟩ := crash observed.survives
  have failures := report.failures
  rw [CheckpointPowerCut.physical_eq report.published ready] at failures
  have observedDirectory : (report.published.segmentedCheckpointView before.wal).CheckpointReopenDirectory
      (.settled report.survivingPair) := .crash observed.survives
  obtain ⟨kept, _, selected, keeper, tail, _, _, openReady⟩ :=
    failures.installsFromCheckpointCut (descriptor := descriptor) layout valid ready.resumed.ordered
      observedDirectory inputs report.liveRefs observed.fresh observed.acquisition report.reopen.unlock
      report.reopen.removeFile report.reopen.write report.reopen.sync report.reopen.renameFile
  obtain ⟨raw, recover⟩ := observed.reads selected keeper tail
  have opened := openReady raw observed.settles (observed.healthy selected keeper tail)
  have execution : report.reopen.run directory report.retry =
      runOpenWithInstallation directory descriptor report.reopen.nextRef (.ok true) report.reopen.unlock
        (raw.reopen report.reopen.removeFile report.reopen.write report.reopen.sync report.reopen.renameFile)
        report.retry := by
    rw [BoundedReopenAttempt.run, observed.reopenDescriptor, observed.acquired, recover]
  rw [← execution] at opened
  obtain ⟨session, final, after, returned, path, lock, phase, files, owners, wal, target, history, durable, resumed⟩ :=
    opened.writerReady layout chain keeper kept
  have exactWal : after.wal = { before.wal with directory := after.files.directory } := by
    rw [wal, files]; rfl
  have targetPair : after.target.pair = report.retry.image.directory.active := by rw [target]; rfl
  have targetFirst : after.target.first = before.wal.active.first := target ▸ keeper
  have targetBytes : after.target.trimmed = before.wal.active.bytes := by
    rw [resumed.resumed.contents, history, targetFirst, ready.layout.activeBytes]
  have surviving : after.target.pair = report.survivingPair := targetPair.trans
    (keepsSelectedPair rfl (failures.lineage (fun a b pair => CheckpointRetryTarget.unique a b pair)))
  have generationRead := resumed.generationRead
  rw [surviving] at generationRead
  have generation := Except.ok.inj (generationRead.symm.trans (CheckpointPowerCut.selectedGeneration loaded))
  have decided : (after.installed.generation = before.installed.generation ∧
      after.target.pair.manifest = before.wal.directory.active.manifest) ∨
      (after.installed.generation = SegmentedCheckpointReport.generation before ∧
        after.target.pair.manifest = some report.cut.checkpoint.manifest) := by
    rw [generation, surviving]
    exact generationChoice
  exact ⟨after, ⟨⟨⟨session, final, returned, path, lock, phase, files, owners⟩,
    history, exactWal, durable, resumed.manifestFiles, targetPair, targetFirst, targetBytes,
    resumed.resumed.selected⟩, initialLoss, surviving, decided⟩, resumed⟩

theorem Installs.preservesReady {report : SegmentedCheckpointPowerLossReport directory before writer descriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after) (observed : report.Valid)
    (ready : before.Ready directory writer) : after.Ready directory descriptor := by
  obtain ⟨_, opened, next⟩ := report.installs observed ready
  exact opened.toSegmentedCheckpointReopened.unique endpoint.toSegmentedCheckpointReopened ▸ next

end SegmentedCheckpointPowerLossReport

end Alvoki.Storage.DiskSession
