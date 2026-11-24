import Alvoki.Storage.Disk.SegmentedCheckpointRecovery
import Alvoki.Storage.Disk.WalSegmentCachedExtentReports
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

/-- A retry and every admitted crash keep the binding of an already settled directory. -/
theorem keepsSelectedPair {origin current : FileImage} {admits : Target → Prop}
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

private theorem installsRetained_exact (report : SegmentedCheckpointPowerLossReport directory before writer descriptor)
    (observed : report.Valid) (ready : before.RetainedReady directory writer) :
    ∃ after, report.Installs after ∧ after.RetainedReady directory descriptor ∧
      recoverSelected (after.checkpoint.getD (.empty, 0)).1 (WAL.encode before.history) = .ok after.installed.table := by
  obtain ⟨published, projected, layout, valid, inputs, crash⟩ :=
    report.cut.selectsAcknowledgedHistory ready
  have exactPublished : published = report.published := Option.some.inj (projected.symm.trans observed.projected)
  subst published
  obtain ⟨initialLoss, _, _, _, _, _, _, _, _, _, loaded, generationChoice, _⟩ := crash observed.survives
  have failures := report.failures
  rw [CheckpointPowerCut.physical_eq report.published ready] at failures
  have observedDirectory : (report.published.segmentedCheckpointView before.wal).CheckpointReopenDirectory
      (.settled report.survivingPair) := .crash observed.survives
  obtain ⟨kept, chosen, selected, keeper, tail, _, _, openReady⟩ :=
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
    opened.writerCheckpointRetained layout valid ready.spans chosen rfl keeper kept
  have exactWal : after.wal = { before.wal with directory := after.files.directory } := by
    rw [wal, files]
  have targetPair : after.target.pair = report.retry.image.directory.active := by rw [target]; rfl
  have targetFirst : after.target.first = before.wal.active.first := target ▸ keeper
  have targetBytes : after.target.trimmed = before.wal.active.bytes := by
    rw [resumed.resumed.contents, history, targetFirst, ready.layout.activeBytes]
  have surviving : after.target.pair = report.survivingPair := targetPair.trans
    (keepsSelectedPair rfl (failures.lineage (fun a b pair => CheckpointRetryTarget.unique a b pair)))
  have generationRead := CheckpointPowerCut.selectedGeneration resumed.resumed.selected
  rw [← resumed.resumed.generation, surviving] at generationRead
  have generation := Except.ok.inj (generationRead.symm.trans (CheckpointPowerCut.selectedGeneration loaded))
  have decided : (after.installed.generation = before.installed.generation ∧
      after.target.pair.manifest = before.wal.directory.active.manifest) ∨
      (after.installed.generation = SegmentedCheckpointReport.generation before ∧
        after.target.pair.manifest = some report.cut.checkpoint.manifest) := by
    rw [generation, surviving]
    exact generationChoice
  obtain ⟨_, _, _, _, checkpoint, table, _, replaySession, replayFinal, replayResult, selectedRuns, _, replay, _, _,
    replayPhase, _⟩ := opened
  have sameSession := (EStateM.Result.ok.inj (replayResult.symm.trans returned)).1
  rw [sameSession] at replayPhase
  have sameTable : table = after.installed.table :=
    congrArg Installed.table (Phase.ready.inj (replayPhase.symm.trans phase))
  have selectedAfter := resumed.resumed.selected
  rw [durable, target] at selectedAfter
  have sameCheckpoint := Except.ok.inj ((raw.readCheckpoint selectedRuns).symm.trans (raw.readCheckpoint selectedAfter))
  have exactReplay : recoverSelected (after.checkpoint.getD (.empty, 0)).1 (WAL.encode before.history) =
      .ok after.installed.table := by
    rwa [sameCheckpoint, sameTable] at replay
  exact ⟨after, ⟨⟨⟨session, final, returned, path, lock, phase, files, owners⟩,
    history, exactWal, durable, resumed.manifestFiles, targetPair, targetFirst, targetBytes,
    resumed.resumed.selected⟩, initialLoss, surviving, decided⟩, resumed, exactReplay⟩

/-- Recover through any number of subsequent failed opens. The final
healthy bounded open loads exactly the surviving checkpoint and the
unchanged acknowledged history. -/
theorem installsRetained (report : SegmentedCheckpointPowerLossReport directory before writer descriptor)
    (observed : report.Valid) (ready : before.RetainedReady directory writer) :
    ∃ after, report.Installs after ∧ after.RetainedReady directory descriptor := by
  obtain ⟨after, installed, next, _⟩ := report.installsRetained_exact observed ready
  exact ⟨after, installed, next⟩

/-- Both workers use the held inventory at the reached retry. The cached
worker reads just the run and WAL prefixes selected by that inventory. -/
def CachedReads (report : SegmentedCheckpointPowerLossReport directory before writer descriptor)
    (recover : EStateM IO.Error FileImage Reopened) : Prop :=
  ∀ selected : CanonicalKeeperLayout report.retry.image before.history,
    selected.target.first = before.wal.active.first → selected.tail = ByteArray.empty →
    let wal := report.published.segmentedCheckpointView before.wal
    ∃ raw : HealthyBoundedWalReports directory (report.retry.owners.set (directory.file .lock) (some descriptor))
        descriptor wal report.retry.image.directory.active selected.range.watermark report.published.durable selected.tail,
      ∃ sizes : SizedCheckpointRunReports directory raw.reports report.retry.image.directory.active.manifest
          report.published.durable,
        ∃ cached : CachedWalFileReports directory raw.reports wal selected.range.watermark selected.tail,
          report.reopen.recover directory = raw.reopen report.reopen.removeFile report.reopen.write report.reopen.sync
            report.reopen.renameFile ∧
          recover = raw.reopenCached sizes cached report.reopen.removeFile report.reopen.write report.reopen.sync
            report.reopen.renameFile

/-- Recover through the cached opener from the exact previous or next
manifest that survived the publication cut. Its durable run files select
the installed checkpoint, and WAL replay preserves the acknowledged history. -/
theorem installsRetainedCached (report : SegmentedCheckpointPowerLossReport directory before writer descriptor)
    (observed : report.Valid) (ready : before.RetainedReady directory writer)
    (recover : EStateM IO.Error FileImage Reopened) (reads : report.CachedReads recover) :
    ∃ after session final,
      report.Installs after ∧ after.RetainedReady directory descriptor ∧
      SelectedIntegrityCheckpoint report.published.durable report.survivingPair.manifest after.checkpoint ∧
      recoverSelected (after.checkpoint.getD (.empty, 0)).1 (WAL.encode before.history) = .ok after.installed.table ∧
      runOpenWithInstallation directory report.reopen.descriptor report.reopen.nextRef report.reopen.acquired
        report.reopen.unlock recover report.retry = .ok session final ∧
      session.phase = .ready after.installed ∧ after.files = final.image ∧ after.owners = final.owners := by
  obtain ⟨published, projected, layout, valid, inputs, crash⟩ := report.cut.selectsAcknowledgedHistory ready
  have exactPublished : published = report.published := Option.some.inj (projected.symm.trans observed.projected)
  subst published
  obtain ⟨_, _, _, _, _, _, _, _, _, _, checkpoint, _, _⟩ := crash observed.survives
  have failures := report.failures
  rw [CheckpointPowerCut.physical_eq report.published ready] at failures
  have lineage := failures.lineage (fun a b pair => CheckpointRetryTarget.unique a b pair)
  have observedDirectory : (report.published.segmentedCheckpointView before.wal).CheckpointReopenDirectory
      (.settled report.survivingPair) := .crash observed.survives
  obtain ⟨selected, chosen, keeper, noTail, _, _, _, _, _⟩ :=
    report.published.checkpointRetryLayout layout valid observedDirectory inputs lineage
  obtain ⟨raw, sizes, cached, boundedRead, cachedRead⟩ := reads selected (congrArg WalSegment.first keeper) noTail
  have surviving : report.retry.image.directory.active = report.survivingPair := keepsSelectedPair rfl lineage
  rw [← surviving] at checkpoint
  have sameAction := cachedRead.trans ((raw.reopenCached_eq sizes cached layout valid chosen selected.decoded rfl
    selected.through checkpoint report.reopen.removeFile report.reopen.write report.reopen.sync
    report.reopen.renameFile).trans boundedRead.symm)
  obtain ⟨after, installed, next, replay⟩ := report.installsRetained_exact observed ready
  obtain ⟨session, final, returned, _, _, phase, files, owners⟩ := installed.reopened
  have actual : runOpenWithInstallation directory report.reopen.descriptor report.reopen.nextRef report.reopen.acquired
      report.reopen.unlock recover report.retry = .ok session final := by
    rw [sameAction]
    exact returned
  have selectedCheckpoint := installed.checkpoint
  rw [installed.durable, installed.surviving] at selectedCheckpoint
  exact ⟨after, session, final, installed, next, selectedCheckpoint, replay, actual, phase, files, owners⟩

/-- Existing full-history writers retain their stronger chain witness
across the same crash and recovery. -/
theorem installs (report : SegmentedCheckpointPowerLossReport directory before writer descriptor)
    (observed : report.Valid) (ready : before.Ready directory writer) :
    ∃ after, report.Installs after ∧ after.Ready directory descriptor := by
  obtain ⟨after, endpoint, retained⟩ := report.installsRetained observed ready.toRetained
  have chain : WalSegment.Chain after.history 0 after.wal.segments := by
    rw [endpoint.history, endpoint.wal]
    exact ready.chain
  exact ⟨after, endpoint, ⟨retained.resumed, retained.layout, chain, retained.directoryFiles,
    retained.sealedFiles, retained.active, retained.manifestFiles, retained.held⟩⟩

theorem Installs.preservesRetained {report : SegmentedCheckpointPowerLossReport directory before writer descriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after) (observed : report.Valid)
    (ready : before.RetainedReady directory writer) : after.RetainedReady directory descriptor := by
  obtain ⟨_, opened, next⟩ := report.installsRetained observed ready
  exact opened.toSegmentedCheckpointReopened.unique endpoint.toSegmentedCheckpointReopened ▸ next

theorem Installs.preservesReady {report : SegmentedCheckpointPowerLossReport directory before writer descriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after) (observed : report.Valid)
    (ready : before.Ready directory writer) : after.Ready directory descriptor := by
  obtain ⟨_, opened, next⟩ := report.installs observed ready
  exact opened.toSegmentedCheckpointReopened.unique endpoint.toSegmentedCheckpointReopened ▸ next

end SegmentedCheckpointPowerLossReport

end Alvoki.Storage.DiskSession
