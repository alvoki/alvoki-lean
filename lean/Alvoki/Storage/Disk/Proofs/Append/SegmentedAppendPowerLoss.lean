import Alvoki.Storage.Disk.Proofs.Append.WalSegmentAppendPowerLoss
import Alvoki.Storage.Disk.Proofs.WAL.WalSegmentCachedExtentReports

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open WAL (frameSize)

/-- The submitted write and physical observations for power loss before
the append callback returns. The retry receives exactly the surviving
keeper and the old manifest and marker. -/
structure SegmentedAppendPowerLossReport (directory : DiskDirectory) (before : SegmentedWriterState)
    (oldDescriptor nextDescriptor : Nat) where
  event : WAL.Write
  table : PackedTable
  activeMetadata : FilePath → Except IO.Error IO.FS.Metadata
  cut : FirstAppendCut
  survivingTail : ByteArray
  retry : LockedFileState FileImage
  failures : BoundedReopenTrace directory (fun target => target = before.target)
    (cut.crashed before directory survivingTail) retry
  currentTail : ByteArray
  nextRef : Nat
  liveRefs : List Nat
  unlock : UnlockReport
  read : HealthyBoundedWalReports directory (retry.owners.set (directory.file .lock) (some nextDescriptor))
    nextDescriptor before.wal retry.image.directory.active before.target.range.watermark before.published.durable
    currentTail
  removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit)
  write : FilePath → ByteArray → EStateM IO.Error FileImage Unit
  sync : Array FilePath → EStateM IO.Error FileImage Unit
  renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit

namespace SegmentedAppendPowerLossReport

variable {directory : DiskDirectory} {before : SegmentedWriterState} {oldDescriptor nextDescriptor : Nat}

def attempt (report : SegmentedAppendPowerLossReport directory before oldDescriptor nextDescriptor) :
    BoundedReopenAttempt :=
  ⟨nextDescriptor, report.nextRef, .ok true, report.unlock, report.read.reports.readOptional, report.read.list,
    (fun path => .ok (report.read.reports.lstat path)), report.read.reports.readBin, report.read.readPrefix,
    report.removeFile, report.write, report.sync, report.renameFile⟩

def plan (report : SegmentedAppendPowerLossReport directory before oldDescriptor nextDescriptor) : Plan :=
  ⟨before.target.range.through, before.target.first, report.retry.image.later.visible,
    before.wal.active.bytes ++ report.currentTail⟩

structure Valid (report : SegmentedAppendPowerLossReport directory before oldDescriptor nextDescriptor) : Prop where
  prepared : prepareWrite before.installed.table report.event.key report.event.value = some (report.event, report.table)
  fits : before.installed.walBytes + frameSize < UInt64.size
  activeGuard : ∃ metadata,
    report.activeMetadata (directory.file (.walSegment before.installed.activeFirst)) = .ok metadata ∧
    metadata.type = .file ∧ metadata.numLinks = 1 ∧
    metadata.byteSize.toNat = before.installed.walBytes - before.installed.activeFirst * frameSize
  survives : report.survivingTail ∈ ByteArray.empty :: report.cut.crashTails
  keeper : report.retry.image.keeper.active = some (before.wal.active.bytes ++ report.currentTail)
  fresh : ∀ ref ∈ report.liveRefs, ref < report.nextRef
  acquisition : TryLockObserves report.retry.owners directory (.ok true)
  syncDirectory : report.sync #[directory.path] report.retry.image = .ok () report.retry.image.syncDirectory
  healthy : ∀ action prior next,
    ReachesAction before.target report.retry.image.syncDirectory report.plan.finishActions action prior →
    prior.effect before.target action = some next →
    performPaths directory report.plan report.removeFile throw report.write report.sync report.renameFile action prior =
      .ok () next

theorem Valid.submittedSequence {report : SegmentedAppendPowerLossReport directory before oldDescriptor nextDescriptor}
    (observed : report.Valid) (ready : before.Ready directory oldDescriptor) :
    report.event.sequence.toNat = before.history.length + 1 := by
  obtain ⟨model, refined, represented⟩ := ready.resumed.canonical
  have count : before.history.length = before.installed.table.committed.toNat :=
    represented.committed_count.symm.trans (congrArg UInt64.toNat refined.committed).symm
  obtain ⟨event, ordinal, _, _, _⟩ := prepareWrite_extends_history ready.resumed.ordered count observed.prepared
  rw [event]
  exact ordinal

private def reopenedWriter (before : SegmentedWriterState) (table : PackedTable) (final : LockedFileState FileImage) :
    SegmentedWriterState :=
  SegmentedWriterState.ofReopen { before.installed with table } before.wal before.history
    before.published before.target before.checkpoint final

structure Installs (report : SegmentedAppendPowerLossReport directory before oldDescriptor nextDescriptor)
    (after : SegmentedWriterState) : Prop where
  initialLoss : BoundedReopenTrace directory (fun target => target = before.target)
    ⟨report.cut.physical before, before.owners⟩ (report.cut.crashed before directory report.survivingTail)
  openEffect : ∃ session final table,
    report.attempt.run directory report.retry = .ok session final ∧ session.directory = directory ∧
    session.descriptor = nextDescriptor ∧ session.phase = .ready (reopenedWriter before table final).installed ∧
    after = reopenedWriter before table final

private theorem Valid.matchSelected {report : SegmentedAppendPowerLossReport directory before oldDescriptor nextDescriptor}
    (observed : report.Valid) (ready : before.RetainedReady directory oldDescriptor)
    (selected : CanonicalKeeperLayout report.retry.image before.history) (target : selected.target = before.target) :
    selected.range.watermark = before.target.range.watermark ∧ selected.tail = report.currentTail ∧
    ∀ action prior next,
      ReachesAction selected.target report.retry.image.syncDirectory selected.plan.finishActions action prior →
      prior.effect selected.target action = some next →
      performPaths directory selected.plan report.removeFile throw report.write report.sync report.renameFile action prior =
        .ok () next := by
  have keeperBytes : selected.keeper.bytes = before.wal.active.bytes := by
    change selected.target.trimmed = _
    rw [target, ready.resumed.contents, ready.active, ready.layout.activeBytes]
  have tail : selected.tail = report.currentTail := by
    have bytes := Option.some.inj (selected.visible.symm.trans observed.keeper)
    rw [keeperBytes] at bytes
    exact (ByteArray.append_right_inj before.wal.active.bytes).mp bytes
  have watermark := congrArg (fun target : Target => target.range.watermark) target
  have through := congrArg (fun target : Target => target.range.through) target
  have first := congrArg Target.first target
  have plan : selected.plan = report.plan := by
    change (⟨selected.target.range.through, selected.target.first, report.retry.image.later.visible,
      selected.keeper.bytes ++ selected.tail⟩ : Plan) = _
    rw [through, first, keeperBytes, tail]
    rfl
  have effects : ∀ action prior next,
      ReachesAction selected.target report.retry.image.syncDirectory selected.plan.finishActions action prior →
      prior.effect selected.target action = some next →
      performPaths directory selected.plan report.removeFile throw report.write report.sync report.renameFile action prior =
        .ok () next := by
    rw [target, plan]
    exact observed.healthy
  change selected.range.watermark = before.target.range.watermark at watermark
  exact ⟨watermark, tail, effects⟩

private theorem assembleEndpoint (report : SegmentedAppendPowerLossReport directory before oldDescriptor nextDescriptor)
    (ready : before.RetainedReady directory oldDescriptor)
    {writer : SegmentedWriterState} (writerReady : writer.RetainedReady directory nextDescriptor)
    (powerLoss : BoundedReopenTrace directory (fun target => target = before.target)
      ⟨report.cut.physical before, before.owners⟩ (report.cut.crashed before directory report.survivingTail))
    {session : SegmentedSession} {final : LockedFileState FileImage}
    (ran : report.attempt.run directory report.retry = .ok session final)
    (path : session.directory = directory) (owner : session.descriptor = nextDescriptor)
    (phase : session.phase = .ready writer.installed) (files : writer.files = final.image)
    (owners : writer.owners = final.owners) (wal : writer.wal = { before.wal with directory := final.image.directory })
    (writerTarget : writer.target = before.target) (history : writer.history = before.history)
    (durable : writer.published.durable = before.published.durable) (checkpoint : writer.checkpoint = before.checkpoint)
    (generation : writer.installed.generation = before.installed.generation) : report.Installs writer := by
  let next := reopenedWriter before writer.installed.table final
  have count : writer.installed.walBytes = before.installed.walBytes := by
    rw [writerReady.resumed.bytes, history, ready.resumed.bytes]
  have start : writer.installed.activeFirst = before.installed.activeFirst := by
    rw [writerReady.resumed.keeper, writerTarget, ← ready.resumed.keeper]
  have installed : writer.installed = next.installed := by
    change Installed.mk writer.installed.table writer.installed.generation writer.installed.walBytes
        writer.installed.activeFirst = Installed.mk writer.installed.table before.installed.generation
        before.installed.walBytes before.installed.activeFirst
    rw [Installed.mk.injEq]
    exact ⟨rfl, generation, count, start⟩
  have published : writer.published = next.published := by
    change CheckpointPublication.Image.mk writer.published.manifest writer.published.durable =
      CheckpointPublication.Image.mk (final.image.directory.project .manifest) before.published.durable
    rw [CheckpointPublication.Image.mk.injEq]
    exact ⟨writerReady.manifestFiles.trans (congrArg (fun files : FileImage => files.directory.project .manifest) files),
      durable⟩
  have exactWriter : writer = next := by
    change SegmentedWriterState.mk writer.installed writer.wal writer.history writer.files writer.published
        writer.target writer.checkpoint writer.owners =
      SegmentedWriterState.mk next.installed next.wal next.history next.files next.published
        next.target next.checkpoint next.owners
    rw [SegmentedWriterState.mk.injEq]
    exact ⟨installed, wal, history, files, published, writerTarget, checkpoint, owners⟩
  exact ⟨powerLoss, session, final, writer.installed.table, ran, path, owner, installed ▸ phase, exactWriter⟩

theorem installs (report : SegmentedAppendPowerLossReport directory before oldDescriptor nextDescriptor)
    (observed : report.Valid) (ready : before.Ready directory oldDescriptor) :
    ∃ after, report.Installs after ∧ after.Ready directory nextDescriptor := by
  obtain ⟨powerLoss, selected, target, reopened⟩ := report.cut.reopens ready observed.survives report.failures
    (nextDescriptor := nextDescriptor) report.liveRefs observed.fresh observed.acquisition report.unlock
    report.removeFile report.write report.sync report.renameFile
  obtain ⟨watermark, tail, effects⟩ := observed.matchSelected ready.toRetained selected target
  rw [watermark, tail] at reopened
  obtain ⟨session, final, writer, ran, path, owner, phase, files, owners, wal, writerTarget, history,
    durable, checkpoint, generation, writerReady⟩ := reopened report.read observed.syncDirectory effects
  exact ⟨writer, report.assembleEndpoint ready.toRetained writerReady.toRetained powerLoss ran path owner phase
    files owners wal writerTarget history durable checkpoint generation, writerReady⟩

/-- Recover the exact prior writer after power loss in the first append
callback with a retained WAL suffix. The attempted frame is outside the
unchanged marker even if its bytes survived. -/
theorem installsRetained (report : SegmentedAppendPowerLossReport directory before oldDescriptor nextDescriptor)
    (observed : report.Valid) (ready : before.RetainedReady directory oldDescriptor) :
    ∃ after, report.Installs after ∧ after.RetainedReady directory nextDescriptor := by
  obtain ⟨powerLoss, selected, target, reopened⟩ := report.cut.reopensRetained ready observed.survives report.failures
    (nextDescriptor := nextDescriptor) report.liveRefs observed.fresh observed.acquisition report.unlock
    report.removeFile report.write report.sync report.renameFile
  obtain ⟨watermark, tail, effects⟩ := observed.matchSelected ready selected target
  rw [watermark, tail] at reopened
  obtain ⟨session, final, writer, ran, path, owner, phase, files, owners, wal, writerTarget, history,
    durable, checkpoint, generation, writerReady⟩ := reopened report.read observed.syncDirectory effects
  exact ⟨writer, report.assembleEndpoint ready writerReady powerLoss ran path owner phase
    files owners wal writerTarget history durable checkpoint generation, writerReady⟩

/-- The cached recovery action reaches the same report endpoint after a crash
inside the append callback, including the session and final file image. -/
theorem installsRetainedCached (report : SegmentedAppendPowerLossReport directory before oldDescriptor nextDescriptor)
    (observed : report.Valid) (ready : before.RetainedReady directory oldDescriptor)
    (sizes : SizedCheckpointRunReports directory report.read.reports report.retry.image.directory.active.manifest
      before.published.durable)
    (cached : CachedWalFileReports directory report.read.reports before.wal before.target.range.watermark report.currentTail) :
    ∃ after, report.Installs after ∧ ∃ session final,
      runOpenWithInstallation directory nextDescriptor report.nextRef (.ok true) report.unlock
        (report.read.reopenCached sizes cached report.removeFile report.write report.sync report.renameFile)
        report.retry = .ok session final ∧
      session.phase = .ready after.installed ∧ final.image = after.files ∧ final.owners = after.owners := by
  obtain ⟨_, selected, exactTarget, _⟩ := report.cut.reopensRetained ready observed.survives report.failures
    (nextDescriptor := nextDescriptor) report.liveRefs observed.fresh observed.acquisition report.unlock
    report.removeFile report.write report.sync report.renameFile
  have pair : report.retry.image.directory.active = before.target.pair := congrArg Target.pair exactTarget
  have decoded : report.retry.image.directory.active.walRange = some before.target.range := by
    rw [pair]
    exact before.target.decoded
  have chosen : before.wal.Selects report.retry.image.directory.active := by
    rw [pair, ← ready.walPair]
    exact List.mem_cons_self ..
  have checkpoint : SelectedIntegrityCheckpoint before.published.durable report.retry.image.directory.active.manifest
      before.checkpoint := by
    rw [pair]
    exact ready.resumed.selected
  have same := report.read.reopenCached_eq sizes cached ready.layout ready.valid chosen decoded rfl
    ready.resumed.through checkpoint report.removeFile report.write report.sync report.renameFile
  obtain ⟨after, installed, _⟩ := report.installsRetained observed ready
  obtain ⟨session, final, _, ran, _, _, phase, exactWriter⟩ := installed.openEffect
  refine ⟨after, installed, session, final, ?_, ?_, ?_, ?_⟩
  · rw [same]
    exact ran
  · rw [exactWriter]
    exact phase
  · rw [exactWriter]
    rfl
  · rw [exactWriter]
    rfl

theorem Installs.unique {report : SegmentedAppendPowerLossReport directory before oldDescriptor nextDescriptor}
    {left right : SegmentedWriterState} (a : report.Installs left) (b : report.Installs right) : left = right := by
  obtain ⟨_, _, leftTable, leftOpen, _, _, leftPhase, rfl⟩ := a.openEffect
  obtain ⟨_, _, rightTable, rightOpen, _, _, rightPhase, rfl⟩ := b.openEffect
  obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj (leftOpen.symm.trans rightOpen)
  have table : leftTable = rightTable := congrArg Installed.table (Phase.ready.inj (leftPhase.symm.trans rightPhase))
  rw [table]

theorem Installs.preservesReady {report : SegmentedAppendPowerLossReport directory before oldDescriptor nextDescriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after) (observed : report.Valid)
    (ready : before.Ready directory oldDescriptor) : after.Ready directory nextDescriptor := by
  obtain ⟨_, exactEndpoint, next⟩ := report.installs observed ready
  exact exactEndpoint.unique endpoint ▸ next

theorem Installs.preservesRetained {report : SegmentedAppendPowerLossReport directory before oldDescriptor nextDescriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after) (observed : report.Valid)
    (ready : before.RetainedReady directory oldDescriptor) : after.RetainedReady directory nextDescriptor := by
  obtain ⟨_, exactEndpoint, next⟩ := report.installsRetained observed ready
  exact exactEndpoint.unique endpoint ▸ next

theorem Installs.preservesChain {report : SegmentedAppendPowerLossReport directory before oldDescriptor nextDescriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after)
    (chain : WalSegment.Chain before.history 0 before.wal.segments) :
    WalSegment.Chain after.history 0 after.wal.segments := by
  obtain ⟨_, _, _, _, _, _, _, rfl⟩ := endpoint.openEffect
  exact chain

theorem Installs.history {report : SegmentedAppendPowerLossReport directory before oldDescriptor nextDescriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after) : after.history = before.history := by
  obtain ⟨_, _, _, _, _, _, _, rfl⟩ := endpoint.openEffect
  rfl

theorem Installs.checkpoint {report : SegmentedAppendPowerLossReport directory before oldDescriptor nextDescriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after) : after.checkpoint = before.checkpoint := by
  obtain ⟨_, _, _, _, _, _, _, rfl⟩ := endpoint.openEffect
  rfl

theorem Installs.generation {report : SegmentedAppendPowerLossReport directory before oldDescriptor nextDescriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after) :
    after.installed.generation = before.installed.generation := by
  obtain ⟨_, _, _, _, _, _, _, rfl⟩ := endpoint.openEffect
  rfl

end SegmentedAppendPowerLossReport

end Alvoki.Storage.DiskSession
