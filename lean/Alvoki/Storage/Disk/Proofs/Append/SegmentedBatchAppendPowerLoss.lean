import Alvoki.Storage.Disk.Proofs.Append.WalBatchAppendPowerLoss
import Alvoki.Storage.Disk.Proofs.Append.WalSegmentCachedAppendPowerLoss

namespace Alvoki.Storage.DiskSession

open System WalSegmentCommit WalSegmentRepair WAL.Boundary

/-- An interruption at the first batch callback, before marker publication.
The observed invocation records the path and bytes passed to the append. -/
structure BatchAppendInterruption (directory : DiskDirectory) (before : SegmentedWriterState) where
  rows : List (UInt64 × Option UInt64)
  batch : List WAL.Write
  table : PackedTable
  activeMetadata : FilePath → Except IO.Error IO.FS.Metadata
  appendCall : FilePath × ByteArray
  cut : FirstAppendCut

namespace BatchAppendInterruption

variable {directory : DiskDirectory} {before : SegmentedWriterState} {writer : Nat}

structure Valid (report : BatchAppendInterruption directory before) : Prop where
  prepared : prepareBatch before.installed.table report.rows = some (report.batch, report.table)
  nonempty : report.rows ≠ []
  fits : before.installed.walBytes + WAL.frameSize * report.rows.length < UInt64.size
  activeGuard : ∃ metadata,
    report.activeMetadata (directory.file (.walSegment before.installed.activeFirst)) = .ok metadata ∧
    metadata.type = .file ∧ metadata.numLinks = 1 ∧
    metadata.byteSize.toNat = before.installed.walBytes - before.installed.activeFirst * WAL.frameSize
  invoked : report.appendCall = (directory.file (.walSegment before.installed.activeFirst), WAL.encodeBatch report.batch)

/-- The interpreter records the first callback's arguments while the old
writer holds the lock. Its stop tag leaves later callbacks unexecuted. -/
def ReachesInterruption (report : BatchAppendInterruption directory before)
    (writer : Nat) : Prop :=
    ∀ (stage : FilePath → ByteArray → EStateM (FilePath × ByteArray) WriteFiles Unit)
      (sync : Array FilePath → EStateM (FilePath × ByteArray) WriteFiles Unit)
      (rename : FilePath → FilePath → EStateM (FilePath × ByteArray) WriteFiles Unit),
    let scratch := before.files.directory.staged .walBoundary
    let count := (WAL.encode (before.history ++ report.batch)).size
    before.owners.Owns directory writer ∧
    count = before.installed.walBytes + WAL.frameSize * report.rows.length ∧
    commitBytesAt directory before.wal.active.first (WAL.encodeBatch report.batch) count
      (fun path bytes _ => .error (path, bytes) (report.cut.writeFiles before.history scratch))
      stage sync rename (WriteFiles.initial before.history scratch) =
    .error report.appendCall
      (writeFilesAfter (runBatchEffects before.history report.batch report.cut.writeEffects scratch))

/-- The admitted batch reaches exactly the reported append invocation. -/
theorem Valid.reachesInterruption {report : BatchAppendInterruption directory before}
    (observed : report.Valid) (ready : before.RetainedReady directory writer) : report.ReachesInterruption writer := by
  intro stage sync rename
  obtain ⟨model, refined, represented⟩ := ready.resumed.canonical
  have count : before.history.length = before.installed.table.committed.toNat :=
    represented.committed_count.symm.trans (congrArg UInt64.toNat refined.committed).symm
  have width := (prepareBatch_extends_history ready.resumed.ordered count observed.prepared).2.2.2
  have first := ready.resumed.keeper.trans ready.active
  refine ⟨ready.held, width.trans ?_, ?_⟩
  · rw [ready.resumed.bytes]
  · rw [observed.invoked, first]
    exact report.cut.interruptsBatch directory _ _ before.history report.batch _ stage sync rename

end BatchAppendInterruption

/-- The observed interrupted append and the reports for the next healthy
cached open. The retry origin depends on how the writer stopped. -/
structure SegmentedBatchAppendReopenReport (directory : DiskDirectory) (before : SegmentedWriterState)
    (descriptor : Nat) (origin : FirstAppendCut → LockedFileState FileImage) extends
    BatchAppendInterruption directory before where
  retry : LockedFileState FileImage
  failures : BoundedReopenTrace directory (fun target => target = before.target) (origin cut) retry
  currentTail : ByteArray
  nextRef : Nat
  liveRefs : List Nat
  unlock : UnlockReport
  read : HealthyBoundedWalReports directory (retry.owners.set (directory.file .lock) (some descriptor)) descriptor
    before.wal retry.image.directory.active before.target.range.watermark before.published.durable currentTail
  sizes : SizedCheckpointRunReports directory read.reports retry.image.directory.active.manifest before.published.durable
  cached : CachedWalFileReports directory read.reports before.wal before.target.range.watermark currentTail
  removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit)
  write : FilePath → ByteArray → EStateM IO.Error FileImage Unit
  sync : Array FilePath → EStateM IO.Error FileImage Unit
  renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit

namespace SegmentedBatchAppendReopenReport

variable {directory : DiskDirectory} {before : SegmentedWriterState} {writer descriptor : Nat}
  {origin : FirstAppendCut → LockedFileState FileImage}

def run (report : SegmentedBatchAppendReopenReport directory before descriptor origin) :
    EStateM.Result IO.Error (LockedFileState FileImage) SegmentedSession :=
  runOpenWithInstallation directory descriptor report.nextRef (.ok true) report.unlock
    (report.read.reopenCached report.sizes report.cached report.removeFile report.write report.sync report.renameFile)
    report.retry

structure Valid (report : SegmentedBatchAppendReopenReport directory before descriptor origin) : Prop extends
    toInterruptionValid : report.toBatchAppendInterruption.Valid where
  keeper : report.retry.image.keeper.active = some (before.wal.active.bytes ++ report.currentTail)
  fresh : ∀ ref ∈ report.liveRefs, ref < report.nextRef
  acquisition : TryLockObserves report.retry.owners directory (.ok true)
  settles : report.sync #[directory.path] report.retry.image = .ok () report.retry.image.syncDirectory
  healthy : ∀ selected : CanonicalKeeperLayout report.retry.image before.history, selected.target = before.target →
    ∀ action prior next,
      ReachesAction selected.target report.retry.image.syncDirectory selected.plan.finishActions action prior →
      prior.effect selected.target action = some next →
      performPaths directory selected.plan report.removeFile throw report.write report.sync report.renameFile action prior =
        .ok () next

abbrev ReachesInterruption (report : SegmentedBatchAppendReopenReport directory before descriptor origin)
    (writer : Nat) : Prop :=
  report.toBatchAppendInterruption.ReachesInterruption writer

theorem Valid.reachesInterruption {report : SegmentedBatchAppendReopenReport directory before descriptor origin}
    (observed : report.Valid) (ready : before.RetainedReady directory writer) : report.ReachesInterruption writer :=
  observed.toInterruptionValid.reachesInterruption ready

structure Installs (report : SegmentedBatchAppendReopenReport directory before descriptor origin)
    (after : SegmentedWriterState) : Prop where
  retries : BoundedReopenTrace directory (fun target => target = before.target)
    ⟨report.cut.physical before, before.owners⟩ report.retry
  reopened : ∃ session final, report.run = .ok session final ∧
    session.directory = directory ∧ session.descriptor = descriptor ∧ session.phase = .ready after.installed ∧
    after.files = final.image ∧ after.owners = final.owners ∧ final.image.Ready before.target
  target : after.target = before.target
  history : after.history = before.history
  checkpoint : after.checkpoint = before.checkpoint
  generation : after.installed.generation = before.installed.generation
  durable : after.published.durable = before.published.durable
  retained : after.RetainedReady directory descriptor
  sealedWal : after.wal.sealed = before.wal.sealed

/-- From either observed cut, the prior marker and exact selected files
authorize the same bounded repair and installation. -/
theorem installsFromFixedAuthority (report : SegmentedBatchAppendReopenReport directory before descriptor origin)
    (observed : report.Valid) (ready : before.RetainedReady directory writer)
    (stopped : BoundedReopenTrace directory (fun target => target = before.target)
      ⟨report.cut.physical before, before.owners⟩ (origin report.cut))
    (source : CanonicalKeeperLayout (origin report.cut).image before.history)
    (target : source.target = before.target) (sameKeeper : source.keeper = before.wal.active)
    (descriptors : source.sealed ++ [source.keeper] = before.wal.readDescriptors source.range.watermark)
    (offsets : selectWalSegmentReads (before.wal.segments.map WalSegment.first) source.range.watermark =
      some (source.first, (before.wal.readDescriptors source.range.watermark).map WalSegment.first))
    (prepared : Prepared (origin report.cut).image source.target source.plan)
    (fixed : (origin report.cut).image.syncDirectory = (origin report.cut).image)
    (emptyLater : (origin report.cut).image.later.visible = [])
    (sealed : (origin report.cut).image.kept = before.files.kept) :
    ∃ after, report.Installs after := by
  have attempts : BoundedReopenTrace directory (fun target => target = source.target) (origin report.cut) report.retry :=
    target.symm ▸ report.failures
  have pair : (origin report.cut).image.directory.active = before.target.pair := congrArg Target.pair target
  obtain ⟨kept, selected, selectedTarget, install⟩ := attempts.installsAfterFixedAuthority
    ready.layout ready.resumed.ordered source sameKeeper descriptors offsets prepared fixed emptyLater
    (by rw [pair]; exact ready.resumed.accepted) (by rw [pair]; exact ready.resumed.generationRead)
    report.liveRefs observed.fresh observed.acquisition report.unlock report.removeFile report.write
    report.sync report.renameFile
  have sameTarget := selectedTarget.trans target
  have keeperBytes : selected.keeper.bytes = before.wal.active.bytes := by
    change selected.target.trimmed = _
    rw [sameTarget, ready.resumed.contents, ready.active, ready.layout.activeBytes]
  have tail : selected.tail = report.currentTail := by
    have bytes := Option.some.inj (selected.visible.symm.trans observed.keeper)
    rw [keeperBytes] at bytes
    exact (ByteArray.append_right_inj before.wal.active.bytes).mp bytes
  have watermark : selected.range.watermark = before.target.range.watermark :=
    congrArg (fun chosen : Target => chosen.range.watermark) sameTarget
  have retryPair : report.retry.image.directory.active = before.target.pair := congrArg Target.pair sameTarget
  have chosen : before.wal.Selects report.retry.image.directory.active := by
    rw [retryPair, ← ready.walPair]
    exact List.mem_cons_self ..
  have checkpoint : SelectedIntegrityCheckpoint before.published.durable report.retry.image.directory.active.manifest
      before.checkpoint := by rw [retryPair]; exact ready.resumed.selected
  have decoded : report.retry.image.directory.active.walRange = some before.target.range := by
    rw [retryPair]; exact before.target.decoded
  have cachedEq := report.read.reopenCached_eq report.sizes report.cached ready.layout ready.valid chosen decoded rfl
    ready.resumed.through checkpoint report.removeFile report.write report.sync report.renameFile
  have visible : before.wal.directory.active = selected.target.pair := ready.walPair.trans retryPair.symm
  have first : selected.target.first = before.wal.active.first :=
    (congrArg Target.first sameTarget).trans ready.active
  rw [watermark, tail] at install
  obtain ⟨session, final, after, returned, path, lock, phase, files, owners, wal, exactTarget, history,
    generation, durable, retained⟩ :=
    (install report.read observed.settles (observed.healthy selected sameTarget)).writerRetained
      ready.layout ready.valid ready.spans visible first ((kept.trans sealed).trans ready.sealedFiles)
  have target := exactTarget.trans sameTarget
  have selectedCheckpoint := retained.resumed.selected
  rw [target, durable, ← retryPair] at selectedCheckpoint
  have sameCheckpoint := Except.ok.inj ((report.read.readCheckpoint selectedCheckpoint).symm.trans
    (report.read.readCheckpoint checkpoint))
  have durableKeeper : final.image.Ready before.target := by
    rw [← files, ← target]
    exact retained.resumed.ready
  have ran : report.run = .ok session final := by
    unfold run
    rw [cachedEq]
    exact returned
  have sealedWal := congrArg WalSegmentImage.sealed wal
  exact ⟨after, ⟨stopped.trans report.failures, ⟨session, final, ran, path, lock, phase, files, owners, durableKeeper⟩,
    target, history, sameCheckpoint, generation, durable, retained, sealedWal⟩⟩

end SegmentedBatchAppendReopenReport

/-- Reports from a machine crash during the first batch append. -/
structure SegmentedBatchAppendPowerLossReport (directory : DiskDirectory) (before : SegmentedWriterState)
    (descriptor : Nat) where
  survivingTail : ByteArray
  reopen : SegmentedBatchAppendReopenReport directory before descriptor (fun cut => cut.crashed before directory survivingTail)

namespace SegmentedBatchAppendPowerLossReport

variable {directory : DiskDirectory} {before : SegmentedWriterState} {writer descriptor : Nat}

structure Valid (report : SegmentedBatchAppendPowerLossReport directory before descriptor) : Prop extends
    report.reopen.Valid where
  survives : report.survivingTail ∈ ByteArray.empty :: report.reopen.cut.crashTails

theorem Valid.reachesInterruption {report : SegmentedBatchAppendPowerLossReport directory before descriptor}
    (observed : report.Valid) (ready : before.RetainedReady directory writer) : report.reopen.ReachesInterruption writer :=
  observed.toValid.reachesInterruption ready

abbrev Installs (report : SegmentedBatchAppendPowerLossReport directory before descriptor)
    (after : SegmentedWriterState) : Prop := report.reopen.Installs after

/-- The cached installer recovers every old acknowledgement and none of
the interrupted batch. It leaves the prior checkpoint and keeper durable. -/
theorem installs (report : SegmentedBatchAppendPowerLossReport directory before descriptor)
    (observed : report.Valid) (ready : before.RetainedReady directory writer) :
    ∃ after, report.Installs after := by
  obtain ⟨source, target, keeper, descriptors, offsets, prepared⟩ :=
    report.reopen.cut.crashedLayout ready report.survivingTail
  exact report.reopen.installsFromFixedAuthority observed.toValid ready
    (report.reopen.cut.powersOff ready _ observed.survives) source target keeper descriptors offsets prepared rfl rfl rfl

end SegmentedBatchAppendPowerLossReport
end Alvoki.Storage.DiskSession
