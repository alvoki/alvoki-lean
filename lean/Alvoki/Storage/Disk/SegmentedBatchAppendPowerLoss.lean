import Alvoki.Storage.Disk.WalBatchAppendPowerLoss
import Alvoki.Storage.Disk.WalSegmentCachedAppendPowerLoss

namespace Alvoki.Storage.DiskSession

open System WalSegmentCommit WalSegmentRepair WAL.Boundary

/-- An interrupted batch append and the reports for the next healthy
cached open after a finite retry prefix. The old marker stays authoritative. -/
structure SegmentedBatchAppendPowerLossReport (directory : DiskDirectory) (before : SegmentedWriterState)
    (descriptor : Nat) where
  rows : List (UInt64 × Option UInt64)
  batch : List WAL.Write
  table : PackedTable
  activeMetadata : FilePath → Except IO.Error IO.FS.Metadata
  appendCall : FilePath × ByteArray
  cut : FirstAppendCut
  survivingTail : ByteArray
  retry : LockedFileState FileImage
  failures : BoundedReopenTrace directory (fun target => target = before.target)
    (cut.crashed before directory survivingTail) retry
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

namespace SegmentedBatchAppendPowerLossReport

variable {directory : DiskDirectory} {before : SegmentedWriterState} {writer descriptor : Nat}

def run (report : SegmentedBatchAppendPowerLossReport directory before descriptor) :
    EStateM.Result IO.Error (LockedFileState FileImage) SegmentedSession :=
  runOpenWithInstallation directory descriptor report.nextRef (.ok true) report.unlock
    (report.read.reopenCached report.sizes report.cached report.removeFile report.write report.sync report.renameFile)
    report.retry

structure Valid (report : SegmentedBatchAppendPowerLossReport directory before descriptor) : Prop where
  prepared : prepareBatch before.installed.table report.rows = some (report.batch, report.table)
  nonempty : report.rows ≠ []
  fits : before.installed.walBytes + WAL.frameSize * report.rows.length < UInt64.size
  activeGuard : ∃ metadata,
    report.activeMetadata (directory.file (.walSegment before.installed.activeFirst)) = .ok metadata ∧
    metadata.type = .file ∧ metadata.numLinks = 1 ∧
    metadata.byteSize.toNat = before.installed.walBytes - before.installed.activeFirst * WAL.frameSize
  invoked : report.appendCall = (directory.file (.walSegment before.installed.activeFirst), WAL.encodeBatch report.batch)
  survives : report.survivingTail ∈ ByteArray.empty :: report.cut.crashTails
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

/-- The admitted batch reaches exactly the reported append invocation
while the old writer holds the lock. The stop tag belongs to the
interpreter for the interruption. -/
theorem Valid.reachesInterruption {report : SegmentedBatchAppendPowerLossReport directory before descriptor}
    (observed : report.Valid) (ready : before.RetainedReady directory writer)
    (stage : FilePath → ByteArray → EStateM (FilePath × ByteArray) WriteFiles Unit)
    (sync : Array FilePath → EStateM (FilePath × ByteArray) WriteFiles Unit)
    (rename : FilePath → FilePath → EStateM (FilePath × ByteArray) WriteFiles Unit) :
    let scratch := before.files.directory.staged .walBoundary
    let count := (WAL.encode (before.history ++ report.batch)).size
    before.owners.Owns directory writer ∧
    count = before.installed.walBytes + WAL.frameSize * report.rows.length ∧
    commitBytesAt directory before.wal.active.first (WAL.encodeBatch report.batch) count
      (fun path bytes _ => .error (path, bytes) (report.cut.writeFiles before.history scratch))
      stage sync rename (WriteFiles.initial before.history scratch) =
    .error report.appendCall
      (writeFilesAfter (runBatchEffects before.history report.batch report.cut.writeEffects scratch)) := by
  obtain ⟨model, refined, represented⟩ := ready.resumed.canonical
  have count : before.history.length = before.installed.table.committed.toNat :=
    represented.committed_count.symm.trans (congrArg UInt64.toNat refined.committed).symm
  have width := (prepareBatch_extends_history ready.resumed.ordered count observed.prepared).2.2.2
  have first := ready.resumed.keeper.trans ready.active
  refine ⟨ready.held, width.trans ?_, ?_⟩
  · rw [ready.resumed.bytes]
  · rw [observed.invoked, first]
    exact report.cut.interruptsBatch directory _ _ before.history report.batch _ stage sync rename

structure Installs (report : SegmentedBatchAppendPowerLossReport directory before descriptor)
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

/-- The cached installer recovers every old acknowledgement and none of
the interrupted batch. It leaves the prior checkpoint and keeper durable. -/
theorem installs (report : SegmentedBatchAppendPowerLossReport directory before descriptor)
    (observed : report.Valid) (ready : before.RetainedReady directory writer) :
    ∃ after, report.Installs after := by
  obtain ⟨powerLoss, selected, target, _, _, install⟩ :=
    report.cut.reopensRetainedCached ready observed.survives report.failures
      (nextDescriptor := descriptor) report.liveRefs observed.fresh observed.acquisition report.unlock
      report.removeFile report.write report.sync report.renameFile
  have keeperBytes : selected.keeper.bytes = before.wal.active.bytes := by
    change selected.target.trimmed = _
    rw [target, ready.resumed.contents, ready.active, ready.layout.activeBytes]
  have tail : selected.tail = report.currentTail := by
    have bytes := Option.some.inj (selected.visible.symm.trans observed.keeper)
    rw [keeperBytes] at bytes
    exact (ByteArray.append_right_inj before.wal.active.bytes).mp bytes
  have watermark : selected.range.watermark = before.target.range.watermark :=
    congrArg (fun chosen : Target => chosen.range.watermark) target
  rw [watermark, tail] at install
  obtain ⟨session, final, after, returned, path, lock, phase, files, owners, durableKeeper, _, target, history,
    durable, checkpoint, generation, retained⟩ :=
    install report.read report.sizes report.cached observed.settles (observed.healthy selected target)
  exact ⟨after, ⟨powerLoss.trans report.failures, ⟨session, final, returned, path, lock, phase, files, owners, durableKeeper⟩,
    target, history, checkpoint, generation, durable, retained⟩⟩

end SegmentedBatchAppendPowerLossReport
end Alvoki.Storage.DiskSession
