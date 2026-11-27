import Alvoki.Storage.Disk.WalBatchCommitReports
import Alvoki.Storage.Disk.Proofs.Write.RetainedWriterReopen
import Alvoki.Storage.Disk.Proofs.Append.SegmentedAppendRecovery

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WalSegmentCommit WAL.Boundary

/-- Reported batch commit after the native guards. The error carries the
physical state left by the callbacks. -/
structure SegmentedBatchFailure (directory : DiskDirectory) (before : SegmentedWriterState) where
  rows : List (UInt64 × Option UInt64)
  batch : List WAL.Write
  table : PackedTable
  effects : WriteEffects
  append : FilePath → ByteArray → EStateM IO.Error WriteFiles Unit
  stage : FilePath → ByteArray → EStateM IO.Error WriteFiles Unit
  sync : Array FilePath → EStateM IO.Error WriteFiles Unit
  rename : FilePath → FilePath → EStateM IO.Error WriteFiles Unit
  cause : IO.Error
  failed : WriteFiles
  nonempty : rows ≠ []
  prepared : prepareBatch before.installed.table rows = some (batch, table)
  fits : before.installed.walBytes + WAL.frameSize * rows.length < UInt64.size
  reports : BatchCommitReports directory before.installed.activeFirst before.history batch
    (before.installed.walBytes + WAL.frameSize * rows.length) effects
    (before.wal.directory.staged .walBoundary) append stage sync rename
  ran : commitBytesAt directory before.installed.activeFirst (WAL.encodeBatch batch)
    (before.installed.walBytes + WAL.frameSize * rows.length) append stage sync rename
    (WriteFiles.initial before.history (before.wal.directory.staged .walBoundary)) = .error cause failed

namespace SegmentedBatchFailure

variable {directory : DiskDirectory} {before : SegmentedWriterState}

def proposed (failure : SegmentedBatchFailure directory before) : Installed :=
  { before.installed with
    table := failure.table
    walBytes := before.installed.walBytes + WAL.frameSize * failure.rows.length }

def commit (failure : SegmentedBatchFailure directory before) : EStateM IO.Error WriteFiles Unit :=
  commitBytesAt directory before.installed.activeFirst (WAL.encodeBatch failure.batch)
    failure.proposed.walBytes failure.append failure.stage failure.sync failure.rename

def released (failure : SegmentedBatchFailure directory before) : LockedFileState FileImage :=
  ⟨before.wal.appendReopenFiles
    (failure.failed.reopenSegment before.wal.active.first before.history before.wal.directory.active.manifest)
    before.files.keeper.staged, before.owners.set (directory.file .lock) none⟩

def poisoned (failure : SegmentedBatchFailure directory before) :
    Phase Installed × LockedFileState WriteFiles :=
  (.poisoned, ⟨failure.failed, before.owners⟩)

/-- The reported failure fixes the modeled byte cut of the whole batch. -/
theorem retainedCut {writer : Nat} (failure : SegmentedBatchFailure directory before)
    (ready : before.RetainedReady directory writer) :
    (WAL.encode (before.history ++ failure.batch)).size < UInt64.size ∧
    writeFilesAfter (runBatchEffects before.history failure.batch failure.effects
      (before.wal.directory.staged .walBoundary)) = failure.failed := by
  obtain ⟨model, refined, represented⟩ := ready.resumed.canonical
  have count : before.history.length = before.installed.table.committed.toNat :=
    represented.committed_count.symm.trans (congrArg UInt64.toNat refined.committed).symm
  obtain ⟨_, _, _, size⟩ := prepareBatch_extends_history ready.resumed.ordered count failure.prepared
  have byteCount : failure.proposed.walBytes = (WAL.encode (before.history ++ failure.batch)).size := by
    change before.installed.walBytes + WAL.frameSize * failure.rows.length = _
    rw [ready.resumed.bytes, size]
  exact ⟨byteCount ▸ failure.fits, failure.reports.cut_eq_of_error byteCount failure.ran⟩

end SegmentedBatchFailure

/-- Batch publication error and release followed by a finite retry trace
and the primitive reports from the healthy bounded open. -/
structure SegmentedBatchRecoveryReport (directory : DiskDirectory) (before : SegmentedWriterState)
    (writer descriptor : Nat) where
  failure : SegmentedBatchFailure directory before
  release : SegmentedFailureRelease writer
  retry : LockedFileState FileImage
  attempts : BoundedReopenTrace directory (BatchRetryTarget before.history failure.batch before.wal.active.first)
    failure.released retry
  reopen : BoundedReopenAttempt
  descriptorEq : reopen.descriptor = descriptor
  acquired : reopen.acquired = .ok true
  acquisition : TryLockObserves retry.owners directory (.ok true)
  liveRefs : List Nat
  fresh : ∀ ref ∈ liveRefs, ref < reopen.nextRef
  reads : ∀ history, ∀ layout : CanonicalKeeperLayout retry.image history,
    (history = before.history ∨ history = before.history ++ failure.batch) → layout.target.first = before.wal.active.first →
    let wal := before.wal.appendSelectedView retry.image.directory.active history
    ∃ raw : HealthyBoundedWalReports directory (retry.owners.set (directory.file .lock) (some descriptor)) descriptor
        wal retry.image.directory.active layout.range.watermark before.published.durable layout.tail,
      reopen.recover directory = raw.reopen reopen.removeFile reopen.write reopen.sync reopen.renameFile
  settles : reopen.sync #[directory.path] retry.image = .ok () retry.image.syncDirectory
  healthy : ∀ history, ∀ layout : CanonicalKeeperLayout retry.image history,
    (history = before.history ∨ history = before.history ++ failure.batch) → layout.target.first = before.wal.active.first →
    ∀ action prior next,
      ReachesAction layout.target retry.image.syncDirectory layout.plan.finishActions action prior →
      prior.effect layout.target action = some next →
      performPaths directory layout.plan reopen.removeFile throw reopen.write reopen.sync reopen.renameFile action prior =
        .ok () next

namespace SegmentedBatchRecoveryReport

variable {directory : DiskDirectory} {before : SegmentedWriterState} {writer descriptor : Nat}

/-- Observed failure handoff and exact writer installed by the healthy retry. -/
structure Installs (report : SegmentedBatchRecoveryReport directory before writer descriptor)
    (after : SegmentedWriterState) : Prop where
  uncertain : runPreparedWrite report.failure.proposed report.failure.table.committed report.failure.commit
    (.ready before.installed,
      ⟨WriteFiles.initial before.history (before.wal.directory.staged .walBoundary), before.owners⟩) =
    .error (.commitUnknown report.failure.cause) report.failure.poisoned
  released : report.release.Observed (directory := directory) report.failure.poisoned
    ⟨report.failure.failed, before.owners.set (directory.file .lock) none⟩
  reopened : ∃ session final, report.reopen.run directory report.retry = .ok session final ∧
    session.directory = directory ∧ session.descriptor = descriptor ∧ session.phase = .ready after.installed ∧
    after.files = final.image ∧ after.owners = final.owners
  history : after.history = before.history ∨ after.history = before.history ++ report.failure.batch
  wal : after.wal = { before.wal.appendSelectedView report.retry.image.directory.active after.history with
    directory := after.files.directory }
  pair : after.target.pair = report.retry.image.directory.active
  first : after.target.first = before.wal.active.first
  durable : after.published.durable = before.published.durable
  retained : after.RetainedReady directory descriptor

/-- The native commit error poisons and releases the writer. The modeled
cut and the actual retry reports then establish the exact retained writer. -/
theorem installsRetained (report : SegmentedBatchRecoveryReport directory before writer descriptor)
    (ready : before.RetainedReady directory writer) :
    ∃ after, report.Installs after ∧ after.RetainedReady directory descriptor := by
  let failure := report.failure
  let initial := WriteFiles.initial before.history (before.wal.directory.staged .walBoundary)
  obtain ⟨uncertain, closed, dropped, _⟩ := runPreparedWrite_failure_handoff
    (before := ⟨initial, before.owners⟩) before.installed failure.proposed failure.table.committed
    (commit := failure.commit) failure.ran ready.held
  have released : report.release.Observed (directory := directory) failure.poisoned
      ⟨failure.failed, before.owners.set (directory.file .lock) none⟩ := by
    cases report.release with
    | closed => exact closed
    | references held drops last => exact dropped held drops last
  obtain ⟨fits, cut⟩ := failure.retainedCut ready
  have attempts : BoundedReopenTrace directory (BatchRetryTarget before.history failure.batch before.wal.active.first)
      ⟨before.wal.appendReopenFiles
        ((writeFilesAfter (runBatchEffects before.history failure.batch failure.effects
          (before.wal.directory.staged .walBoundary))).reopenSegment
          before.wal.active.first before.history before.wal.directory.active.manifest)
        before.files.keeper.staged, before.owners.set (directory.file .lock) none⟩ report.retry := by
    rw [cut]
    exact report.attempts
  have oldRange : before.wal.directory.active.walRange = some ⟨before.target.range.watermark, before.history.length⟩ := by
    rw [ready.walPair, ← ready.resumed.through]
    exact before.target.decoded
  have accepted := (congrArg DirectoryPublication.Bindings.manifest ready.walPair).symm ▸ ready.resumed.accepted
  obtain ⟨model, refined, represented⟩ := ready.resumed.canonical
  have count : before.history.length = before.installed.table.committed.toNat :=
    represented.committed_count.symm.trans (congrArg UInt64.toNat refined.committed).symm
  obtain ⟨kept, _, history, allowed, _, layout, valid, selected, _, first, generation, _, installs⟩ :=
    attempts.installsAfterBatchCut ready.layout ready.valid oldRange ready.resumed.ordered count failure.prepared
      fits accepted failure.effects ⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩⟩ report.liveRefs report.fresh report.acquisition
      report.reopen.unlock report.reopen.removeFile report.reopen.write report.reopen.sync report.reopen.renameFile
  obtain ⟨raw, exactRead⟩ := report.reads history selected allowed first
  let wal := before.wal.appendSelectedView report.retry.image.directory.active history
  have keeper : selected.target.first = wal.active.first := first
  have sealed : report.retry.image.kept = (wal.checkpointReopenFiles wal.directory none).kept := kept
  have spans : ∀ segment ∈ wal.sealed, segment.bytes.size = (segment.last - segment.first) * WAL.frameSize :=
    ready.spans
  obtain ⟨session, final, after, returned, path, slot, phase, files, owners, actualWal, target, exactHistory,
      _, durable, next⟩ :=
    (installs raw report.settles (report.healthy history selected allowed first)).writerRetained layout valid
      spans rfl keeper sealed
  have actualResult : report.reopen.run directory report.retry = .ok session final := by
    unfold BoundedReopenAttempt.run
    rw [report.descriptorEq, report.acquired, exactRead]
    exact returned
  have afterWal : after.wal = { before.wal.appendSelectedView report.retry.image.directory.active after.history with
      directory := after.files.directory } := by rw [actualWal, files, exactHistory]
  exact ⟨after, ⟨uncertain, released, ⟨session, final, actualResult, path, slot, phase, files, owners⟩,
    exactHistory ▸ allowed, afterWal, target ▸ rfl, target ▸ first, durable, next⟩, next⟩

end SegmentedBatchRecoveryReport

end Alvoki.Storage.DiskSession
