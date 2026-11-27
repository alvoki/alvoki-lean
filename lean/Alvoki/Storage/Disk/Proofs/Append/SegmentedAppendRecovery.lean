import Alvoki.Storage.Disk.Proofs.Append.AppendRetrySession
import Alvoki.Storage.Disk.Proofs.Recovery.SegmentedFailureRelease
import Alvoki.Storage.Disk.Proofs.Write.SegmentedWriterState

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WalSegmentCommit WAL.Boundary
open WAL (frameSize)

/-- A submitted frame and its reported append and publication error after
the native active-file guard. The commit error preserves the physical cut. -/
structure SegmentedAppendFailure (directory : DiskDirectory) (before : SegmentedWriterState) where
  event : WAL.Write
  table : PackedTable
  effects : WriteEffects
  append : FilePath → ByteArray → EStateM IO.Error WriteFiles Unit
  stage : FilePath → ByteArray → EStateM IO.Error WriteFiles Unit
  sync : Array FilePath → EStateM IO.Error WriteFiles Unit
  rename : FilePath → FilePath → EStateM IO.Error WriteFiles Unit
  cause : IO.Error
  failed : WriteFiles
  prepared : prepareWrite before.installed.table event.key event.value = some (event, table)
  fits : before.installed.walBytes + frameSize < UInt64.size
  reports : AppendCommitReports directory before.installed.activeFirst before.history event
    (before.installed.walBytes + frameSize) effects (before.wal.directory.staged .walBoundary) append stage sync rename
  ran : commitAt directory before.installed.activeFirst event (before.installed.walBytes + frameSize)
    append stage sync rename (WriteFiles.initial before.history (before.wal.directory.staged .walBoundary)) =
      .error cause failed

namespace SegmentedAppendFailure

variable {directory : DiskDirectory} {before : SegmentedWriterState}

/-- Keep the prior keeper scratch in the append cut. The append projection
models the selected manifest binding and the boundary stage. -/
def released (failure : SegmentedAppendFailure directory before) : LockedFileState FileImage :=
  ⟨before.wal.appendReopenFiles
    (failure.failed.reopenSegment before.wal.active.first before.history before.wal.directory.active.manifest)
    before.files.keeper.staged, before.owners.set (directory.file .lock) none⟩

def poisoned (failure : SegmentedAppendFailure directory before) : Phase Installed × LockedFileState WriteFiles :=
  (.poisoned, ⟨failure.failed, before.owners⟩)

end SegmentedAppendFailure

/-- The reported append failure, finite failed-reopen prefix, and the
primitive reports from the final bounded open. -/
structure SegmentedAppendRecoveryReport (directory : DiskDirectory) (before : SegmentedWriterState)
    (writer descriptor : Nat) where
  failure : SegmentedAppendFailure directory before
  release : SegmentedFailureRelease writer
  retry : LockedFileState FileImage
  attempts : BoundedReopenTrace directory (AppendRetryTarget before.history failure.event before.wal.active.first)
    failure.released retry
  reopen : BoundedReopenAttempt
  descriptorEq : reopen.descriptor = descriptor
  acquired : reopen.acquired = .ok true
  acquisition : TryLockObserves retry.owners directory (.ok true)
  liveRefs : List Nat
  fresh : ∀ ref ∈ liveRefs, ref < reopen.nextRef
  reads : ∀ history, ∀ layout : CanonicalKeeperLayout retry.image history,
    (history = before.history ∨ history = before.history ++ [failure.event]) → layout.target.first = before.wal.active.first →
    let wal := before.wal.appendSelectedView retry.image.directory.active history
    ∃ raw : HealthyBoundedWalReports directory (retry.owners.set (directory.file .lock) (some descriptor)) descriptor
        wal retry.image.directory.active layout.range.watermark before.published.durable layout.tail,
      reopen.recover directory = raw.reopen reopen.removeFile reopen.write reopen.sync reopen.renameFile
  settles : reopen.sync #[directory.path] retry.image = .ok () retry.image.syncDirectory
  healthy : ∀ history, ∀ layout : CanonicalKeeperLayout retry.image history,
    (history = before.history ∨ history = before.history ++ [failure.event]) → layout.target.first = before.wal.active.first →
    ∀ action prior next,
      ReachesAction layout.target retry.image.syncDirectory layout.plan.finishActions action prior →
      prior.effect layout.target action = some next →
      performPaths directory layout.plan reopen.removeFile throw reopen.write reopen.sync reopen.renameFile action prior =
        .ok () next

/-- The exact writer established by a bounded open after an append cut.
Its physical keeper and selected history are fixed by the returned image. -/
structure AppendRetryEndpoint (directory : DiskDirectory) (before : SegmentedWriterState)
    (event : WAL.Write) (retry : LockedFileState FileImage) (descriptor : Nat)
    (result : EStateM.Result IO.Error (LockedFileState FileImage) SegmentedSession)
    (after : SegmentedWriterState) : Prop where
  reopened : ∃ session final, result = .ok session final ∧
    session.directory = directory ∧ session.descriptor = descriptor ∧ session.phase = .ready after.installed ∧
    after.files = final.image ∧ after.owners = final.owners
  history : after.history = before.history ∨ after.history = before.history ++ [event]
  wal : after.wal = { before.wal.appendSelectedView retry.image.directory.active after.history with
    directory := after.files.directory }
  pair : after.target.pair = retry.image.directory.active
  first : after.target.first = before.wal.active.first
  through : after.target.range.through = after.history.length
  trimmed : after.target.trimmed = WAL.encode (after.history.drop after.target.first)
  durable : after.published.durable = before.published.durable
  manifest : after.published.manifest = after.files.directory.project .manifest
  checkpoint : SelectedIntegrityCheckpoint after.published.durable after.target.pair.manifest after.checkpoint

namespace SegmentedAppendRecoveryReport

variable {directory : DiskDirectory} {before : SegmentedWriterState} {writer descriptor : Nat}

structure Installs (report : SegmentedAppendRecoveryReport directory before writer descriptor)
    (after : SegmentedWriterState) : Prop extends
    AppendRetryEndpoint directory before report.failure.event report.retry descriptor
      (report.reopen.run directory report.retry) after where
  uncertain : runPreparedWrite
    { before.installed with table := report.failure.table, walBytes := before.installed.walBytes + frameSize }
    report.failure.event.sequence
    (commitAt directory before.installed.activeFirst report.failure.event (before.installed.walBytes + frameSize)
      report.failure.append report.failure.stage report.failure.sync report.failure.rename)
    (.ready before.installed,
      ⟨WriteFiles.initial before.history (before.wal.directory.staged .walBoundary), before.owners⟩) =
    .error (.commitUnknown report.failure.cause) report.failure.poisoned
  released : report.release.Observed (directory := directory) report.failure.poisoned
    ⟨report.failure.failed, before.owners.set (directory.file .lock) none⟩

/-- Derive the next ready writer from the previous installed state and
the actual reported append and reopen operations. -/
theorem installs (report : SegmentedAppendRecoveryReport directory before writer descriptor)
    (ready : before.Ready directory writer) :
    ∃ after, report.Installs after ∧ after.Ready directory descriptor := by
  let failure := report.failure
  obtain ⟨uncertain, closed, drop, _, history, survived, _, _, wal, walEq, layout, chain, kept, selected, _,
    keeper, opened⟩ :=
    report.attempts.installsAfterAppendError (descriptor := descriptor) ready.held ready.appendInput failure.prepared failure.fits failure.effects
      failure.append failure.stage failure.sync failure.rename failure.reports failure.ran before.files.keeper.staged
      report.liveRefs report.fresh report.acquisition report.reopen.unlock report.reopen.removeFile
      report.reopen.write report.reopen.sync report.reopen.renameFile
  subst wal
  obtain ⟨raw, exactRead⟩ := report.reads history selected survived keeper
  obtain ⟨session, final, after, returned, path, acquired, phase, files, owners, actualWal, target, exactHistory,
    durable, next⟩ := (opened raw report.settles (report.healthy history selected survived keeper)).writerReady layout chain keeper kept
  have actualResult : report.reopen.run directory report.retry = .ok session final := by
    unfold BoundedReopenAttempt.run
    rw [report.descriptorEq, report.acquired, exactRead]
    exact returned
  have afterWal : after.wal = { before.wal.appendSelectedView report.retry.image.directory.active after.history with
      directory := after.files.directory } := by rw [actualWal, files, exactHistory]
  have released : report.release.Observed (directory := directory) failure.poisoned
      ⟨failure.failed, before.owners.set (directory.file .lock) none⟩ := by
    cases report.release with
    | closed => exact closed
    | references held drops last => exact drop held drops last
  exact ⟨after, ⟨⟨⟨session, final, actualResult, path, acquired, phase, files, owners⟩,
    exactHistory ▸ survived, afterWal, target ▸ rfl, by rw [target, keeper]; rfl,
    next.resumed.through, next.resumed.contents, durable, next.manifestFiles, next.resumed.selected⟩,
    uncertain, released⟩, next⟩

private theorem sameCheckpoint {durable binding left right}
    (a : SelectedIntegrityCheckpoint durable binding left) (b : SelectedIntegrityCheckpoint durable binding right) :
    left = right := by
  cases a with
  | absent => cases b; rfl
  | present decoded stored loaded =>
    cases b with
    | present otherDecode otherStored otherLoaded =>
      cases Except.ok.inj (decoded.symm.trans otherDecode)
      cases Option.some.inj (stored.symm.trans otherStored)
      cases Except.ok.inj (loaded.symm.trans otherLoaded)
      rfl

theorem _root_.Alvoki.Storage.DiskSession.AppendRetryEndpoint.unique {directory before event retry descriptor result}
    {left right : SegmentedWriterState}
    (a : AppendRetryEndpoint directory before event retry descriptor result left)
    (b : AppendRetryEndpoint directory before event retry descriptor result right) : left = right := by
  obtain ⟨ls, lf, lr, _, _, lp, li, lo⟩ := a.reopened
  obtain ⟨rs, rf, rr, _, _, rp, ri, ro⟩ := b.reopened
  obtain ⟨sameSession, sameFinal⟩ := EStateM.Result.ok.inj (lr.symm.trans rr)
  have installed : left.installed = right.installed := by
    rw [sameSession] at lp
    exact Phase.ready.inj (lp.symm.trans rp)
  have files := li.trans ((congrArg LockedFileState.image sameFinal).trans ri.symm)
  have owners := lo.trans ((congrArg LockedFileState.owners sameFinal).trans ro.symm)
  have pair := a.pair.trans b.pair.symm
  have target := AppendRetryTarget.unique ⟨a.first, left.history, a.history, a.through, a.first ▸ a.trimmed⟩
    ⟨b.first, right.history, b.history, b.through, b.first ▸ b.trimmed⟩ pair
  have lengths := a.through.symm.trans ((congrArg (·.range.through) target).trans b.through)
  have history : left.history = right.history := by
    rcases a.history with first | first <;> rcases b.history with second | second <;>
      rw [first, second] at lengths ⊢ <;> simp at lengths ⊢
  have wal : left.wal = right.wal := by rw [a.wal, b.wal, files, history]
  have durable := a.durable.trans b.durable.symm
  have manifest := a.manifest.trans (congrArg (·.directory.project .manifest) files) |>.trans b.manifest.symm
  have published : left.published = right.published := by
    cases lp : left.published
    cases rp : right.published
    rw [lp, rp] at manifest durable
    cases manifest
    cases durable
    rfl
  have checkpoint := sameCheckpoint a.checkpoint (pair.symm ▸ durable.symm ▸ b.checkpoint)
  cases left
  cases right
  cases installed
  cases files
  cases owners
  cases history
  cases wal
  cases target
  cases published
  cases checkpoint
  rfl

theorem Installs.unique {report : SegmentedAppendRecoveryReport directory before writer descriptor}
    {left right : SegmentedWriterState} (a : report.Installs left) (b : report.Installs right) : left = right :=
  a.toAppendRetryEndpoint.unique b.toAppendRetryEndpoint

theorem Installs.preservesReady {report : SegmentedAppendRecoveryReport directory before writer descriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after) (ready : before.Ready directory writer) :
    after.Ready directory descriptor := by
  obtain ⟨actual, observed, ready⟩ := report.installs ready
  exact observed.unique endpoint ▸ ready

end SegmentedAppendRecoveryReport

end Alvoki.Storage.DiskSession
