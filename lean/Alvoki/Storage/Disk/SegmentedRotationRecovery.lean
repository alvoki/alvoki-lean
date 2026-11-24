import Alvoki.Storage.Disk.RotationLockHandoff
import Alvoki.Storage.Disk.SegmentedWriterEntry

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WalSegmentRotation
open WAL (frameSize)
open WAL.Boundary (CheckpointRepresentsPrefix)

/-- The native rotation branch after the nonempty and active-file guards.
The reports observe the successor lookup and the effects on its name. -/
structure SegmentedRotationFailure (directory : DiskDirectory) (before : SegmentedWriterState) where
  read : FilePath → EStateM IO.Error WalSegmentRotation.State (Option ByteArray)
  create : FilePath → EStateM IO.Error WalSegmentRotation.State Unit
  sync : FilePath → EStateM IO.Error WalSegmentRotation.State Unit
  cause : IO.Error
  cut : WalSegmentRotation.State
  nonempty : before.installed.activeFirst < before.installed.walBytes / frameSize
  lookup : match read (directory.file (.walSegment before.wal.active.last)) (.initial before.wal) with
    | .ok bytes after => bytes = (WalSegmentRotation.State.initial before.wal).observeSuccessor ∧
        after = .initial before.wal
    | .error _ after => after = .initial before.wal
  reports : EffectReports (performPaths directory before.wal.active.last create sync)
  failed : runAt directory (before.installed.walBytes / frameSize) read create sync (.initial before.wal) =
    .error cause cut

namespace SegmentedRotationFailure

variable {directory : DiskDirectory} {before : SegmentedWriterState}

def poisoned (failure : SegmentedRotationFailure directory before) :
    Phase Installed × LockedFileState WalSegmentRotation.State :=
  (.poisoned, ⟨failure.cut, before.owners⟩)

def released (failure : SegmentedRotationFailure directory before) : LockedFileState WalSegmentRotation.State :=
  ⟨failure.cut, before.owners.set (directory.file .lock) none⟩

/-- The actual publication failure poisons the original session and keeps
its exact file cut. Close or a reported last-reference drop releases it. -/
theorem handoff (failure : SegmentedRotationFailure directory before) {descriptor : Nat}
    (ready : before.Ready directory descriptor) :
    let successor := before.installed.walBytes / frameSize
    Trace before.wal failure.cut ∧
    runPreparedRotation { before.installed with activeFirst := successor }
      (runAt directory successor failure.read failure.create failure.sync)
      (.ready before.installed, ⟨.initial before.wal, before.owners⟩) = .error failure.cause failure.poisoned ∧
    runCloseWithFiles directory descriptor .success failure.poisoned = .ok () (.closed, failure.released) ∧
    (∀ (references : HeldLockReferences descriptor) (drops : List LockReferenceDrop),
      references.remaining drops = [] →
      references.afterFileDrops drops directory failure.poisoned.2 = failure.released) := by
  have absolute : before.installed.walBytes = before.history.length * frameSize := by
    rw [ready.resumed.bytes, WAL.encode_size, Nat.mul_comm]
  obtain ⟨_, _, files, poisoned, close, drops⟩ := runPreparedRotation_failure_handoff
    (before := ⟨.initial before.wal, before.owners⟩) (ready.rotationInput failure.nonempty)
    .start before.installed absolute ready.appendInput.first ready.held
    failure.read failure.create failure.sync failure.lookup failure.reports failure.failed
  exact ⟨files, poisoned, close, drops⟩

end SegmentedRotationFailure

private theorem selectedIntegrityCheckpoint_unique {durable binding left right}
    (a : SelectedIntegrityCheckpoint durable binding left) (b : SelectedIntegrityCheckpoint durable binding right) :
    left = right := by
  cases a with
  | absent => cases b; rfl
  | present decoded stored loaded =>
    cases b with
    | present decodeAgain storeAgain loadAgain =>
      cases Except.ok.inj (decoded.symm.trans decodeAgain)
      cases Option.some.inj (stored.symm.trans storeAgain)
      cases Except.ok.inj (loaded.symm.trans loadAgain)
      rfl

/-- Reached file reports for the next healthy bounded open after the
rotation failure and its observed retry prefix. -/
structure SegmentedRotationRecoveryReport (directory : DiskDirectory) (before : SegmentedWriterState)
    (descriptor : Nat) where
  failure : SegmentedRotationFailure directory before
  retry : LockedFileState WalSegmentRotation.State
  attempts : RotationReopenFailures directory before.wal before.history failure.released retry
  nextRef : Nat
  liveRefs : List Nat
  fresh : ∀ ref ∈ liveRefs, ref < nextRef
  acquisition : TryLockObserves retry.owners directory (.ok true)
  unlock : UnlockReport
  removeFile : FilePath → EStateM IO.Error WalSegmentRotation.State (Except IO.Error Unit)
  write : FilePath → ByteArray → EStateM IO.Error WalSegmentRotation.State Unit
  sync : Array FilePath → EStateM IO.Error WalSegmentRotation.State Unit
  renameFile : FilePath → FilePath → EStateM IO.Error WalSegmentRotation.State Unit
  read : HealthyBoundedWalReports directory (retry.owners.set (directory.file .lock) (some descriptor)) descriptor
    (retry.image.settleForReopen.visible before.wal) (retry.image.settledReopenImage before.wal).directory.active
    before.target.range.watermark before.published.durable ByteArray.empty
  syncDirectory : sync #[directory.path] retry.image = .ok () retry.image.settleForReopen
  syncKeeper : sync #[directory.file (.walSegment (retry.image.visible before.wal).active.first)]
    retry.image.settleForReopen = .ok () retry.image.settleForReopen

def SegmentedRotationRecoveryReport.attempt {directory before descriptor}
    (report : SegmentedRotationRecoveryReport directory before descriptor) :
    BoundedReopenAttempt WalSegmentRotation.State :=
  ⟨descriptor, report.nextRef, .ok true, report.unlock, report.read.reports.readOptional, report.read.list,
    (fun path => .ok (report.read.reports.lstat path)), report.read.reports.readBin, report.read.readPrefix,
    report.removeFile, report.write, report.sync, report.renameFile⟩

def SegmentedRotationRecoveryReport.run {directory before descriptor}
    (report : SegmentedRotationRecoveryReport directory before descriptor) :
    EStateM.Result IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession :=
  report.attempt.run directory report.retry

/-- The exact session returned by a concrete bounded open. The keeper and
metadata are fixed by that result and the original acknowledged history. -/
structure SegmentedRotationReopened (directory : DiskDirectory) (descriptor : Nat)
    (before after : SegmentedWriterState)
    (result : EStateM.Result IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession) : Prop where
  returned : ∃ session final, result = .ok session final ∧ session.directory = directory ∧
    session.descriptor = descriptor ∧ session.phase = .ready after.installed ∧
    after.files = final.image.settledReopenImage before.wal ∧ after.wal = final.image.visible before.wal ∧
    after.owners = final.owners
  history : after.history = before.history
  pair : after.target.pair = before.target.pair
  first : after.target.first = after.wal.active.first
  bytes : after.target.trimmed = after.wal.active.bytes
  manifest : after.published.manifest = after.files.directory.project .manifest
  durableRuns : after.published.durable = before.published.durable
  checkpoint : after.checkpoint = before.checkpoint
  generation : after.installed.generation = before.installed.generation
  execution : ∃ report : SegmentedRotationRecoveryReport directory before descriptor, result = report.run

/-- Retry the actual reported rotation failure under the next acquired lock.
The keeper follows the surviving name. Rotation preserves the acknowledged
history and checkpoint across the whole handoff. -/
theorem SegmentedRotationRecoveryReport.installs {directory : DiskDirectory} {before : SegmentedWriterState}
    {descriptor newDescriptor : Nat} (report : SegmentedRotationRecoveryReport directory before newDescriptor)
    (ready : before.Ready directory descriptor) :
    ∃ writer, SegmentedRotationReopened directory newDescriptor before writer report.run ∧
      writer.Ready directory newDescriptor := by
  let failure := report.failure
  let retry := report.retry
  let fixed := retry.image.settledReopenImage before.wal
  have attempts := report.attempts
  have rotation := ready.rotationInput failure.nonempty
  have origin := (failure.handoff ready).1
  have originalPair {pair} (chosen : before.wal.Selects pair) : pair = before.wal.directory.active := by
    simpa [WalSegmentImage.Selects, ready.walDirectorySettled] using chosen
  have originalPairs (pair) (chosen : before.wal.Selects pair) : ∃ range, pair.walRange = some range ∧
      range.through = before.history.length ∧
      before.published.AcceptsVersioned before.history.length.toUInt64
        (CheckpointRepresentsPrefix before.history) pair.manifest := by
    rw [originalPair chosen]
    exact ⟨_, ready.appendInput.range, rfl, ready.appendInput.checkpoint⟩
  obtain ⟨selected, keeper, install⟩ := attempts.installs origin rotation ready.layout ready.walValid
    ready.resumed.ordered before.published originalPairs (descriptor := newDescriptor)
    report.liveRefs report.fresh report.acquisition report.unlock report.removeFile report.write report.sync report.renameFile
  have trace := attempts.rotationTrace rotation ready.layout origin
  have original := originalPair (trace.selectsOriginal (List.mem_cons_self ..))
  have fixedPair : fixed.directory.active = retry.image.metadata.active := by
    change (retry.image.settleForReopen.visible before.wal).directory.active = _
    rw [WalSegmentRotation.State.visible_metadata]
    rfl
  have priorPair := (congrArg DirectoryPublication.Image.active ready.directoryFiles.symm).trans
    ready.resumed.ready.selected
  have pair : fixed.directory.active = before.target.pair :=
    fixedPair.trans (original.trans priorPair)
  have range := Option.some.inj (selected.decoded.symm.trans
    (pair.symm ▸ before.target.decoded : fixed.directory.active.walRange = some before.target.range))
  have exactKeeper : fixed.keeper.active = some selected.keeper.bytes := by
    rw [keeper, ← retry.image.settleForReopen_keeper before.wal]
    rfl
  have tail : selected.tail = ByteArray.empty := by
    have bytes := Option.some.inj (selected.visible.symm.trans exactKeeper)
    have sizes := congrArg ByteArray.size bytes
    rw [ByteArray.size_append] at sizes
    exact ByteArray.size_eq_zero_iff.mp (by omega)
  rw [congrArg MarkedWalRange.watermark range, tail, keeper] at install
  obtain ⟨session, final, writer, returned, path, lock, phase, files, visible, target, owners, history, durable, reopened⟩ :=
    (install report.read report.syncDirectory report.syncKeeper).writerReady ready.chain
  have targetPair := (congrArg Target.pair target).trans pair
  have loaded := reopened.resumed.selected
  rw [durable, targetPair] at loaded
  have checkpoint := selectedIntegrityCheckpoint_unique loaded ready.resumed.selected
  have generation : writer.installed.generation = before.installed.generation := by
    rw [reopened.resumed.generation, checkpoint, ← ready.resumed.generation]
  have keeperBytes : writer.target.trimmed = writer.wal.active.bytes := by
    rw [reopened.resumed.contents, reopened.active, reopened.layout.activeBytes]
  exact ⟨writer, ⟨⟨session, final, returned, path, lock, phase, files, visible, owners⟩,
    history, targetPair, reopened.active, keeperBytes, reopened.manifestFiles, durable, checkpoint, generation,
    ⟨report, rfl⟩⟩, reopened⟩

private theorem sameRotationTarget {left right : Target} (pair : left.pair = right.pair)
    (first : left.first = right.first) (bytes : left.trimmed = right.trimmed) : left = right := by
  have range := Option.some.inj (left.decoded.symm.trans (pair ▸ right.decoded))
  cases left
  cases right
  cases pair
  cases range
  cases first
  cases bytes
  rfl

theorem SegmentedRotationReopened.unique {directory descriptor before left right result}
    (a : SegmentedRotationReopened directory descriptor before left result)
    (b : SegmentedRotationReopened directory descriptor before right result) : left = right := by
  obtain ⟨sessionA, finalA, outcomeA, _, _, phaseA, filesA, walA, ownersA⟩ := a.returned
  obtain ⟨sessionB, finalB, outcomeB, _, _, phaseB, filesB, walB, ownersB⟩ := b.returned
  obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj (outcomeA.symm.trans outcomeB)
  have installed := Phase.ready.inj (phaseA.symm.trans phaseB)
  have files := filesA.trans filesB.symm
  have wal := walA.trans walB.symm
  have owners := ownersA.trans ownersB.symm
  have history := a.history.trans b.history.symm
  have checkpoint := a.checkpoint.trans b.checkpoint.symm
  have target := sameRotationTarget (a.pair.trans b.pair.symm)
    (a.first.trans ((congrArg (fun wal : WalSegmentImage => wal.active.first) wal).trans b.first.symm))
    (a.bytes.trans ((congrArg (fun wal : WalSegmentImage => wal.active.bytes) wal).trans b.bytes.symm))
  have manifest := a.manifest.trans
    ((congrArg (fun files : FileImage => files.directory.project .manifest) files).trans b.manifest.symm)
  have durable := a.durableRuns.trans b.durableRuns.symm
  have sameImage {a b : CheckpointPublication.Image}
      (manifest : a.manifest = b.manifest) (durable : a.durable = b.durable) : a = b := by
    cases a
    cases b
    cases manifest
    cases durable
    rfl
  have published := sameImage manifest durable
  cases left
  cases right
  cases installed
  cases wal
  cases history
  cases files
  cases published
  cases target
  cases checkpoint
  cases owners
  rfl

/-- Re-establish the full ready invariant by executing the certified report
from the preceding ready writer. Its returned endpoint is deterministic. -/
theorem SegmentedRotationReopened.preservesReady {directory oldDescriptor descriptor before after result}
    (opened : SegmentedRotationReopened directory descriptor before after result)
    (ready : before.Ready directory oldDescriptor) : after.Ready directory descriptor := by
  obtain ⟨report, observed⟩ := opened.execution
  obtain ⟨writer, exactEndpoint, writerReady⟩ := report.installs ready
  have same := (observed ▸ opened).unique exactEndpoint
  exact same.symm ▸ writerReady

end Alvoki.Storage.DiskSession
