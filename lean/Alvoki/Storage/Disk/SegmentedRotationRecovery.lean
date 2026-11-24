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

/-- The exact session returned by the bounded open, together with the
settled WAL and checkpoint available to the next operation. -/
structure SegmentedRotationReopened (directory : DiskDirectory) (descriptor : Nat)
    (before after : SegmentedWriterState)
    (result : EStateM.Result IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession) : Prop where
  returned : ∃ session final, result = .ok session final ∧ session.directory = directory ∧
    session.descriptor = descriptor ∧ session.phase = .ready after.installed ∧
    after.files = final.image.settledReopenImage before.wal ∧ after.wal = final.image.visible before.wal ∧
    after.owners = final.owners
  ready : after.Ready directory descriptor
  history : after.history = before.history
  pair : after.target.pair = before.target.pair
  durableRuns : after.published.durable = before.published.durable
  checkpoint : after.checkpoint = before.checkpoint
  generation : after.installed.generation = before.installed.generation
  execution : ∃ (failure : SegmentedRotationFailure directory before)
      (retry : LockedFileState WalSegmentRotation.State)
      (attempt : BoundedReopenAttempt WalSegmentRotation.State),
    RotationReopenFailures directory before.wal before.history failure.released retry ∧
    attempt.descriptor = descriptor ∧ attempt.acquired = .ok true ∧
    TryLockObserves retry.owners directory attempt.acquired ∧ result = attempt.run directory retry

/-- Retry the actual reported rotation failure under the next acquired lock.
The keeper follows the surviving name. Rotation preserves the acknowledged
history and checkpoint across the whole handoff. -/
theorem SegmentedRotationFailure.reopens {directory : DiskDirectory} {before : SegmentedWriterState}
    (failure : SegmentedRotationFailure directory before) {descriptor newDescriptor nextRef : Nat}
    (ready : before.Ready directory descriptor) {retry : LockedFileState WalSegmentRotation.State}
    (attempts : RotationReopenFailures directory before.wal before.history failure.released retry)
    (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < nextRef)
    (acquisition : TryLockObserves retry.owners directory (.ok true)) (unlock : UnlockReport)
    (removeFile : FilePath → EStateM IO.Error WalSegmentRotation.State (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error WalSegmentRotation.State Unit)
    (sync : Array FilePath → EStateM IO.Error WalSegmentRotation.State Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error WalSegmentRotation.State Unit) :
    let wal := retry.image.settleForReopen.visible before.wal
    let fixed := retry.image.settledReopenImage before.wal
    ∀ raw : HealthyBoundedWalReports directory (retry.owners.set (directory.file .lock) (some newDescriptor))
        newDescriptor wal fixed.directory.active before.target.range.watermark before.published.durable ByteArray.empty,
      sync #[directory.path] retry.image = .ok () retry.image.settleForReopen →
      sync #[directory.file (.walSegment (retry.image.visible before.wal).active.first)] retry.image.settleForReopen =
        .ok () retry.image.settleForReopen →
      let attempt : BoundedReopenAttempt WalSegmentRotation.State :=
        ⟨newDescriptor, nextRef, .ok true, unlock, raw.reports.readOptional, raw.list,
          (fun path => .ok (raw.reports.lstat path)), raw.reports.readBin, raw.readPrefix,
          removeFile, write, sync, renameFile⟩
      ∃ writer, SegmentedRotationReopened directory newDescriptor before writer (attempt.run directory retry) := by
  intro wal fixed raw metadata keeperSync attempt
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
    liveRefs fresh acquisition unlock removeFile write sync renameFile
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
    (install raw metadata keeperSync).writerReady ready.chain
  have targetPair := (congrArg Target.pair target).trans pair
  have loaded := reopened.resumed.selected
  rw [durable, targetPair] at loaded
  have checkpoint := selectedIntegrityCheckpoint_unique loaded ready.resumed.selected
  have generation : writer.installed.generation = before.installed.generation := by
    rw [reopened.resumed.generation, checkpoint, ← ready.resumed.generation]
  exact ⟨writer, ⟨⟨session, final, returned, path, lock, phase, files, visible, owners⟩, reopened,
    history, targetPair, durable, checkpoint, generation,
    ⟨failure, retry, attempt, attempts, rfl, rfl, acquisition, rfl⟩⟩⟩

end Alvoki.Storage.DiskSession
