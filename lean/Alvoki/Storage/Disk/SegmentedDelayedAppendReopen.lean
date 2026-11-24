import Alvoki.Storage.Disk.RetainedAppendRecovery

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WalSegmentCommit WAL.Boundary
open WAL (frameSize)

/-- A retained directory description can sync the exact image left by
the failed append after the writer's last lock reference drops. Its
reported effect, followed by ordinary bounded retries, supplies the
lineage for the actual final open. -/
theorem DelayedDirectorySync.reopensRetainedAppendError {directory : DiskDirectory} {before : SegmentedWriterState}
    {writer descriptor : Nat} (barrier : DelayedDirectorySync directory)
    (ready : before.RetainedReady directory writer) (failure : SegmentedAppendFailure directory before)
    (references : HeldLockReferences writer) (last : references.remaining barrier.drops = [])
    (separate : barrier.captured.description ≠ writer)
    {retry : LockedFileState FileImage}
    (attempts : BoundedReopenTrace directory (AppendRetryTarget before.history failure.event before.wal.active.first)
      (barrier.after failure.released) retry)
    (reopen : BoundedReopenAttempt) (descriptorEq : reopen.descriptor = descriptor)
    (acquired : reopen.acquired = .ok true) (acquisition : TryLockObserves retry.owners directory (.ok true))
    (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < reopen.nextRef)
    (reads : ∀ history, ∀ layout : CanonicalKeeperLayout retry.image history,
      (history = before.history ∨ history = before.history ++ [failure.event]) → layout.target.first = before.wal.active.first →
      let wal := before.wal.appendSelectedView retry.image.directory.active history
      ∃ raw : HealthyBoundedWalReports directory (retry.owners.set (directory.file .lock) (some descriptor)) descriptor
          wal retry.image.directory.active layout.range.watermark before.published.durable layout.tail,
        reopen.recover directory = raw.reopen reopen.removeFile reopen.write reopen.sync reopen.renameFile)
    (settles : reopen.sync #[directory.path] retry.image = .ok () retry.image.syncDirectory)
    (healthy : ∀ history, ∀ layout : CanonicalKeeperLayout retry.image history,
      (history = before.history ∨ history = before.history ++ [failure.event]) → layout.target.first = before.wal.active.first →
      ∀ action prior next,
        ReachesAction layout.target retry.image.syncDirectory layout.plan.finishActions action prior →
        prior.effect layout.target action = some next →
        performPaths directory layout.plan reopen.removeFile throw reopen.write reopen.sync reopen.renameFile action prior =
          .ok () next) :
    let initial := WriteFiles.initial before.history (before.wal.directory.staged .walBoundary)
    let proposed : Installed := { before.installed with table := failure.table, walBytes := before.installed.walBytes + frameSize }
    let commit := commitAt directory before.installed.activeFirst failure.event (before.installed.walBytes + frameSize)
      failure.append failure.stage failure.sync failure.rename
    runPreparedWrite proposed failure.event.sequence commit (.ready before.installed, ⟨initial, before.owners⟩) =
      .error (.commitUnknown failure.cause) failure.poisoned ∧
    (SegmentedFailureRelease.references references barrier.drops last).Observed (directory := directory) failure.poisoned
      ⟨failure.failed, failure.released.owners⟩ ∧
    barrier.effectTarget.description ≠ writer ∧
    (barrier.after failure.released).owners (directory.file .lock) = none ∧
    ∃ after, AppendRetryEndpoint directory before failure.event retry descriptor (reopen.run directory retry) after ∧
      after.RetainedReady directory descriptor ∧
      retry.image.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode after.history).size.toUInt64) ∧
      after.checkpoint = before.checkpoint ∧ after.installed.generation = before.installed.generation := by
  intro initial proposed commit
  obtain ⟨uncertain, _, dropped, _⟩ := runPreparedWrite_failure_handoff
    (before := ⟨initial, before.owners⟩) before.installed proposed failure.event.sequence failure.ran ready.held
  obtain ⟨extended, fits, exactCut⟩ := failure.retainedCut ready
  have released : (⟨appendCutFiles before.wal before.history failure.event failure.effects before.files.keeper.staged,
      before.owners.set (directory.file .lock) none⟩ : LockedFileState FileImage) = failure.released := by
    rw [exactCut]
    rfl
  have oldRange : before.wal.directory.active.walRange =
      some ⟨before.target.range.watermark, before.history.length⟩ := by
    rw [ready.walPair, ← ready.resumed.through]
    exact before.target.decoded
  obtain ⟨retained, unlocked, reached⟩ := barrier.retainedAppendCutAfterLastDrop references ready.held last separate
    ready.layout ready.valid oldRange failure.event fits failure.effects before.files.keeper.staged
  have continued := attempts.continuesLineage (released ▸ reached)
    (fun a b pair => AppendRetryTarget.unique a b pair)
  exact ⟨uncertain, dropped references barrier.drops last, retained, released ▸ unlocked,
    continued.reopensRetainedAppend ready failure.event extended fits failure.effects
      reopen descriptorEq acquired acquisition liveRefs fresh reads settles healthy⟩

end Alvoki.Storage.DiskSession
