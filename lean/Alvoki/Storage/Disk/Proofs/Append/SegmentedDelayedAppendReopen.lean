import Alvoki.Storage.Disk.Proofs.Append.RetainedAppendRecovery
import Alvoki.Storage.Disk.Proofs.WAL.WalSegmentCachedExtentReports

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WalSegmentCommit WAL.Boundary
open WAL (frameSize)

/-- The failed append poisons the writer. The last observed lock drop leaves
the database free while the separate directory description can still sync. -/
abbrev DelayedDirectorySync.AppendHandoff {directory : DiskDirectory} {before : SegmentedWriterState}
    {writer : Nat} (barrier : DelayedDirectorySync directory) (failure : SegmentedAppendFailure directory before)
    (references : HeldLockReferences writer) (last : references.remaining barrier.drops = []) : Prop :=
  let initial := WriteFiles.initial before.history (before.wal.directory.staged .walBoundary)
  let proposed : Installed := { before.installed with table := failure.table, walBytes := before.installed.walBytes + frameSize }
  let commit := commitAt directory before.installed.activeFirst failure.event (before.installed.walBytes + frameSize)
    failure.append failure.stage failure.sync failure.rename
  runPreparedWrite proposed failure.event.sequence commit (.ready before.installed, ⟨initial, before.owners⟩) =
    .error (.commitUnknown failure.cause) failure.poisoned ∧
  (SegmentedFailureRelease.references references barrier.drops last).Observed (directory := directory) failure.poisoned
    ⟨failure.failed, failure.released.owners⟩ ∧
  barrier.effectTarget.description ≠ writer ∧ (barrier.after failure.released).owners (directory.file .lock) = none

private theorem DelayedDirectorySync.appendRetryLineage {directory : DiskDirectory} {before : SegmentedWriterState}
    {writer : Nat} (barrier : DelayedDirectorySync directory)
    (ready : before.RetainedReady directory writer) (failure : SegmentedAppendFailure directory before)
    (references : HeldLockReferences writer) (last : references.remaining barrier.drops = [])
    (separate : barrier.captured.description ≠ writer) {retry : LockedFileState FileImage}
    (attempts : BoundedReopenTrace directory (AppendRetryTarget before.history failure.event before.wal.active.first)
      (barrier.after failure.released) retry) :
    barrier.AppendHandoff failure references last ∧ WAL.OrdinalsFrom 1 (before.history ++ [failure.event]) ∧
      (WAL.encode (before.history ++ [failure.event])).size < UInt64.size ∧
      ReopenLineage (appendCutFiles before.wal before.history failure.event failure.effects before.files.keeper.staged)
        (AppendRetryTarget before.history failure.event before.wal.active.first) retry.image := by
  let initial := WriteFiles.initial before.history (before.wal.directory.staged .walBoundary)
  let proposed : Installed := { before.installed with table := failure.table, walBytes := before.installed.walBytes + frameSize }
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
  exact ⟨⟨uncertain, dropped references barrier.drops last, retained, released ▸ unlocked⟩, extended, fits, continued⟩

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
  obtain ⟨⟨uncertain, dropped, retained, unlocked⟩, extended, fits, continued⟩ :=
    barrier.appendRetryLineage ready failure references last separate attempts
  exact ⟨uncertain, dropped, retained, unlocked,
    continued.reopensRetainedAppend ready failure.event extended fits failure.effects
      reopen descriptorEq acquired acquisition liveRefs fresh reads settles healthy⟩

/-- The cached worker uses the raw path reports for the selected checkpoint,
seals, and bounded keeper of the reached retry. -/
abbrev DelayedDirectorySync.CachedAppendReads {directory : DiskDirectory} {before : SegmentedWriterState}
    {descriptor : Nat} (failure : SegmentedAppendFailure directory before) (retry : LockedFileState FileImage)
    (reopen : BoundedReopenAttempt) (recover : EStateM IO.Error FileImage Reopened) : Prop :=
  ∀ history, ∀ selected : CanonicalKeeperLayout retry.image history,
    (history = before.history ∨ history = before.history ++ [failure.event]) →
    selected.target.first = before.wal.active.first →
    let wal := before.wal.appendSelectedView retry.image.directory.active history
    ∃ raw : HealthyBoundedWalReports directory (retry.owners.set (directory.file .lock) (some descriptor)) descriptor
        wal retry.image.directory.active selected.range.watermark before.published.durable selected.tail,
      ∃ sizes : SizedCheckpointRunReports directory raw.reports retry.image.directory.active.manifest before.published.durable,
        ∃ cached : CachedWalFileReports directory raw.reports wal selected.range.watermark selected.tail,
          recover = raw.reopenCached sizes cached reopen.removeFile reopen.write reopen.sync reopen.renameFile

/-- Following the same reported directory sync and retries, the cached
reader installs the exact surviving marker and strict checkpoint. -/
theorem DelayedDirectorySync.reopensRetainedAppendErrorCached
    {directory : DiskDirectory} {before : SegmentedWriterState} {writer descriptor : Nat}
    (barrier : DelayedDirectorySync directory) (ready : before.RetainedReady directory writer)
    (failure : SegmentedAppendFailure directory before)
    (references : HeldLockReferences writer) (last : references.remaining barrier.drops = [])
    (separate : barrier.captured.description ≠ writer) {retry : LockedFileState FileImage}
    (attempts : BoundedReopenTrace directory (AppendRetryTarget before.history failure.event before.wal.active.first)
      (barrier.after failure.released) retry)
    (reopen : BoundedReopenAttempt) (descriptorEq : reopen.descriptor = descriptor)
    (acquired : reopen.acquired = .ok true) (acquisition : TryLockObserves retry.owners directory (.ok true))
    (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < reopen.nextRef)
    (recover : EStateM IO.Error FileImage Reopened)
    (reads : CachedAppendReads (descriptor := descriptor) failure retry reopen recover)
    (settles : reopen.sync #[directory.path] retry.image = .ok () retry.image.syncDirectory)
    (healthy : ∀ history, ∀ selected : CanonicalKeeperLayout retry.image history,
      (history = before.history ∨ history = before.history ++ [failure.event]) →
      selected.target.first = before.wal.active.first →
      ∀ action prior next,
        ReachesAction selected.target retry.image.syncDirectory selected.plan.finishActions action prior →
        prior.effect selected.target action = some next →
        performPaths directory selected.plan reopen.removeFile throw reopen.write reopen.sync reopen.renameFile action prior =
          .ok () next) :
    barrier.AppendHandoff failure references last ∧
    ∃ after, AppendRetryEndpoint directory before failure.event retry descriptor
      (runOpenWithInstallation directory reopen.descriptor reopen.nextRef reopen.acquired reopen.unlock recover retry) after ∧
      after.RetainedReady directory descriptor ∧
      retry.image.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode after.history).size.toUInt64) ∧
      after.checkpoint = before.checkpoint ∧ after.installed.generation = before.installed.generation := by
  obtain ⟨handoff, extended, fits, continued⟩ := barrier.appendRetryLineage ready failure references last separate attempts
  refine ⟨handoff, continued.reopensRetainedAppendWith ready failure.event extended fits failure.effects
    reopen descriptorEq acquired acquisition liveRefs fresh recover ?_ settles healthy⟩
  intro history selected survived first wal layout valid checkpoint
  obtain ⟨raw, sizes, cached, reported⟩ := reads history selected survived first
  have chosen : wal.Selects retry.image.directory.active := List.mem_cons_self ..
  exact ⟨raw, reported.trans (raw.reopenCached_eq sizes cached layout valid chosen selected.decoded rfl
    selected.through checkpoint reopen.removeFile reopen.write reopen.sync reopen.renameFile)⟩

end Alvoki.Storage.DiskSession
