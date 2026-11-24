import Alvoki.Storage.Disk.RetainedWriterReopen
import Alvoki.Storage.Disk.SegmentedAppendRecovery

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WalSegmentCommit WAL.Boundary
open WAL (frameSize)

/-- Install from the reached append lineage using a recovery action that
matches the bounded reports for the files selected by the visible marker. -/
theorem _root_.Alvoki.Storage.WalSegmentRepair.ReopenLineage.reopensRetainedAppendWith
    {directory : DiskDirectory} {before : SegmentedWriterState}
    {writer descriptor : Nat} (ready : before.RetainedReady directory writer)
    (event : WAL.Write) (extended : WAL.OrdinalsFrom 1 (before.history ++ [event]))
    (fits : (WAL.encode (before.history ++ [event])).size < UInt64.size) (effects : WriteEffects)
    {retry : LockedFileState FileImage}
    (lineage : ReopenLineage (appendCutFiles before.wal before.history event effects before.files.keeper.staged)
      (AppendRetryTarget before.history event before.wal.active.first) retry.image)
    (reopen : BoundedReopenAttempt) (descriptorEq : reopen.descriptor = descriptor)
    (acquired : reopen.acquired = .ok true) (acquisition : TryLockObserves retry.owners directory (.ok true))
    (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < reopen.nextRef)
    (recover : EStateM IO.Error FileImage Reopened)
    (reads : ∀ history, ∀ selected : CanonicalKeeperLayout retry.image history,
      (history = before.history ∨ history = before.history ++ [event]) → selected.target.first = before.wal.active.first →
      let wal := before.wal.appendSelectedView retry.image.directory.active history
      wal.ReadLayout history → wal.Valid history →
      SelectedIntegrityCheckpoint before.published.durable retry.image.directory.active.manifest before.checkpoint →
      ∃ raw : HealthyBoundedWalReports directory (retry.owners.set (directory.file .lock) (some descriptor)) descriptor
          wal retry.image.directory.active selected.range.watermark before.published.durable selected.tail,
        recover = raw.reopen reopen.removeFile reopen.write reopen.sync reopen.renameFile)
    (settles : reopen.sync #[directory.path] retry.image = .ok () retry.image.syncDirectory)
    (healthy : ∀ history, ∀ layout : CanonicalKeeperLayout retry.image history,
      (history = before.history ∨ history = before.history ++ [event]) → layout.target.first = before.wal.active.first →
      ∀ action prior next,
        ReachesAction layout.target retry.image.syncDirectory layout.plan.finishActions action prior →
        prior.effect layout.target action = some next →
        performPaths directory layout.plan reopen.removeFile throw reopen.write reopen.sync reopen.renameFile action prior =
          .ok () next) :
    ∃ after, AppendRetryEndpoint directory before event retry descriptor
      (runOpenWithInstallation directory reopen.descriptor reopen.nextRef reopen.acquired reopen.unlock recover retry) after ∧
      after.RetainedReady directory descriptor ∧
      retry.image.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode after.history).size.toUInt64) ∧
      after.checkpoint = before.checkpoint ∧ after.installed.generation = before.installed.generation := by
  have range : before.wal.directory.active.walRange = some ⟨before.target.range.watermark, before.history.length⟩ := by
    rw [ready.walPair, ← ready.resumed.through]
    exact before.target.decoded
  have accepted : before.published.AcceptsVersioned before.history.length.toUInt64
      (CheckpointRepresentsPrefix before.history) before.wal.directory.active.manifest :=
    (congrArg DirectoryPublication.Bindings.manifest ready.walPair).symm ▸ ready.resumed.accepted
  have generationRead : ((before.wal.directory.active.manifest.mapM fun bytes =>
      (Manifest.IntegrityCheckpoint.decode bytes).map (·.header.generation)).map (·.getD 0) : Except String UInt64) =
      .ok before.installed.generation := by
    rw [ready.walPair]
    exact ready.resumed.generationRead
  obtain ⟨_, history, survived, manifest, marker, wal, walEq, layout, valid, kept, selected, first, keeper, opened⟩ :=
    lineage.installsAfterRetainedAppendCut (descriptor := descriptor) ready.layout ready.valid range ready.resumed.ordered
      accepted generationRead event extended fits effects before.files.keeper.staged liveRefs fresh acquisition
      reopen.unlock reopen.removeFile reopen.write reopen.sync reopen.renameFile
  subst wal
  have selectedManifest := manifest.trans (congrArg DirectoryPublication.Bindings.manifest ready.walPair)
  have oldCheckpoint : SelectedIntegrityCheckpoint before.published.durable retry.image.directory.active.manifest
      before.checkpoint := selectedManifest.symm ▸ ready.resumed.selected
  obtain ⟨raw, exactRead⟩ := reads history selected survived first layout valid oldCheckpoint
  obtain ⟨session, final, after, returned, path, acquiredDescriptor, phase, files, owners, actualWal, target,
    exactHistory, generation, durable, next⟩ := (opened raw settles (healthy history selected survived first)).writerRetained
      layout valid ready.spans rfl keeper kept
  have actualResult : runOpenWithInstallation directory reopen.descriptor reopen.nextRef reopen.acquired
      reopen.unlock recover retry = .ok session final := by
    rw [descriptorEq, acquired, exactRead]
    exact returned
  have afterWal : after.wal = { before.wal.appendSelectedView retry.image.directory.active after.history with
      directory := after.files.directory } := by rw [actualWal, files, exactHistory]
  have loaded := next.resumed.selected
  rw [durable, target] at loaded
  have checkpoint := Except.ok.inj ((raw.readCheckpoint loaded).symm.trans (raw.readCheckpoint oldCheckpoint))
  refine ⟨after, ⟨⟨session, final, actualResult, path, acquiredDescriptor, phase, files, owners⟩,
    exactHistory ▸ survived, afterWal, target ▸ rfl, ?_, next.resumed.through, next.resumed.contents, durable,
    next.manifestFiles, next.resumed.selected⟩, next, exactHistory.symm ▸ marker, checkpoint, generation⟩
  rw [target]
  exact first

/-- The bounded prefix-reader attempt is one instance of append-cut
recovery. Its reported marker chooses the old or extended history. -/
theorem _root_.Alvoki.Storage.WalSegmentRepair.ReopenLineage.reopensRetainedAppend
    {directory : DiskDirectory} {before : SegmentedWriterState}
    {writer descriptor : Nat} (ready : before.RetainedReady directory writer)
    (event : WAL.Write) (extended : WAL.OrdinalsFrom 1 (before.history ++ [event]))
    (fits : (WAL.encode (before.history ++ [event])).size < UInt64.size) (effects : WriteEffects)
    {retry : LockedFileState FileImage}
    (lineage : ReopenLineage (appendCutFiles before.wal before.history event effects before.files.keeper.staged)
      (AppendRetryTarget before.history event before.wal.active.first) retry.image)
    (reopen : BoundedReopenAttempt) (descriptorEq : reopen.descriptor = descriptor)
    (acquired : reopen.acquired = .ok true) (acquisition : TryLockObserves retry.owners directory (.ok true))
    (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < reopen.nextRef)
    (reads : ∀ history, ∀ layout : CanonicalKeeperLayout retry.image history,
      (history = before.history ∨ history = before.history ++ [event]) → layout.target.first = before.wal.active.first →
      let wal := before.wal.appendSelectedView retry.image.directory.active history
      ∃ raw : HealthyBoundedWalReports directory (retry.owners.set (directory.file .lock) (some descriptor)) descriptor
          wal retry.image.directory.active layout.range.watermark before.published.durable layout.tail,
        reopen.recover directory = raw.reopen reopen.removeFile reopen.write reopen.sync reopen.renameFile)
    (settles : reopen.sync #[directory.path] retry.image = .ok () retry.image.syncDirectory)
    (healthy : ∀ history, ∀ layout : CanonicalKeeperLayout retry.image history,
      (history = before.history ∨ history = before.history ++ [event]) → layout.target.first = before.wal.active.first →
      ∀ action prior next,
        ReachesAction layout.target retry.image.syncDirectory layout.plan.finishActions action prior →
        prior.effect layout.target action = some next →
        performPaths directory layout.plan reopen.removeFile throw reopen.write reopen.sync reopen.renameFile action prior =
          .ok () next) :
    ∃ after, AppendRetryEndpoint directory before event retry descriptor (reopen.run directory retry) after ∧
      after.RetainedReady directory descriptor ∧
      retry.image.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode after.history).size.toUInt64) ∧
      after.checkpoint = before.checkpoint ∧ after.installed.generation = before.installed.generation :=
  lineage.reopensRetainedAppendWith ready event extended fits effects reopen descriptorEq acquired acquisition
    liveRefs fresh (reopen.recover directory)
    (fun history selected survived first _ _ _ => reads history selected survived first) settles healthy

/-- The exact bounded opener and its primitive observations install the
retained form of the writer invariant from a physical append cut. The old
or extended history is chosen by the visible marker. -/
theorem BoundedReopenTrace.reopensRetainedAppend {directory : DiskDirectory} {before : SegmentedWriterState}
    {writer descriptor : Nat} (ready : before.RetainedReady directory writer)
    (event : WAL.Write) (extended : WAL.OrdinalsFrom 1 (before.history ++ [event]))
    (fits : (WAL.encode (before.history ++ [event])).size < UInt64.size) (effects : WriteEffects)
    {owners : LockOwners} {retry : LockedFileState FileImage}
    (attempts : BoundedReopenTrace directory (AppendRetryTarget before.history event before.wal.active.first)
      ⟨appendCutFiles before.wal before.history event effects before.files.keeper.staged, owners⟩ retry)
    (reopen : BoundedReopenAttempt) (descriptorEq : reopen.descriptor = descriptor)
    (acquired : reopen.acquired = .ok true) (acquisition : TryLockObserves retry.owners directory (.ok true))
    (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < reopen.nextRef)
    (reads : ∀ history, ∀ layout : CanonicalKeeperLayout retry.image history,
      (history = before.history ∨ history = before.history ++ [event]) → layout.target.first = before.wal.active.first →
      let wal := before.wal.appendSelectedView retry.image.directory.active history
      ∃ raw : HealthyBoundedWalReports directory (retry.owners.set (directory.file .lock) (some descriptor)) descriptor
          wal retry.image.directory.active layout.range.watermark before.published.durable layout.tail,
        reopen.recover directory = raw.reopen reopen.removeFile reopen.write reopen.sync reopen.renameFile)
    (settles : reopen.sync #[directory.path] retry.image = .ok () retry.image.syncDirectory)
    (healthy : ∀ history, ∀ layout : CanonicalKeeperLayout retry.image history,
      (history = before.history ∨ history = before.history ++ [event]) → layout.target.first = before.wal.active.first →
      ∀ action prior next,
        ReachesAction layout.target retry.image.syncDirectory layout.plan.finishActions action prior →
        prior.effect layout.target action = some next →
        performPaths directory layout.plan reopen.removeFile throw reopen.write reopen.sync reopen.renameFile action prior =
          .ok () next) :
    ∃ after, AppendRetryEndpoint directory before event retry descriptor (reopen.run directory retry) after ∧
      after.RetainedReady directory descriptor ∧
      retry.image.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode after.history).size.toUInt64) ∧
      after.checkpoint = before.checkpoint ∧ after.installed.generation = before.installed.generation :=
  (attempts.lineage (fun a b pair => AppendRetryTarget.unique a b pair)).reopensRetainedAppend
    ready event extended fits effects reopen descriptorEq acquired acquisition liveRefs fresh reads settles healthy

/-- A reported commit error fixes the physical append cut and bounds
the possible extended history by the submitted record. -/
theorem SegmentedAppendFailure.retainedCut {directory : DiskDirectory} {before : SegmentedWriterState}
    {writer : Nat} (failure : SegmentedAppendFailure directory before) (ready : before.RetainedReady directory writer) :
    WAL.OrdinalsFrom 1 (before.history ++ [failure.event]) ∧
      (WAL.encode (before.history ++ [failure.event])).size < UInt64.size ∧
      appendCutFiles before.wal before.history failure.event failure.effects before.files.keeper.staged =
        failure.released.image := by
  obtain ⟨model, refined, represented⟩ := ready.resumed.canonical
  have count : before.history.length = before.installed.table.committed.toNat :=
    represented.committed_count.symm.trans (congrArg UInt64.toNat refined.committed).symm
  obtain ⟨_, _, extended, _, size⟩ := prepareWrite_extends_history ready.resumed.ordered count failure.prepared
  have byteCount : before.installed.walBytes + frameSize = (WAL.encode (before.history ++ [failure.event])).size := by
    rw [ready.resumed.bytes, size]
  have modeled := failure.reports.run byteCount
  rw [forgetError, failure.ran] at modeled
  have exactCut : writeFilesAfter (runWriteEffects before.history failure.event failure.effects
      (before.wal.directory.staged .walBoundary)) = failure.failed := by rw [← modeled]; rfl
  exact ⟨extended, byteCount ▸ failure.fits, by simp [appendCutFiles, SegmentedAppendFailure.released, exactCut]⟩

namespace SegmentedAppendRecoveryReport

variable {directory : DiskDirectory} {before : SegmentedWriterState} {writer descriptor : Nat}

/-- The real reported publication error poisons and releases the old
writer. Bounded recovery then installs the exact retained writer. -/
theorem installsRetained (report : SegmentedAppendRecoveryReport directory before writer descriptor)
    (ready : before.RetainedReady directory writer) :
    ∃ after, report.Installs after ∧ after.RetainedReady directory descriptor := by
  let failure := report.failure
  let initial := WriteFiles.initial before.history (before.wal.directory.staged .walBoundary)
  let proposed : Installed := { before.installed with table := failure.table, walBytes := before.installed.walBytes + frameSize }
  obtain ⟨uncertain, closed, dropped, _⟩ := runPreparedWrite_failure_handoff
    (before := ⟨initial, before.owners⟩) before.installed proposed failure.event.sequence failure.ran ready.held
  obtain ⟨extended, fits, exactCut⟩ := failure.retainedCut ready
  have attempts : BoundedReopenTrace directory (AppendRetryTarget before.history failure.event before.wal.active.first)
      ⟨appendCutFiles before.wal before.history failure.event failure.effects before.files.keeper.staged,
        before.owners.set (directory.file .lock) none⟩ report.retry := by
    rw [exactCut]
    exact report.attempts
  obtain ⟨after, endpoint, installed, _, _, _⟩ := attempts.reopensRetainedAppend
    ready failure.event extended fits failure.effects report.reopen report.descriptorEq
    report.acquired report.acquisition report.liveRefs report.fresh report.reads report.settles report.healthy
  have release : report.release.Observed (directory := directory) failure.poisoned
      ⟨failure.failed, before.owners.set (directory.file .lock) none⟩ := by
    cases report.release with
    | closed => exact closed
    | references held drops last => exact dropped held drops last
  exact ⟨after, ⟨endpoint, uncertain, release⟩, installed⟩

theorem Installs.preservesRetained {report : SegmentedAppendRecoveryReport directory before writer descriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after)
    (ready : before.RetainedReady directory writer) : after.RetainedReady directory descriptor := by
  obtain ⟨_, installed, retained⟩ := report.installsRetained ready
  exact installed.unique endpoint ▸ retained

end SegmentedAppendRecoveryReport

end Alvoki.Storage.DiskSession
