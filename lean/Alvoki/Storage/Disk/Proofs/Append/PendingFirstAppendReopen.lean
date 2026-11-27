import Alvoki.Storage.Disk.Proofs.Recovery.PendingClientReplay
import Alvoki.Storage.Disk.Proofs.Native.Recovery.NativeMarkedReadPrefix

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WAL.Boundary

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {checkpoint : Option (PackedTable × UInt64)}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {vacant : TryLockObserves retry.owners directory (.ok true)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}

/-- A stop during the first append leaves the earlier marker in charge
after process exit or power loss. The exact retained prefix is replayed
by the final healthy open, with replacement if the keeper is longer.
The same abstract history explains earlier reads and new guarded reads. -/
theorem SegmentedClientReadTrace.reopensInterruptedFirstAppend
    {directory : DiskDirectory} {first writer : Nat} {before : SegmentedWriterState}
    {bootstrap : EStateM.Result IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession}
    (start : BootstrapClientStart directory first bootstrap)
    (client : SegmentedClientReadTrace directory first start.writer allowCollection log recorded writer before)
    (request : WriteRequest) {report : BatchAppendInterruption directory before}
    (observed : report.Valid) (rows : request.rows = report.rows) (stage sync rename)
    (stop : report.Stop writer) {retry : LockedFileState FileImage}
    (retries : ReportedReopenPrefix directory before.wal.active.first stop.origin retry)
    (vacant : TryLockObserves retry.owners directory (.ok true))
    {input : FilePath} (inventory : DescriptorInventory)
    (observe : ∀ layout : CanonicalKeeperLayout retry.image before.history,
      BatchAppendInterruption.PreparedRetry before layout →
      ∀ selected : SelectedIntegrityCheckpoint before.published.durable
          retry.image.directory.active.manifest before.checkpoint,
        Nonempty (MarkedReadyOpenObservations input directory inventory retry layout before.published vacant selected)) :
    let reached := report.cut.writeFiles before.history (before.files.directory.staged .walBoundary)
    report.runRequestUntilAppend request stage sync rename =
      .error report.appendCall (.poisoned, ⟨reached, before.owners⟩) ∧
    BoundedReopenTrace directory (fun target => target = before.target)
      ⟨FirstAppendCut.projectReached before reached, before.owners⟩ retry ∧
    ∃ (layout : CanonicalKeeperLayout retry.image before.history)
      (selected : SelectedIntegrityCheckpoint before.published.durable
        retry.image.directory.active.manifest before.checkpoint)
      (observations : MarkedReadyOpenObservations input directory inventory retry layout before.published vacant selected)
      (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState),
      layout.target = before.target ∧
      observations.finish.run observations.chronology = .ok session (observations.finish.census, final) ∧
      final.image.directory.active = before.target.pair ∧
      session.directory = directory ∧ session.descriptor = observations.admission.owner.description ∧
      session.phase = .ready after.installed ∧
      after.files = final.image ∧ after.owners = final.owners ∧ after.RetainedReady directory session.descriptor ∧
      after.target = before.target ∧ after.history = before.history ∧ after.checkpoint = before.checkpoint ∧
      after.installed.generation = before.installed.generation ∧ after.published.durable = before.published.durable ∧
      after.wal.sealed = before.wal.sealed ∧
      observations.admission.owner ∈ observations.finish.census.slots ∧
      observations.admission.cached ∈ observations.finish.census.slots ∧
      observations.reads.reads.ObservesSelected directory retry.image.directory.active.manifest before.published.durable ∧
      CachedRetryInstalled (before := retry) observations.reads.walReads observations.admission.reached
        observations.admission.owner observations.reads.bindings before.published observations.callbacks.liveRefs
        (.ok session final) ∧
      recoverSelected (before.checkpoint.getD (.empty, 0)).1 (WAL.encode before.history) = .ok after.installed.table ∧
      InstalledClientReplay (log ++ [.uncertainBatch report.batch]) recorded before.history after.installed session ∧
      let state : NativeReadyState := ⟨session, after, observations.finish.census, observations.admission.cache,
        observations.admission.owner, observations.admission.cached⟩
      NativeReadyReadPrefix (observations.finish.run observations.chronology) state before.history
        (log ++ [.uncertainBatch report.batch]) recorded state := by
  dsimp only
  have beforeReady := (client.writes.preservesRetained (start.bootstrap.writerReady start.held).toRetained).1
  obtain ⟨_, _, attempts, pair, pending, layout, prepared⟩ :=
    client.replaysPendingFirstAppend start observed (observed.stopsBatchSchedule stage sync rename) stop retries
  have manifest := congrArg DirectoryPublication.Bindings.manifest pair
  have selected : SelectedIntegrityCheckpoint before.published.durable
      retry.image.directory.active.manifest before.checkpoint := manifest.symm ▸ beforeReady.resumed.selected
  have accepted : before.published.AcceptsVersioned before.history.length.toUInt64
      (CheckpointRepresentsPrefix before.history) retry.image.directory.active.manifest :=
    manifest.symm ▸ beforeReady.resumed.accepted
  obtain ⟨observations⟩ := observe layout prepared selected
  obtain ⟨session, final, returned, samePair, owner, cached, installed⟩ :=
    observations.finish.installsFromCensus observations.chronology observations.markerFound prepared.prepared.newer
      (observations.reads.walReads.selectedAfterWatermark prepared.offsets prepared.descriptors)
      accepted beforeReady.resumed.ordered
  obtain ⟨actual, reached, ready, checkpoint, indexed, phase, loaded, recovered, refined⟩ :=
    CachedRetryInstalled.refinesPendingClient installed pending
  obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj indexed
  obtain ⟨_, appendReady⟩ := CachedRetryInstalled.readyForAppend installed accepted beforeReady.resumed.ordered
  have visible : before.wal.directory.active = layout.target.pair :=
    beforeReady.walPair.trans (congrArg Target.pair prepared.target).symm
  obtain ⟨nextSession, nextFinal, after, exactReturn, path, lock, nextPhase, files, owners,
    wal, target, history, _, durable, nextReady⟩ :=
    appendReady.writerRetained beforeReady.layout beforeReady.valid beforeReady.spans visible prepared.first
      (prepared.kept.trans beforeReady.sealedFiles)
  obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj exactReturn
  have sameInstalled := Phase.ready.inj (phase.symm.trans nextPhase)
  subst ready
  have sameTarget := target.trans prepared.target
  have restored := nextReady.resumed.selected
  rw [sameTarget, durable] at restored
  have sameCheckpoint := restored.uniqueResult beforeReady.resumed.selected
  have generation : after.installed.generation = before.installed.generation := by
    rw [nextReady.resumed.generation, sameCheckpoint, ← beforeReady.resumed.generation]
  have sealed : after.wal.sealed = before.wal.sealed := by rw [wal]
  let state : NativeReadyState := ⟨session, after, observations.finish.census, observations.admission.cache,
    observations.admission.owner, observations.admission.cached⟩
  have exactFiles : state.files = final := by
    change (⟨after.files, after.owners⟩ : LockedFileState FileImage) = final
    rw [files, owners]
  have valid : state.Valid := ⟨nextPhase, lock.symm, owner, cached, ⟨observations.admission.reached, rfl⟩,
    path.symm ▸ lock.symm ▸ nextReady⟩
  have continued : NativeReadyReadPrefix (observations.finish.run observations.chronology)
      state before.history (log ++ [.uncertainBatch report.batch]) recorded state :=
    .installed (exactFiles.symm ▸ returned) valid history pending
      (client.responsesBounded (start.bootstrap.writerReady start.held).toRetained)
  exact ⟨observed.stopsWriteRequest request rows stage sync rename, attempts, layout, selected, observations, session,
    final, after, prepared.target, returned, samePair.trans pair, path, lock, nextPhase, files, owners,
    lock.symm ▸ nextReady, sameTarget, history, sameCheckpoint, generation, durable, sealed,
    owner, cached, observations.reads.chunkReads, installed, loaded.uniqueResult selected ▸ recovered, refined, continued⟩

end Alvoki.Storage.DiskSession
