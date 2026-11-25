import Alvoki.Storage.Disk.PendingClientReplay
import Alvoki.Storage.Disk.CapturedLongKeeperInstallation

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WAL.Boundary

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {checkpoint : Option (PackedTable × UInt64)}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {vacant : TryLockObserves retry.owners directory (.ok true)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}

/-- An interrupted append can leave an aligned keeper or a physical tail.
Both healthy finishes with no later names use the same captured reads. -/
inductive CapturedKeeperFinish (calls : CapturedAlignedCallbacks admission)
    (reads : CapturedMarkedReadReports admission layout published)
    (vacant : TryLockObserves retry.owners directory (.ok true))
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint) where
  | aligned (finish : CapturedAlignedFinish calls reads vacant selected)
  | longer (finish : CapturedLongKeeperFinish calls reads vacant selected)

namespace CapturedKeeperFinish

variable {calls : CapturedAlignedCallbacks admission} {reads : CapturedMarkedReadReports admission layout published}

noncomputable def run : CapturedKeeperFinish calls reads vacant selected →
    EStateM.Result IO.Error CensusOpenState SegmentedSession
  | .aligned finish => finish.run
  | .longer finish => finish.run

noncomputable def census : CapturedKeeperFinish calls reads vacant selected → DescriptorInventory
  | .aligned finish => finish.census
  | .longer finish => finish.census

theorem installsAfterVacancy (finish : CapturedKeeperFinish calls reads vacant selected)
    {metadata : IO.FS.Metadata}
    (marker : admission.lookup (directory.file .walBoundary) (admission.reached, admission.held) =
      .ok (.ok metadata) (admission.reached, admission.held))
    (prepared : Prepared retry.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    ∃ session final, finish.run = .ok session (finish.census, final) ∧
      final.image.directory.active = retry.image.directory.active ∧
      admission.owner ∈ finish.census.slots ∧ admission.cached ∈ finish.census.slots ∧
      CachedRetryInstalled (before := retry) reads.walReads admission.reached admission.owner reads.bindings
        published calls.liveRefs (.ok session final) := by
  cases finish with
  | aligned finish =>
    obtain ⟨session, final, returned, pair, installed⟩ :=
      finish.installsAfterVacancy marker prepared.keeperPrefix prepared.newer following accepted ordered
    exact ⟨session, final, returned, pair, finish.lockRetained, finish.directoryRetained, installed⟩
  | longer finish =>
    obtain ⟨session, returned, pair, installed⟩ :=
      finish.installsAfterVacancy marker prepared.keeperPrefix prepared.newer following accepted ordered
    exact ⟨session, finish.settled, returned, pair, finish.lockRetained, finish.directoryRetained, installed⟩

end CapturedKeeperFinish

/-- Reports for the final healthy held open. The retry prefix supplies the
physical image and selects the checkpoint before these reports are used. -/
structure FirstAppendReopenObservations (input : FilePath) (directory : DiskDirectory)
    (inventory : DescriptorInventory) (retry : LockedFileState FileImage)
    {history : List WAL.Write} (layout : CanonicalKeeperLayout retry.image history)
    (published : CheckpointPublication.Image) (vacant : TryLockObserves retry.owners directory (.ok true))
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint) where
  admission : CensusOpenAdmissionReports input directory inventory retry
  callbacks : CapturedAlignedCallbacks admission
  reads : CapturedMarkedReadReports admission layout published
  finish : CapturedKeeperFinish callbacks reads vacant selected
  marker : IO.FS.Metadata
  markerFound : admission.lookup (directory.file .walBoundary) (admission.reached, admission.held) =
    .ok (.ok marker) (admission.reached, admission.held)
  following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
    layout.range.watermark < start

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
        Nonempty (FirstAppendReopenObservations input directory inventory retry layout before.published vacant selected)) :
    let reached := report.cut.writeFiles before.history (before.files.directory.staged .walBoundary)
    report.runRequestUntilAppend request stage sync rename =
      .error report.appendCall (.poisoned, ⟨reached, before.owners⟩) ∧
    BoundedReopenTrace directory (fun target => target = before.target)
      ⟨FirstAppendCut.projectReached before reached, before.owners⟩ retry ∧
    ∃ (layout : CanonicalKeeperLayout retry.image before.history)
      (selected : SelectedIntegrityCheckpoint before.published.durable
        retry.image.directory.active.manifest before.checkpoint)
      (observations : FirstAppendReopenObservations input directory inventory retry layout before.published vacant selected)
      (session : SegmentedSession) (final : LockedFileState FileImage) (ready : Installed),
      layout.target = before.target ∧
      observations.finish.run = .ok session (observations.finish.census, final) ∧
      final.image.directory.active = before.target.pair ∧
      session.phase = .ready ready ∧
      observations.admission.owner ∈ observations.finish.census.slots ∧
      observations.admission.cached ∈ observations.finish.census.slots ∧
      observations.reads.reads.ObservesSelected directory retry.image.directory.active.manifest before.published.durable ∧
      CachedRetryInstalled (before := retry) observations.reads.walReads observations.admission.reached
        observations.admission.owner observations.reads.bindings before.published observations.callbacks.liveRefs
        (.ok session final) ∧
      recoverSelected (before.checkpoint.getD (.empty, 0)).1 (WAL.encode before.history) = .ok ready.table ∧
      InstalledClientReplay (log ++ [.uncertainBatch report.batch]) recorded before.history ready session := by
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
    observations.finish.installsAfterVacancy observations.markerFound prepared.prepared observations.following
      accepted beforeReady.resumed.ordered
  obtain ⟨actual, reached, ready, checkpoint, indexed, phase, loaded, recovered, refined⟩ :=
    CachedRetryInstalled.refinesPendingClient installed pending
  obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj indexed
  exact ⟨observed.stopsWriteRequest request rows stage sync rename, attempts, layout, selected, observations, session,
    final, ready, prepared.target, returned, samePair.trans pair, phase, owner, cached, observations.reads.chunkReads, installed,
    loaded.uniqueResult selected ▸ recovered, refined⟩

end Alvoki.Storage.DiskSession
