import Alvoki.Storage.Disk.CapturedAlignedInstallation
import Alvoki.Storage.Disk.PendingClientReplay
import Alvoki.Storage.Disk.BatchInterruptionDispatch

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

/-- Primitive reports for a healthy aligned attempt after the earlier
lock description has retired. The prepared layout selects the exact
checkpoint and WAL operands for this attempt. -/
structure AlignedRecoveryObservations (input : FilePath) (directory : DiskDirectory)
    (inventory : DescriptorInventory) (retry : LockedFileState FileImage)
    (retired lockInode : Nat) {history : List WAL.Write} (layout : CanonicalKeeperLayout retry.image history)
    (published : CheckpointPublication.Image) (vacant : TryLockObserves retry.owners directory (.ok true))
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint) where
  admission : CensusOpenAdmissionReports input directory inventory retry
  ownerFresh : admission.owner.description ≠ retired
  directoryFresh : admission.cached.description ≠ retired
  lockObject : inventory.inode admission.owner.description = lockInode
  callbacks : CapturedAlignedCallbacks admission
  reads : CapturedMarkedReadReports admission layout published
  finish : CapturedAlignedFinish callbacks reads vacant selected
  marker : IO.FS.Metadata
  markerFound : admission.lookup (directory.file .walBoundary) (admission.reached, admission.held) =
    .ok (.ok marker) (admission.reached, admission.held)
  following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
    layout.range.watermark < start

/-- The installed session and its disk observations use the same
selected history as the pending client log. -/
abbrev AlignedClientReopened
    {directory : DiskDirectory} (input : FilePath) (inventory : DescriptorInventory)
    (retry : LockedFileState FileImage) (retired lockInode : Nat) (before : SegmentedWriterState)
    (batch : List WAL.Write) (log : List DatabaseSubmissions) (reads : List RecordedSnapshotRead)
    (vacant : TryLockObserves retry.owners directory (.ok true)) : Prop :=
  ∃ (history : List WAL.Write) (layout : CanonicalKeeperLayout retry.image history)
    (selected : SelectedIntegrityCheckpoint before.published.durable
      retry.image.directory.active.manifest before.checkpoint)
    (openReports : AlignedRecoveryObservations input directory inventory retry retired lockInode
      layout before.published vacant selected)
    (session : SegmentedSession) (final : LockedFileState FileImage) (ready : Installed),
    (history = before.history ∨ history = before.history ++ batch) ∧
    openReports.finish.run = .ok session (openReports.finish.census, final) ∧
    session.phase = .ready ready ∧
    openReports.reads.reads.ObservesSelected directory retry.image.directory.active.manifest before.published.durable ∧
    openReports.reads.bindings (directory.file .lock) = some lockInode ∧
    openReports.admission.owner ∈ openReports.finish.census.slots ∧
    openReports.admission.cached ∈ openReports.finish.census.slots ∧
    recoverSelected (before.checkpoint.getD (.empty, 0)).1 (WAL.encode history) = .ok ready.table ∧
    InstalledClientReplay (log ++ [.uncertainBatch batch]) reads history ready session

/-- Both write outcomes derive the selected checkpoint before their common
aligned finish. Its reported callbacks instantiate the exact same replay. -/
private theorem installSelectedAligned
    {directory : DiskDirectory} {writer : Nat} {before : SegmentedWriterState}
    (beforeReady : before.RetainedReady directory writer)
    {batch history : List WAL.Write} {log : List DatabaseSubmissions} {reads : List RecordedSnapshotRead}
    (allowed : history = before.history ∨ history = before.history ++ batch)
    (ordered : WAL.OrdinalsFrom 1 history)
    (fits : (WAL.encode (before.history ++ batch)).size < UInt64.size)
    (pending : PendingClientReplay (log ++ [.uncertainBatch batch]) reads history)
    {origin source retry : LockedFileState FileImage}
    {initial inventory : DescriptorInventory}
    (earlier : ReportedReopenPrefix directory before.wal.active.first origin source)
    (census : LockCensusTrace directory writer initial source inventory retry)
    (last : inventory.references writer = [])
    (manifest : retry.image.directory.active.manifest = before.wal.directory.active.manifest)
    (layout : CanonicalKeeperLayout retry.image history)
    (prepared : Prepared retry.image layout.target layout.plan)
    {input : FilePath}
    (observe : ∀ selected : SelectedIntegrityCheckpoint before.published.durable
        retry.image.directory.active.manifest before.checkpoint,
      Nonempty (AlignedRecoveryObservations input directory inventory retry writer (initial.inode writer)
        layout before.published (census.freshFlockAllowed.mpr last) selected)) :
    AlignedClientReopened input inventory retry writer (initial.inode writer) before batch log reads
      (census.freshFlockAllowed.mpr last) := by
  have sameManifest := manifest.trans (congrArg DirectoryPublication.Bindings.manifest beforeReady.walPair)
  have priorCheckpoint : SelectedIntegrityCheckpoint before.published.durable
      retry.image.directory.active.manifest before.checkpoint :=
    sameManifest.symm ▸ beforeReady.resumed.selected
  have priorAccepted : before.published.AcceptsVersioned before.history.length.toUInt64
      (CheckpointRepresentsPrefix before.history) retry.image.directory.active.manifest :=
    sameManifest.symm ▸ beforeReady.resumed.accepted
  have accepted : before.published.AcceptsVersioned history.length.toUInt64
      (CheckpointRepresentsPrefix history) retry.image.directory.active.manifest := by
    rcases allowed with rfl | rfl
    · exact priorAccepted
    · exact CheckpointPublication.Image.acceptsVersioned_extend_history priorAccepted fits
  obtain ⟨openReports⟩ := observe priorCheckpoint
  obtain ⟨_, lockObject, session, final, opened, liveOwner, liveDirectory, _, _, physicalReads, installed⟩ :=
    openReports.finish.installs census earlier last openReports.ownerFresh openReports.directoryFresh
      openReports.lockObject openReports.markerFound prepared.keeperPrefix prepared.newer openReports.following
      accepted ordered
  obtain ⟨actualSession, actualFinal, ready, checkpoint, same, phase, selected, recovered, refined⟩ :=
    CachedRetryInstalled.refinesPendingClient installed pending
  obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj same
  have sameCheckpoint := selected.uniqueResult priorCheckpoint
  exact ⟨history, layout, priorCheckpoint, openReports, session, final, ready, allowed, opened,
    phase, physicalReads, lockObject, liveOwner, liveDirectory, sameCheckpoint ▸ recovered, refined⟩

/-- A reported uncertain write keeps the old owner and the reached bytes.
The chronological retry prefix and descriptor census determine which
history the succeeding aligned open will use. The same history explains
both the earlier responses and the guarded reads of the returned session. -/
theorem SegmentedClientReadTrace.reopensReturnedWriteAligned
    {handle : Type} {directory : DiskDirectory} {first writer : Nat} {before : SegmentedWriterState}
    {bootstrap : EStateM.Result IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession}
    (start : BootstrapClientStart directory first bootstrap)
    (client : SegmentedClientReadTrace directory first start.writer allowCollection log reads writer before)
    (request : WriteRequest) (failure : SegmentedBatchFailure directory before)
    (reported : ObservedBatchFailure failure handle) (rows : request.rows = failure.rows)
    {source retry : LockedFileState FileImage}
    (earlier : ReportedReopenPrefix directory before.wal.active.first ⟨failure.released.image, before.owners⟩ source)
    {initial inventory : DescriptorInventory}
    (census : LockCensusTrace directory writer initial source inventory retry)
    (last : inventory.references writer = [])
    {input : FilePath}
    (observe : ∀ history, ∀ layout : CanonicalKeeperLayout retry.image history,
      (history = before.history ∨ history = before.history ++ failure.batch) →
      Prepared retry.image layout.target layout.plan →
      ∀ selected : SelectedIntegrityCheckpoint before.published.durable
          retry.image.directory.active.manifest before.checkpoint,
        Nonempty (AlignedRecoveryObservations input directory inventory retry writer (initial.inode writer)
          layout before.published (census.freshFlockAllowed.mpr last) selected)) :
    ∃ cacheAfter, (WriteRequest.Calls.ofFailure reported).run request directory before =
      .error (.commitUnknown failure.cause) (.poisoned, ⟨(cacheAfter, failure.failed), before.owners⟩) ∧
    AlignedClientReopened input inventory retry writer (initial.inode writer) before failure.batch log reads
      (census.freshFlockAllowed.mpr last) := by
  have beforeReady := (client.writes.preservesRetained (start.bootstrap.writerReady start.held).toRetained).1
  have retries := census.reopenTrace earlier
  obtain ⟨cacheAfter, returned, _, manifest, history, allowed, _, pending, layout, _, prepared⟩ :=
    client.replaysPendingWriteError start request failure reported rows retries
  obtain ⟨_, refined, represented⟩ := beforeReady.resumed.canonical
  have count : before.history.length = before.installed.table.committed.toNat :=
    represented.committed_count.symm.trans (congrArg UInt64.toNat refined.committed).symm
  have extended := prepareBatch_extends_history beforeReady.resumed.ordered count failure.prepared
  have fits := (failure.retainedCut beforeReady).1
  have ordered : WAL.OrdinalsFrom 1 history := by
    rcases allowed with rfl | rfl
    · exact beforeReady.resumed.ordered
    · exact extended.2.1
  exact ⟨cacheAfter, returned, installSelectedAligned beforeReady allowed ordered fits pending
    earlier census last manifest layout prepared (observe history layout allowed prepared)⟩

/-- The same aligned open also handles an invocation interrupted in
marker publication. The old owner and exact reached marker files start
the retry prefix, with no ordinary response from the interrupted call. -/
theorem SegmentedClientReadTrace.reopensInterruptedMarkerAligned
    {directory : DiskDirectory} {first writer : Nat} {before : SegmentedWriterState}
    {bootstrap : EStateM.Result IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession}
    (start : BootstrapClientStart directory first bootstrap)
    (client : SegmentedClientReadTrace directory first start.writer allowCollection log reads writer before)
    (request : WriteRequest) {cut : SegmentedBatchMarkerPowerLossReport directory before writer}
    (observed : cut.Reached) (rows : request.rows = cut.rows)
    {source retry : LockedFileState FileImage}
    (earlier : ReportedReopenPrefix directory before.wal.active.first cut.inFlight source)
    {initial inventory : DescriptorInventory}
    (census : LockCensusTrace directory writer initial source inventory retry)
    (last : inventory.references writer = [])
    {input : FilePath}
    (observe : ∀ history, ∀ layout : CanonicalKeeperLayout retry.image history,
      (history = before.history ∨ history = before.history ++ cut.batch) →
      Prepared retry.image layout.target layout.plan →
      ∀ selected : SelectedIntegrityCheckpoint before.published.durable
          retry.image.directory.active.manifest before.checkpoint,
        Nonempty (AlignedRecoveryObservations input directory inventory retry writer (initial.inode writer)
          layout before.published (census.freshFlockAllowed.mpr last) selected)) :
    let scratch := before.wal.directory.staged .walBoundary
    request.runWithInterruption directory cut.activeMetadata cut.publishUntilIssue
      (.ready before.installed, ⟨WAL.Boundary.WriteFiles.initial before.history scratch, before.owners⟩) =
      .error cut.cut.action
        (.poisoned, ⟨cut.cut.interrupt (WAL.Boundary.encode cut.nextBytes.toUInt64) cut.reached, before.owners⟩) ∧
    cut.inFlight = ⟨before.wal.appendReopenFiles
      ((cut.cut.interrupt (WAL.Boundary.encode cut.nextBytes.toUInt64) cut.reached).reopenImage
        (before.history.drop before.wal.active.first) before.wal.directory.active.manifest
        (before.wal.directory.staged .manifest) before.files.keeper.staged)
      before.files.keeper.staged, before.owners⟩ ∧
    AlignedClientReopened input inventory retry writer (initial.inode writer) before cut.batch log reads
      (census.freshFlockAllowed.mpr last) := by
  dsimp only
  have beforeReady := (client.writes.preservesRetained (start.bootstrap.writerReady start.held).toRetained).1
  have retries := census.reopenTrace earlier
  obtain ⟨_, manifest, history, allowed, _, pending, layout, _, prepared⟩ :=
    client.replaysPendingBatchMarker start observed retries
  have actual := observed.preparedHistory beforeReady
  have ordered : WAL.OrdinalsFrom 1 history := by
    rcases allowed with rfl | rfl
    · exact beforeReady.resumed.ordered
    · exact actual.2.2
  refine ⟨observed.stopsWriteRequest request rows, ?_,
    installSelectedAligned beforeReady allowed ordered actual.2.1 pending earlier census last manifest layout
      prepared (observe history layout allowed prepared)⟩
  simp only [SegmentedBatchMarkerPowerLossReport.inFlight, SegmentedBatchMarkerPowerLossReport.physical, actual.1]

end Alvoki.Storage.DiskSession
