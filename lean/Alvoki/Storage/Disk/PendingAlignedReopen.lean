import Alvoki.Storage.Disk.CapturedAlignedInstallation
import Alvoki.Storage.Disk.PendingClientReplay

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
    ∃ (history : List WAL.Write) (layout : CanonicalKeeperLayout retry.image history)
      (selected : SelectedIntegrityCheckpoint before.published.durable
        retry.image.directory.active.manifest before.checkpoint)
      (openReports : AlignedRecoveryObservations input directory inventory retry writer (initial.inode writer)
        layout before.published (census.freshFlockAllowed.mpr last) selected)
      (session : SegmentedSession) (final : LockedFileState FileImage) (ready : Installed),
      (history = before.history ∨ history = before.history ++ failure.batch) ∧
      openReports.finish.run = .ok session (openReports.finish.census, final) ∧
      session.phase = .ready ready ∧
      openReports.reads.reads.ObservesSelected directory retry.image.directory.active.manifest before.published.durable ∧
      openReports.reads.bindings (directory.file .lock) = some (initial.inode writer) ∧
      openReports.admission.owner ∈ openReports.finish.census.slots ∧
      openReports.admission.cached ∈ openReports.finish.census.slots ∧
      recoverSelected (before.checkpoint.getD (.empty, 0)).1 (WAL.encode history) = .ok ready.table ∧
      InstalledClientReplay (log ++ [.uncertainBatch failure.batch]) reads history ready session := by
  have beforeReady := (client.writes.preservesRetained (start.bootstrap.writerReady start.held).toRetained).1
  have retries := census.reopenTrace earlier
  obtain ⟨cacheAfter, returned, _, manifest, history, allowed, _, pending, layout, _, prepared⟩ :=
    client.replaysPendingWriteError start request failure reported rows retries
  have sameManifest := manifest.trans (congrArg DirectoryPublication.Bindings.manifest beforeReady.walPair)
  have priorCheckpoint : SelectedIntegrityCheckpoint before.published.durable
      retry.image.directory.active.manifest before.checkpoint :=
    sameManifest.symm ▸ beforeReady.resumed.selected
  have priorAccepted : before.published.AcceptsVersioned before.history.length.toUInt64
      (CheckpointRepresentsPrefix before.history) retry.image.directory.active.manifest :=
    sameManifest.symm ▸ beforeReady.resumed.accepted
  obtain ⟨_, refined, represented⟩ := beforeReady.resumed.canonical
  have count : before.history.length = before.installed.table.committed.toNat :=
    represented.committed_count.symm.trans (congrArg UInt64.toNat refined.committed).symm
  have extended := prepareBatch_extends_history beforeReady.resumed.ordered count failure.prepared
  have fits := (failure.retainedCut beforeReady).1
  have accepted : before.published.AcceptsVersioned history.length.toUInt64
      (CheckpointRepresentsPrefix history) retry.image.directory.active.manifest := by
    rcases allowed with rfl | rfl
    · exact priorAccepted
    · exact CheckpointPublication.Image.acceptsVersioned_extend_history priorAccepted fits
  have ordered : WAL.OrdinalsFrom 1 history := by
    rcases allowed with rfl | rfl
    · exact beforeReady.resumed.ordered
    · exact extended.2.1
  obtain ⟨openReports⟩ := observe history layout allowed prepared priorCheckpoint
  obtain ⟨_, lockObject, session, final, opened, liveOwner, liveDirectory, _, _, physicalReads, installed⟩ :=
    openReports.finish.installs census earlier last openReports.ownerFresh openReports.directoryFresh
      openReports.lockObject openReports.markerFound prepared.keeperPrefix prepared.newer openReports.following
      accepted ordered
  obtain ⟨actualSession, actualFinal, ready, checkpoint, same, phase, selected, recovered, refined⟩ :=
    CachedRetryInstalled.refinesPendingClient installed pending
  obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj same
  have sameCheckpoint := selected.uniqueResult priorCheckpoint
  exact ⟨cacheAfter, returned, history, layout, priorCheckpoint, openReports, session, final, ready, allowed, opened,
    phase, physicalReads, lockObject, liveOwner, liveDirectory, sameCheckpoint ▸ recovered, refined⟩

end Alvoki.Storage.DiskSession
