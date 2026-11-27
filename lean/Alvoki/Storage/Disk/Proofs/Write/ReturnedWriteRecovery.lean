import Alvoki.Storage.Disk.Proofs.Session.BatchRecoveryPrefix
import Alvoki.Storage.Disk.Proofs.Write.ClientWriteTrace

namespace Alvoki.Storage.DiskSession

open System WAL.Boundary WalSegmentCommit WalSegmentRepair SyncHandleRouting

/-- The exact file cut after a reported publication error supplies the
allowed target for each reached failed recovery. The observed prefix retains
the manifest binding and prior seals even if recovery stops here. The
starting owner comes from the caller’s observed lock state. -/
theorem SegmentedBatchFailure.refinesReopenPrefixWithWal {directory : DiskDirectory} {before : SegmentedWriterState}
    {writer : Nat} {owners : LockOwners} {retry : LockedFileState FileImage}
    (failure : SegmentedBatchFailure directory before) (ready : before.RetainedReady directory writer)
    (reported : ReportedReopenPrefix directory before.wal.active.first ⟨failure.released.image, owners⟩ retry) :
    BoundedReopenTrace directory (BatchRetryTarget before.history failure.batch before.wal.active.first)
      ⟨failure.released.image, owners⟩ retry ∧
    retry.image.kept = failure.released.image.kept ∧
    retry.image.directory.active.manifest = before.wal.directory.active.manifest ∧
    ∃ history, (history = before.history ∨ history = before.history ++ failure.batch) ∧
      retry.image.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64) ∧
      let wal := before.wal.appendSelectedView retry.image.directory.active history
      wal.ReadLayout history ∧ wal.Valid history ∧
      ∃ layout : CanonicalKeeperLayout retry.image history,
        layout.target.first = before.wal.active.first ∧
        layout.sealed ++ [layout.keeper] = wal.readDescriptors layout.range.watermark ∧
        selectWalSegmentReads (wal.segments.map WalSegment.first) layout.range.watermark =
          some (layout.first, (wal.readDescriptors layout.range.watermark).map WalSegment.first) ∧
        Prepared retry.image layout.target layout.plan ∧
        before.published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
          retry.image.directory.active.manifest ∧ WAL.OrdinalsFrom 1 history := by
  obtain ⟨fits, cut⟩ := failure.retainedCut ready
  have projected : BatchCutProjection failure.released.image
      ((writeFilesAfter (runBatchEffects before.history failure.batch failure.effects
        (before.wal.directory.staged .walBoundary))).reopenSegment before.wal.active.first
        before.history before.wal.directory.active.manifest) := by
    rw [cut]
    exact ⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩⟩
  have oldRange : before.wal.directory.active.walRange =
      some ⟨before.target.range.watermark, before.history.length⟩ := by
    rw [ready.walPair, ← ready.resumed.through]
    exact before.target.decoded
  have checkpoint := (congrArg DirectoryPublication.Bindings.manifest ready.walPair).symm ▸ ready.resumed.accepted
  obtain ⟨_, refined, represented⟩ := ready.resumed.canonical
  have count : before.history.length = before.installed.table.committed.toNat :=
    represented.committed_count.symm.trans (congrArg UInt64.toNat refined.committed).symm
  have select {current : LockedFileState FileImage}
      (attempts : BoundedReopenTrace directory (BatchRetryTarget before.history failure.batch before.wal.active.first)
        ⟨failure.released.image, owners⟩ current) :=
    attempts.selectsAfterBatchCut ready.layout ready.valid oldRange ready.resumed.ordered count failure.prepared
      fits checkpoint failure.effects projected
  have attempts := reported.refines fun earlier => by
    obtain ⟨_, _, history, allowed, marker, _, _, layout, _, first, _, _, _, prepared, _⟩ := select earlier
    have bytes : layout.target.trimmed = WAL.encode (history.drop before.wal.active.first) := by
      rw [← first]
      exact layout.chain.keeperBytes
    exact ⟨layout.target, layout.plan, ⟨first, history, allowed, marker, layout.through, bytes⟩, first, prepared⟩
  obtain ⟨kept, manifest, history, allowed, marker, walLayout, walValid, layout, _, first, _,
    descriptors, offsets, prepared, _, accepted, ordered, _⟩ := select attempts
  exact ⟨attempts, kept, manifest, history, allowed, marker, walLayout, walValid, layout, first,
    descriptors, offsets, prepared, accepted, ordered⟩

theorem SegmentedBatchFailure.refinesReopenPrefix {directory : DiskDirectory} {before : SegmentedWriterState}
    {writer : Nat} {owners : LockOwners} {retry : LockedFileState FileImage}
    (failure : SegmentedBatchFailure directory before) (ready : before.RetainedReady directory writer)
    (reported : ReportedReopenPrefix directory before.wal.active.first ⟨failure.released.image, owners⟩ retry) :
    BoundedReopenTrace directory (BatchRetryTarget before.history failure.batch before.wal.active.first)
      ⟨failure.released.image, owners⟩ retry ∧
    retry.image.kept = failure.released.image.kept ∧
    retry.image.directory.active.manifest = before.wal.directory.active.manifest ∧
    ∃ history, (history = before.history ∨ history = before.history ++ failure.batch) ∧
      retry.image.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64) ∧
      ∃ layout : CanonicalKeeperLayout retry.image history,
        layout.target.first = before.wal.active.first ∧ Prepared retry.image layout.target layout.plan := by
  obtain ⟨bounded, kept, manifest, history, allowed, marker, _, _, layout, first, _, _, prepared, _⟩ :=
    failure.refinesReopenPrefixWithWal ready reported
  exact ⟨bounded, kept, manifest, history, allowed, marker, layout, first, prepared⟩

/-- On the exact returned cache, the reported release is a successful
unlock in the file-state projection or an observed last-reference drop.
Once a held open reports its reads, admission and reached primitive
successes, the client continues at that exact session. -/
theorem SegmentedClientReadTrace.reopenAfterReportedWrite {handle : Type}
    {directory : DiskDirectory} {input : FilePath} {initialDescriptor writer : Nat}
    {initialResult : EStateM.Result IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession}
    (start : BootstrapClientStart directory initialDescriptor initialResult)
    {before : SegmentedWriterState} {allowCollection : Bool} {log : List DatabaseSubmissions}
    {reads : List RecordedSnapshotRead} {retry : LockedFileState FileImage}
    (trace : SegmentedClientReadTrace directory initialDescriptor start.writer allowCollection log reads writer before)
    (request : WriteRequest) (failure : SegmentedBatchFailure directory before)
    (observed : ObservedBatchFailure failure handle) (rows : request.rows = failure.rows)
    (cacheAfter : Cache handle)
    (returned : (WriteRequest.Calls.ofFailure observed).run request directory before =
      .error (.commitUnknown failure.cause) (.poisoned, ⟨(cacheAfter, failure.failed), before.owners⟩))
    (release : SegmentedFailureRelease writer)
    (retries : ReportedReopenPrefix directory before.wal.active.first failure.released retry)
    (readAndFinish : ∀ history, ∀ layout : CanonicalKeeperLayout retry.image history,
      (history = before.history ∨ history = before.history ++ failure.batch) →
      layout.target.first = before.wal.active.first →
      Nonempty (PrimitiveCheckpointHeldOpen input directory layout before.published)) :
    let poisoned : WriteCallState handle := (.poisoned, ⟨(cacheAfter, failure.failed), before.owners⟩)
    release.Observed (directory := directory) poisoned ⟨poisoned.2.image, failure.released.owners⟩ ∧
    ∃ (descriptor : Nat) (after : SegmentedWriterState) (history : List WAL.Write)
      (layout : CanonicalKeeperLayout retry.image history)
      (reported : MarkedRetryChunkReports (Cache CheckpointOpenHandle) directory layout before.published)
      (admission : OpenAdmissionReports input directory reported.slot)
      (session : SegmentedSession) (final : LockedFileState FileImage),
      reported.runWithAdmission admission = .ok session final ∧
      session.directory = directory ∧ session.descriptor = descriptor ∧ session.phase = .ready after.installed ∧
      session.sessionRef ∉ reported.liveRefs ∧
      final.owners.Owns directory descriptor ∧ after.files = final.image ∧ after.owners = final.owners ∧
      final.image.directory.active = retry.image.directory.active ∧
      after.history = history ∧ (history = before.history ∨ history = before.history ++ failure.batch) ∧
      after.published.durable = before.published.durable ∧
      after.checkpoint = before.checkpoint ∧ after.installed.generation = before.installed.generation ∧
      SegmentedClientReadTrace directory initialDescriptor start.writer allowCollection
        (log ++ [.uncertainBatch failure.batch]) reads descriptor after ∧
      GuardedClientReplay (log ++ [.uncertainBatch failure.batch]) reads after session := by
  have initialReady := (start.bootstrap.writerReady start.held).toRetained
  have ready := (trace.writes.preservesRetained initialReady).1
  have attempts := (failure.refinesReopenPrefix ready retries).1
  have reports : BatchCutReopenObservations directory before failure.batch (Cache CheckpointOpenHandle) input retry := by
    intro history layout allowed first
    obtain ⟨opened⟩ := readAndFinish history layout allowed first
    exact ⟨opened.toHeldOpen.chunkReports, ⟨opened.admission⟩⟩
  obtain ⟨descriptor, after, released, endpoint, continued⟩ :=
    trace.reopenAfterReturnedWrite initialReady request failure observed rows cacheAfter returned release attempts reports
  obtain ⟨history, layout, reported, admission, session, final, opened, path, lock, phase, held, files, owners,
    bindings, selected⟩ := endpoint.reopened
  exact ⟨released, descriptor, after, history, layout, reported, admission, session, final, opened,
    path, lock, phase, (reported.admittedSessionRefs admission opened).2.2.2, held, files, owners, bindings, selected,
    selected ▸ endpoint.history, endpoint.durable, endpoint.checkpoint, endpoint.generation, continued,
    continued.guardedReplay start.bootstrap start.held phase⟩

end Alvoki.Storage.DiskSession
