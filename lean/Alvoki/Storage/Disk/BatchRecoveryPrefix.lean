import Alvoki.Storage.Disk.BootstrapClientTrace
import Alvoki.Storage.Disk.ListedMarkedFinish

namespace Alvoki.Storage.DiskSession

open WalSegmentCommit WalSegmentRepair

/-- Two preparations of the reached image at the same keeper choose the same
marker-selected bytes. This uses the shared open's actual offset, rather than
assuming that the new attempt already belongs to a logical retry trace. -/
private theorem samePreparedTarget {image : FileImage} {left right : Target} {a b : Plan}
    (preparedLeft : Prepared image left a) (preparedRight : Prepared image right b)
    (sameKeeper : left.first = right.first) : left = right := by
  have pair := preparedLeft.pair.symm.trans preparedRight.pair
  have range : left.range = right.range :=
    Option.some.inj (left.decoded.symm.trans (pair ▸ right.decoded))
  have size : left.trimmed.size = right.trimmed.size := by
    rw [left.trimmedSize, right.trimmedSize, range, sameKeeper]
  obtain ⟨leftTail, leftBytes⟩ := preparedLeft.keeperPrefix.activeValid
  obtain ⟨rightTail, rightBytes⟩ := preparedRight.keeperPrefix.activeValid
  have bytes := Option.some.inj (leftBytes.symm.trans rightBytes)
  have samePrefix := congrArg (fun bytes : ByteArray => bytes.extract 0 left.trimmed.size) bytes
  have trimmed : left.trimmed = right.trimmed := by
    rw [ByteArray.extract_append_eq_left rfl, ByteArray.extract_append_eq_left size] at samePrefix
    exact samePrefix
  cases left
  cases right
  cases pair
  cases range
  cases sameKeeper
  cases trimmed
  rfl

/-- An observed prefix of marked recovery. The recorded canonical keeper is
part of the reached read plan. Each repair failure supplies the local
preparation and the reached effects of that call. Membership of the chosen
target in the batch's old-or-whole alternatives is proved below. -/
inductive ReportedReopenPrefix (directory : DiskDirectory) (keeper : Nat)
    (initial : LockedFileState FileImage) : LockedFileState FileImage → Prop where
  | start : ReportedReopenPrefix directory keeper initial initial
  | prefixFailed {before files}
      (prior : ReportedReopenPrefix directory keeper initial before)
      (failure : CachedOpenPrefixFailure files directory before) (unchanged : failure.reached = before.image) :
      ReportedReopenPrefix directory keeper initial failure.after
  | rejected {before} (prior : ReportedReopenPrefix directory keeper initial before)
      (rejection : CachedOpenRejection directory before) :
      ReportedReopenPrefix directory keeper initial rejection.after
  | authorizationFailed {before} (prior : ReportedReopenPrefix directory keeper initial before)
      (failure : CachedOpenAuthorizationFailure directory before) (first : failure.target.first = keeper) :
      ReportedReopenPrefix directory keeper initial failure.after
  | repairFailed {before target plan opened cause reached} (prior : ReportedReopenPrefix directory keeper initial before)
      (attempt : CachedOpenAttempt directory before) (prepared : Prepared before.image target plan)
      (first : target.first = keeper)
      (preparedRead : attempt.prepare before.image =
        .ok ({ plan with keeperBytes := plan.keeperBytes.extract 0 plan.keeperSize }, opened, plan.keeperBytes.size) before.image)
      (failed : finishBoundedMarkedOpen directory { plan with keeperBytes := plan.keeperBytes.extract 0 plan.keeperSize }
        plan.keeperBytes.size attempt.removeFile attempt.write attempt.sync attempt.renameFile before.image = .error cause reached)
      (effects : EffectTrace target before.image reached) :
      ReportedReopenPrefix directory keeper initial (attempt.cleanupError cause reached).2
  | referenceDrops {before description} (prior : ReportedReopenPrefix directory keeper initial before)
      (references : HeldLockReferences description) (drops : List LockReferenceDrop) :
      ReportedReopenPrefix directory keeper initial (references.afterFileDrops drops directory before)
  | powerLoss {before pair bytes names} (prior : ReportedReopenPrefix directory keeper initial before)
      (metadata : pair ∈ before.image.directory.crashImages) (payload : bytes ∈ before.image.keeper.crashImages)
      (later : names ∈ before.image.later.crashImages) :
      ReportedReopenPrefix directory keeper initial
        ⟨before.image.crash pair bytes names, before.owners.set (directory.file .lock) none⟩

private theorem ReportedReopenPrefix.refines {directory keeper initial after} {admits : Target → Prop}
    (reported : ReportedReopenPrefix directory keeper initial after)
    (selects : ∀ {current}, BoundedReopenTrace directory admits initial current →
      ∃ target plan, admits target ∧ target.first = keeper ∧ Prepared current.image target plan) :
    BoundedReopenTrace directory admits initial after := by
  induction reported with
  | start => exact .empty
  | prefixFailed _ failure unchanged ih => exact .cachedPrefixFailed ih failure unchanged
  | rejected _ rejection ih => exact .cachedRejected ih rejection
  | authorizationFailed _ failure first ih =>
    obtain ⟨chosen, _, allowed, chosenFirst, prepared⟩ := selects ih
    have same := samePreparedTarget prepared failure.prepared (chosenFirst.trans first.symm)
    exact .cachedAuthorizationFailed ih failure (same ▸ allowed)
  | repairFailed _ attempt prepared first preparedRead failed effects ih =>
    obtain ⟨chosen, _, allowed, chosenFirst, earlier⟩ := selects ih
    have same := samePreparedTarget earlier prepared (chosenFirst.trans first.symm)
    exact .cachedRepairFailed ih attempt (same ▸ allowed) prepared effects (attempt.run_repairError preparedRead failed)
  | referenceDrops _ references drops ih => exact .referenceDrops ih references drops
  | powerLoss _ metadata payload later ih => exact .powerLoss ih metadata payload later

namespace SegmentedBatchMarkerPowerLossReport

variable {directory : DiskDirectory} {before : SegmentedWriterState} {writer : Nat}
  {cut : SegmentedBatchMarkerPowerLossReport directory before writer} {retry : LockedFileState FileImage}

/-- The reached marker publication and every subsequent retry prefix keep
the old manifest binding and sealed WAL. The visible marker selects the old
history or the whole submitted batch even if no open has returned ready. -/
theorem Reached.refinesReopenPrefix
    (observed : cut.Reached) (ready : before.RetainedReady directory writer)
    (reported : ReportedReopenPrefix directory before.wal.active.first cut.inFlight retry) :
    BoundedReopenTrace directory (BatchRetryTarget before.history cut.batch before.wal.active.first)
      cut.inFlight retry ∧
    retry.image.kept = cut.inFlight.image.kept ∧
    retry.image.directory.active.manifest = before.wal.directory.active.manifest ∧
    ∃ history, (history = before.history ∨ history = before.history ++ cut.batch) ∧
      retry.image.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64) ∧
      ∃ layout : CanonicalKeeperLayout retry.image history,
        layout.target.first = before.wal.active.first ∧ Prepared retry.image layout.target layout.plan := by
  have oldRange : before.wal.directory.active.walRange =
      some ⟨before.target.range.watermark, before.history.length⟩ := by
    rw [ready.walPair, ← ready.resumed.through]
    exact before.target.decoded
  have checkpoint := (congrArg DirectoryPublication.Bindings.manifest ready.walPair).symm ▸ ready.resumed.accepted
  obtain ⟨_, refined, represented⟩ := ready.resumed.canonical
  have count : before.history.length = before.installed.table.committed.toNat :=
    represented.committed_count.symm.trans (congrArg UInt64.toNat refined.committed).symm
  let effects := cut.cut.writeEffects cut.appendCrashTails (before.wal.directory.staged .walBoundary)
  have select {current : LockedFileState FileImage}
      (attempts : BoundedReopenTrace directory (BatchRetryTarget before.history cut.batch before.wal.active.first)
        cut.inFlight current) :=
    attempts.selectsAfterBatchCut ready.layout ready.valid oldRange ready.resumed.ordered count observed.prepared
      (observed.preparedHistory ready).2.1 checkpoint effects cut.physicalProjection
  have attempts := reported.refines fun earlier => by
    obtain ⟨_, _, history, allowed, marker, _, _, layout, _, first, _, _, _, prepared, _⟩ := select earlier
    have bytes : layout.target.trimmed = WAL.encode (history.drop before.wal.active.first) := by
      rw [← first]
      exact layout.chain.keeperBytes
    exact ⟨layout.target, layout.plan, ⟨first, history, allowed, marker, layout.through, bytes⟩,
      first, prepared⟩
  obtain ⟨kept, manifest, history, allowed, marker, _, _, layout, _, first, _, _, _, prepared, _⟩ := select attempts
  exact ⟨attempts, kept, manifest, history, allowed, marker, layout, first, prepared⟩

end SegmentedBatchMarkerPowerLossReport

/-- The client can continue from the marker interruption and its observed
retry prefix. Native read and finish reports supply the next exact session,
whose supported reads agree with the replay of the continued client log. -/
theorem SegmentedClientReadTrace.reopenAfterReportedBatchMarker
    {directory : DiskDirectory} {initialDescriptor writer : Nat}
    {initialResult : EStateM.Result IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession}
    (start : BootstrapClientStart directory initialDescriptor initialResult)
    {allowCollection : Bool} {log : List DatabaseSubmissions} {reads : List RecordedSnapshotRead}
    {before : SegmentedWriterState}
    (trace : SegmentedClientReadTrace directory initialDescriptor start.writer allowCollection log reads writer before)
    {cut : SegmentedBatchMarkerPowerLossReport directory before writer}
    (observed : cut.Reached) {retry : LockedFileState FileImage}
    (retries : ReportedReopenPrefix directory before.wal.active.first cut.inFlight retry)
    {input : System.FilePath}
    (readAndFinish : ∀ history, ∀ layout : CanonicalKeeperLayout retry.image history,
      (history = before.history ∨ history = before.history ++ cut.batch) →
      layout.target.first = before.wal.active.first →
      Nonempty (PrimitiveCheckpointHeldOpen input directory layout before.published)) :
    ∃ (descriptor : Nat) (after : SegmentedWriterState) (history : List WAL.Write)
      (layout : CanonicalKeeperLayout retry.image history)
      (reported : MarkedRetryChunkReports (SyncHandleRouting.Cache CheckpointOpenHandle) directory layout before.published)
      (admission : OpenAdmissionReports input directory reported.slot)
      (session : SegmentedSession) (final : LockedFileState FileImage),
      reported.runWithAdmission admission = .ok session final ∧
      session.directory = directory ∧ session.descriptor = descriptor ∧ session.phase = .ready after.installed ∧
      after.files = final.image ∧ after.owners = final.owners ∧ after.history = history ∧
      (history = before.history ∨ history = before.history ++ cut.batch) ∧
      SegmentedClientReadTrace directory initialDescriptor start.writer allowCollection
        (log ++ [.uncertainBatch cut.batch]) reads descriptor after ∧
      GuardedClientReplay (log ++ [.uncertainBatch cut.batch]) reads after session := by
  have initialReady := (start.bootstrap.writerReady start.held).toRetained
  have ready := (trace.writes.preservesRetained initialReady).1
  have attempts := (observed.refinesReopenPrefix ready retries).1
  have reports : BatchCutReopenObservations directory before cut.batch
      (SyncHandleRouting.Cache CheckpointOpenHandle) input retry := by
    intro history layout allowed first
    obtain ⟨openReport⟩ := readAndFinish history layout allowed first
    exact ⟨openReport.toHeldOpen.chunkReports, ⟨openReport.admission⟩⟩
  obtain ⟨descriptor, after, opened⟩ := observed.installsAdmitted ready attempts reports
  have continued := trace.advance (.batchMarkerAdmitted .start cut observed opened)
  obtain ⟨history, layout, report, admission, session, final, returned, path, lock, phase, _, files, owners, _,
    selected⟩ := opened.reopened
  exact ⟨descriptor, after, history, layout, report, admission, session, final, returned, path, lock, phase,
    files, owners, selected, selected ▸ opened.history, continued, continued.guardedReplay start.bootstrap start.held phase⟩

end Alvoki.Storage.DiskSession
