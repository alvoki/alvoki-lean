import Alvoki.Storage.Disk.ClientReadTrace

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- The exact returned manifest failure, release and admitted reopen extend the
client trace at the returned session without adding a submission or read. -/
theorem SegmentedClientReadTrace.afterManifestError
    (trace : SegmentedClientReadTrace directory initialDescriptor initial allowCollection log reads writer before)
    (endpoint : CheckpointManifestErrorReopened (directory := directory) (before := before) writer descriptor session final after) :
    SegmentedClientReadTrace directory initialDescriptor initial allowCollection log reads descriptor after := by
  simpa only [List.append_nil] using trace.advance (.checkpointManifestError .start endpoint)

/-- The returned final manifest-directory error and exact admitted retry
preserve the existing client ledgers. One replay accounts for the
recorded responses and for supported reads in the returned ready session. -/
theorem SegmentedClientReadTrace.reopenAfterManifestDirectoryError {input : FilePath}
    {first : LockedFileState WalSegmentRotation.State}
    (bootstrap : BootstrapReady first.image) (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads writer before)
    {cut : CheckpointPowerCut directory before} (report : ObservedManifestDirectoryFailure cut)
    (release : SegmentedFailureRelease writer) (retry : LockedFileState FileImage) :
    let publication := report.publication
    let released := ⟨CheckpointPowerCut.physical before publication, before.owners.set (directory.file .lock) none⟩
    BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first) released retry →
    CheckpointHeldOpen.Reports input directory before retry publication publication →
    ∃ (layout : CanonicalKeeperLayout retry.image before.history)
      (opened : CheckpointHeldOpen input directory layout publication)
      (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState),
      report.Reopened release opened session final after ∧
      SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
        allowCollection log reads opened.calls.slot.description after ∧
      GuardedClientReplay log reads after session := by
  intro publication released attempts observed
  have ready := (trace.writes.preservesRetained (bootstrap.writerReady held).toRetained).1
  obtain ⟨layout, opened, session, final, after, endpoint⟩ := report.reopens ready release retry attempts observed
  have continued := trace.afterManifestError (.directorySync endpoint)
  exact ⟨layout, opened, session, final, after, endpoint, continued, continued.guardedReplay bootstrap held endpoint.phase⟩

/-- The admitted retry of a returned rename error selects the exact
physical checkpoint. The same replay accounts for the existing ledgers
and supported reads in the session that the open actually returned. -/
theorem SegmentedClientReadTrace.reopenAfterManifestRenameError {input : FilePath}
    {first : LockedFileState WalSegmentRotation.State}
    (bootstrap : BootstrapReady first.image) (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads writer before)
    {cut : CheckpointPowerCut directory before} (report : ObservedManifestRenameFailure cut)
    (release : SegmentedFailureRelease writer) (retry : LockedFileState FileImage) :
    let publication := report.publication
    let released := ⟨CheckpointPowerCut.physical before publication, before.owners.set (directory.file .lock) none⟩
    BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first) released retry →
    CheckpointHeldOpen.Reports input directory before retry publication publication →
    ∃ (layout : CanonicalKeeperLayout retry.image before.history)
      (opened : CheckpointHeldOpen input directory layout publication)
      (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState),
      report.Reopened release opened session final after ∧
      SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
        allowCollection log reads opened.calls.slot.description after ∧
      GuardedClientReplay log reads after session := by
  intro publication released attempts observed
  have ready := (trace.writes.preservesRetained (bootstrap.writerReady held).toRetained).1
  obtain ⟨layout, opened, session, final, after, endpoint⟩ := report.reopens ready release retry attempts observed
  have continued := trace.afterManifestError (.rename endpoint)
  exact ⟨layout, opened, session, final, after, endpoint, continued, continued.guardedReplay bootstrap held endpoint.phase⟩

end Alvoki.Storage.DiskSession
