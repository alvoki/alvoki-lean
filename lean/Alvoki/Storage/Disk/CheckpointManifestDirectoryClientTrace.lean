import Alvoki.Storage.Disk.ClientReadTrace

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- The exact returned sync failure, release and admitted reopen extend the
client trace at the returned session without adding a submission or read. -/
theorem SegmentedClientReadTrace.afterManifestDirectoryError {input : FilePath}
    (trace : SegmentedClientReadTrace directory initialDescriptor initial allowCollection log reads writer before)
    {cut : CheckpointPowerCut directory before} {report : ObservedManifestDirectoryFailure cut}
    {retry : LockedFileState FileImage} {layout : CanonicalKeeperLayout retry.image before.history}
    {release : SegmentedFailureRelease writer}
    {opened : CheckpointHeldOpen input directory layout report.publication} {session final}
    (endpoint : report.Reopened release opened session final after) :
    SegmentedClientReadTrace directory initialDescriptor initial allowCollection log reads opened.calls.slot.description after := by
  simpa only [List.append_nil] using trace.advance (.checkpointManifestDirectoryError .start endpoint)

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
  have continued := trace.afterManifestDirectoryError endpoint
  exact ⟨layout, opened, session, final, after, endpoint, continued, continued.guardedReplay bootstrap held endpoint.phase⟩

end Alvoki.Storage.DiskSession
