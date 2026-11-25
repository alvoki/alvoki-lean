import Alvoki.Storage.Disk.ClientReadTrace

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- The exact admitted reopen after a reported run-publication error
extends the client trace without adding a submission or read. -/
theorem SegmentedClientReadTrace.afterRunError
    (trace : SegmentedClientReadTrace directory initialDescriptor initial allowCollection log reads writer before)
    (endpoint : PriorCheckpointErrorReopened (directory := directory) (before := before) writer descriptor session final after) :
    SegmentedClientReadTrace directory initialDescriptor initial allowCollection log reads descriptor after := by
  simpa only [List.append_nil] using trace.advance (.checkpointRunError .start endpoint)

/-- An error at a run's guard, write-open, write, flush or own file sync
preserves the installed prior checkpoint and both client ledgers. One
replay accounts for recorded responses and supported reads in the
returned ready session. -/
theorem SegmentedClientReadTrace.reopenAfterRunError {input : FilePath}
    {first : LockedFileState WalSegmentRotation.State}
    (bootstrap : BootstrapReady first.image) (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads writer before)
    {attempt : SegmentedCheckpointReport directory before} {runs : ObservedCheckpointRunPrefix attempt}
    (reported : CheckpointRunError runs cause reached)
    (entry : CheckpointRunPrefix.EntrySelection before (runs.view 0)) (frames : RunPrefixManifestFrames runs reached manifest)
    (release : SegmentedFailureRelease writer) (retry : LockedFileState FileImage) :
    let publication := reported.publication manifest
    let released := ⟨CheckpointPowerCut.physical before publication, before.owners.set (directory.file .lock) none⟩
    BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first) released retry →
    CheckpointHeldOpen.Reports input directory before retry publication publication →
    ∃ (layout : CanonicalKeeperLayout retry.image before.history)
      (opened : CheckpointHeldOpen input directory layout publication)
      (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState),
      reported.Reopened release opened session final after ∧
      SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
        allowCollection log reads opened.calls.slot.description after ∧
      GuardedClientReplay log reads after session := by
  intro publication released attempts observed
  have ready := (trace.writes.preservesRetained (bootstrap.writerReady held).toRetained).1
  obtain ⟨layout, opened, session, final, after, endpoint⟩ := reported.reopens ready entry frames release retry attempts observed
  have continued := trace.afterRunError (.runError endpoint)
  exact ⟨layout, opened, session, final, after, endpoint, continued, continued.guardedReplay bootstrap held endpoint.phase⟩

/-- The first run-directory sync error keeps the same prior checkpoint
for both reported name effects. The admitted reopen continues the same
client ledger and its replay through the actual returned session. -/
theorem SegmentedClientReadTrace.reopenAfterRunDirectoryError {input : FilePath}
    {first : LockedFileState WalSegmentRotation.State}
    (bootstrap : BootstrapReady first.image) (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads writer before)
    {cut : CheckpointPowerCut directory before} (reported : ObservedCheckpointRunDirectoryFailure cut)
    (release : SegmentedFailureRelease writer) (retry : LockedFileState FileImage) :
    let publication := reported.publication
    let released := ⟨CheckpointPowerCut.physical before publication, before.owners.set (directory.file .lock) none⟩
    BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first) released retry →
    CheckpointHeldOpen.Reports input directory before retry publication publication →
    ∃ (layout : CanonicalKeeperLayout retry.image before.history)
      (opened : CheckpointHeldOpen input directory layout publication)
      (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState),
      reported.Reopened release opened session final after ∧
      SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
        allowCollection log reads opened.calls.slot.description after ∧
      GuardedClientReplay log reads after session := by
  intro publication released attempts observed
  have ready := (trace.writes.preservesRetained (bootstrap.writerReady held).toRetained).1
  obtain ⟨layout, opened, session, final, after, endpoint⟩ := reported.reopens ready release retry attempts observed
  have continued := trace.afterRunError (.directorySync endpoint)
  exact ⟨layout, opened, session, final, after, endpoint, continued, continued.guardedReplay bootstrap held endpoint.phase⟩

end Alvoki.Storage.DiskSession
