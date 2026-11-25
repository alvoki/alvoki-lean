import Alvoki.Storage.Disk.CheckpointManifestRenameReopen
import Alvoki.Storage.Disk.ClientReadTrace

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open scoped List

/-- The ready client session returned after a checkpoint power cut, using
the reported surviving checkpoint bytes and unchanged WAL history. -/
abbrev CheckpointPowerCut.ClientReopened
    {directory : DiskDirectory} {before : SegmentedWriterState}
    (cut : CheckpointPowerCut directory before) (input : FilePath) (retry : LockedFileState FileImage)
    (published : CheckpointPublication.Image) (binding : Option ByteArray) (runs : CheckpointPublication.RunFiles)
    (initialDescriptor : Nat) (initial : SegmentedWriterState) (allowCollection : Bool)
    (log : List DatabaseSubmissions) (reads : List RecordedSnapshotRead) : Prop :=
    ∃ (layout : CanonicalKeeperLayout retry.image before.history)
      (observed : CheckpointHeldOpen input directory layout { published with durable := runs })
      (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState),
      observed.wal.operations.runWithAdmission observed.admission = .ok session final ∧
      session.directory = directory ∧ session.descriptor = observed.calls.slot.description ∧
      session.phase = .ready after.installed ∧ final.owners.Owns directory session.descriptor ∧
      after.files = final.image ∧ after.owners = final.owners ∧ after.RetainedReady directory observed.calls.slot.description ∧
      after.history = before.history ∧
      final.image.directory.active = ⟨binding, before.wal.directory.active.walBoundary⟩ ∧
      SelectedIntegrityCheckpoint runs binding after.checkpoint ∧
      ((after.installed.generation = before.installed.generation ∧ binding = before.wal.directory.active.manifest) ∨
        (after.installed.generation = SegmentedCheckpointReport.generation before ∧ binding = some cut.checkpoint.manifest)) ∧
      recoverSelected (after.checkpoint.getD (.empty, 0)).1 (WAL.encode before.history) = .ok after.installed.table ∧
      SegmentedClientReadTrace directory initialDescriptor initial allowCollection log reads observed.calls.slot.description after ∧
      GuardedClientReplay log reads after session

/-- An observed checkpoint power cut extends the client ledger at the
session returned by the admitted reopen. No submission or read is added. -/
theorem CheckpointPowerCut.HeldReopen.refinesClient
    {directory : DiskDirectory} {before : SegmentedWriterState}
    {input : FilePath} {writer initialDescriptor : Nat} {allowCollection : Bool}
    {log : List DatabaseSubmissions} {reads : List RecordedSnapshotRead}
    {first : LockedFileState WalSegmentRotation.State}
    (bootstrap : BootstrapReady first.image) (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads writer before)
    {cut : CheckpointPowerCut directory before} {retry : LockedFileState FileImage}
    {published : CheckpointPublication.Image} {binding : Option ByteArray} {runs : CheckpointPublication.RunFiles}
    (reopened : cut.HeldReopen input writer retry published binding runs) :
    cut.ClientReopened input retry published binding runs initialDescriptor
      (bootstrap.writerState first.owners) allowCollection log reads := by
  obtain ⟨layout, observed, session, final, opened, checkpoint, _, returned, path, descriptor, phase, owner, pair, selected,
    generation, replay, _, _, _, after, nextReady, afterCheckpoint, afterInstalled, files, owners, continues⟩ := reopened
  have ready := (trace.writes.preservesRetained (bootstrap.writerReady held).toRetained).1
  let suffix : SegmentedBatchDatabaseTrace directory writer before allowCollection [] observed.calls.slot.description after :=
    continues .start
  have sameHistory : after.history = before.history := by
    obtain ⟨_, retained, extended, kept⟩ := suffix.preservesRetained ready
    have noneSubmitted : retained <+ ([] : List WAL.Write) := kept.orderedSubmissions.2
    have empty : retained = [] := List.sublist_nil.mp noneSubmitted
    simpa only [empty, List.append_nil] using extended
  have currentPhase : session.phase = .ready after.installed := afterInstalled ▸ phase
  have continued : SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads observed.calls.slot.description after := by
    simpa only [List.append_nil] using trace.advance suffix
  refine ⟨layout, observed, session, final, after, returned, path, descriptor, currentPhase, owner,
    files, owners, nextReady, sameHistory, pair, afterCheckpoint ▸ selected, ?_, ?_, continued,
    continued.guardedReplay bootstrap held currentPhase⟩
  · simpa only [afterInstalled, Reopened.installed] using generation
  · simpa only [afterCheckpoint, afterInstalled, Reopened.installed] using replay

/-- Derive the held reopen and the continued client replay from the cut's
reported file survivors and the native-shaped retry observations. -/
theorem CheckpointPowerCut.reopensClient
    {directory : DiskDirectory} {before : SegmentedWriterState}
    {input : FilePath} {writer initialDescriptor : Nat} {allowCollection : Bool}
    {log : List DatabaseSubmissions} {reads : List RecordedSnapshotRead}
    {first : LockedFileState WalSegmentRotation.State}
    (cut : CheckpointPowerCut directory before)
    (bootstrap : BootstrapReady first.image) (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads writer before)
    (published : CheckpointPublication.Image)
    (projected : before.published.executeVersioned cut.checkpoint.plan cut.checkpoint.cut = some published)
    (binding : Option ByteArray) (survives : binding ∈ published.manifest.crashImages)
    (runs : CheckpointPublication.RunFiles) (agrees : SelectedRunsAgree binding runs published.durable)
    (retry : LockedFileState FileImage)
    (attempts : BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
      ⟨(CheckpointPowerCut.physical before published).crash ⟨binding, before.wal.directory.active.walBoundary⟩
        (some before.wal.active.bytes) [], before.owners.set (directory.file .lock) none⟩ retry)
    (reports : CheckpointHeldOpen.Reports input directory before retry published { published with durable := runs }) :
    cut.ClientReopened input retry published binding runs initialDescriptor
      (bootstrap.writerState first.owners) allowCollection log reads := by
  have ready := (trace.writes.preservesRetained (bootstrap.writerReady held).toRetained).1
  have opened := cut.reopensSelectedRunMap ready published projected binding survives runs agrees retry attempts reports
  exact opened.refinesClient bootstrap held trace

end Alvoki.Storage.DiskSession
