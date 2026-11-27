import Alvoki.Storage.Disk.CheckpointManifestRenameCut
import Alvoki.Storage.Disk.NativeReadyCheckpoint
import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointManifestRenameReboot

namespace Alvoki.Storage.DiskSession

/-- The manifest at a completed checkpoint's returned file image sets
the next ready writer's watermark to the full prior history length. -/
theorem NativeReadyCheckpoint.Completed.checkpointWatermark
    {image : Type} {state : NativeReadyState}
    {attempt : SegmentedCheckpointReport state.session.directory state.writer}
    {reports : CheckpointCompletionReports (CensusDirectoryCache × image) attempt}
    {report : NativeReadyCheckpoint state reports} {writer : SegmentedWriterState}
    (completed : report.Completed writer) (valid : state.Valid) :
    writer.target.range.watermark = state.writer.history.length ∧
      state.writer.target.range.watermark ≤ writer.target.range.watermark := by
  have binding : writer.files.directory.active.manifest = some attempt.manifest := by
    change (report.next writer).files.image.directory.active.manifest = some attempt.manifest
    rw [← completed.files]
    exact completed.manifestBinding
  have authority : writer.files.directory.active = writer.target.pair :=
    completed.valid.retained.resumed.ready.selected
  rw [authority] at binding
  have selected := (DirectoryPublication.Bindings.walRange_accounting writer.target.decoded).1
  rw [binding, (attempt.preparedManifestWatermark valid.retained reports.preflight).2] at selected
  have watermark := (Option.some.inj selected).symm
  refine ⟨watermark, ?_⟩
  rw [watermark, ← valid.retained.resumed.through]
  exact (DirectoryPublication.Bindings.walRange_accounting state.writer.target.decoded).2.1

/-- Decode the published bytes from the actual reached writer's selected
binding. The caller provides the old/new choice of that survivor. -/
private theorem CheckpointPowerCut.reopenedWatermark
    {history : List WAL.Write} {log : List DatabaseSubmissions}
    {current next : NativeReadPosition history log} {survivor : DirectoryPublication.Bindings}
    (cut : CheckpointPowerCut current.state.session.directory current.state.writer)
    (settled : next.state.files.image.directory.active = survivor)
    (chosen : survivor.manifest = current.state.writer.wal.directory.active.manifest ∨
      survivor.manifest = some cut.checkpoint.manifest) :
    current.state.writer.target.range.watermark ≤ next.state.writer.target.range.watermark ∧
      (survivor.manifest = current.state.writer.wal.directory.active.manifest →
        next.state.writer.target.range.watermark = current.state.writer.target.range.watermark) ∧
      (survivor.manifest = some cut.checkpoint.manifest →
        next.state.writer.target.range.watermark = current.state.writer.history.length) := by
  have before := current.readPrefix.refines.1.retained
  have authority : next.state.writer.target.pair = survivor :=
    next.readPrefix.refines.1.retained.resumed.ready.selected.symm.trans settled
  have old := congrArg DirectoryPublication.Bindings.manifest before.walPair
  rw [← authority, old] at chosen ⊢
  exact cut.preflight.reopenedWatermark before chosen

/-- The reopened writer follows the manifest reported to survive the
final directory barrier, for both returned and interrupted calls. -/
theorem NativeCheckpointRebootContinuation.checkpointWatermark
    {history : List WAL.Write} {log : List DatabaseSubmissions} {image : Type}
    {current next : NativeReadPosition history log} {input : System.FilePath}
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    {barrier : NativeCheckpointFinalBarrier (image := image) current.state cut} {after : image}
    {physical : barrier.Physical after} {crash : NativeCheckpointCrashFiles physical}
    (reopened : NativeCheckpointRebootContinuation current crash input next) :
    current.state.writer.target.range.watermark ≤ next.state.writer.target.range.watermark ∧
      (crash.pair.manifest = current.state.writer.wal.directory.active.manifest →
        next.state.writer.target.range.watermark = current.state.writer.target.range.watermark) ∧
      (crash.pair.manifest = some cut.checkpoint.manifest →
        next.state.writer.target.range.watermark = current.state.writer.history.length) :=
  cut.reopenedWatermark (current := current) (next := next) reopened.settled
    (crash.classification current.readPrefix.refines.1).2.2

/-- After a reported manifest rename error and reboot, the same selected
manifest bytes determine the watermark of the aligned reopen. This also
applies when earlier rejected opens left the selected files unchanged. -/
theorem NativeCheckpointManifestRenameReopened.checkpointWatermark
    {history : List WAL.Write} {log : List DatabaseSubmissions} {image : Type}
    {current next : NativeReadPosition history log} {input : System.FilePath}
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    {report : NativeCheckpointManifestRenameError (image := image) current.state cut}
    {crash : NativeCheckpointManifestRenameCrash report} {inventory : DescriptorInventory}
    (reopened : NativeCheckpointManifestRenameReopened current crash input next inventory) :
    current.state.writer.target.range.watermark ≤ next.state.writer.target.range.watermark ∧
      (crash.pair.manifest = current.state.writer.wal.directory.active.manifest →
        next.state.writer.target.range.watermark = current.state.writer.target.range.watermark) ∧
      (crash.pair.manifest = some cut.checkpoint.manifest →
        next.state.writer.target.range.watermark = current.state.writer.history.length) := by
  apply cut.reopenedWatermark (current := current) (next := next) reopened.settled
  rcases crash.classification current.readPrefix.refines.1 with ⟨_, original⟩ | ⟨_, _, replacement⟩
  · exact .inl original
  · exact .inr replacement

end Alvoki.Storage.DiskSession
