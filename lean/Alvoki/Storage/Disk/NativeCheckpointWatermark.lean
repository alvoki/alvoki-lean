import Alvoki.Storage.Disk.CheckpointManifestRenameCut
import Alvoki.Storage.Disk.NativeReadyCheckpoint
import Alvoki.Storage.Disk.NativeCheckpointErrorPowerLoss

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

/-- The watermark of the reopened writer follows the manifest of the
reported survivor, for both returned and interrupted checkpoint calls. -/
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
        next.state.writer.target.range.watermark = current.state.writer.history.length) := by
  have before := current.readPrefix.refines.1.retained
  have authority : next.state.files.image.directory.active = next.state.writer.target.pair :=
    next.readPrefix.refines.1.retained.resumed.ready.selected
  have selected : selectedCheckpointWatermark crash.pair.manifest = some next.state.writer.target.range.watermark := by
    rw [← reopened.settled, authority]
    exact (DirectoryPublication.Bindings.walRange_accounting next.state.writer.target.decoded).1
  have old (survived : crash.pair.manifest = current.state.writer.wal.directory.active.manifest) :
      next.state.writer.target.range.watermark = current.state.writer.target.range.watermark := by
    have watermark := (DirectoryPublication.Bindings.walRange_accounting current.state.writer.target.decoded).1
    rw [survived, before.walPair, watermark] at selected
    exact (Option.some.inj selected).symm
  have new (survived : crash.pair.manifest = some cut.checkpoint.manifest) :
      next.state.writer.target.range.watermark = current.state.writer.history.length := by
    have watermark := (cut.checkpoint.preparedManifestWatermark before cut.preflight).2
    rw [survived, watermark] at selected
    exact (Option.some.inj selected).symm
  refine ⟨?_, old, new⟩
  rcases reopened.generation with ⟨_, original⟩ | ⟨_, replacement⟩
  · exact Nat.le_of_eq (old original).symm
  · rw [new replacement, ← before.resumed.through]
    exact (DirectoryPublication.Bindings.walRange_accounting current.state.writer.target.decoded).2.1

end Alvoki.Storage.DiskSession
