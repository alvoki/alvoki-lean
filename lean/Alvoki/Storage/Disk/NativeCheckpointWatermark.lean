import Alvoki.Storage.Disk.CheckpointManifestRenameCut
import Alvoki.Storage.Disk.NativeReadyCheckpoint

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

end Alvoki.Storage.DiskSession
