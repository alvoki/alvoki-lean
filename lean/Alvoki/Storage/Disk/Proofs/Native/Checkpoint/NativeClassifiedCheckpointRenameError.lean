import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointWatermark
import Alvoki.Storage.Disk.Proofs.Native.Checkpoint.NativeOpenCheckpoint
import Alvoki.Storage.Disk.Proofs.Native.Open.NativeOpenedPosition

namespace Alvoki.Storage.DiskSession

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- The reported rename uses the exact return of the public checkpoint
on the original opened phase cell. -/
theorem NativeOpenedPosition.checkpointManifestRenameErrorFromReturn {image : Type}
    (start : NativeOpenedPosition opened)
    {cut : CheckpointPowerCut start.current.ready.state.session.directory start.current.ready.state.writer}
    (report : NativeCheckpointManifestRenameError (image := image) start.current.ready.state cut)
    {cause : IO.Error} {reached : heap} {after : CensusDirectoryCache × image}
    (returned : runCheckpointOnOpenPhase report.synced.settled.runs.perform opened.phase opened.get opened.set
      (start.reached, report.synced.settled.runs.entry.image) = .error cause (reached, after)) :
    let state := start.current.ready.state
    opened.table.UsesOpenCheckpointSchedule state.session.directory opened.files opened.phase ∧
    cause = report.cause ∧ after = (state.cache, report.after) ∧
    opened.contents reached opened.phase = some .poisoned := by
  intro state
  let runs := report.synced.settled.runs
  obtain ⟨source, classified⟩ := opened.phaseEffects.classifiesCheckpointReturn
    start.uses start.stored runs.primitives runs.entry
  have raw : runCheckpointOnOpenPhase (runs.primitives.cached.perform state.session.directory)
      opened.phase opened.get opened.set (start.reached, runs.entry.image) = .error cause (reached, after) := returned
  have normalized := (start.current.ready.checkpointManifestRenameError report).returned
  change runCheckpointWithEffects (runs.primitives.cached.perform state.session.directory)
    (state.session.phase, runs.entry) = _ at normalized
  have ready := start.current.ready.readPrefix.refines.1.phase
  rw [raw, normalized, ready] at classified
  cases classified with
  | fileError _ _ poison _ =>
    exact ⟨source, rfl, rfl, poison⟩

/-- The opened checkpoint's actual error return identifies this rename
incident. The reported reboot then reopens one survivor of those same
files and supplies the next ready position in the common trace. -/
theorem NativeOpenedPosition.recoversManifestRenameErrorFromReturn {image : Type}
    (start : NativeOpenedPosition opened)
    {cut : CheckpointPowerCut start.current.ready.state.session.directory start.current.ready.state.writer}
    {report : NativeCheckpointManifestRenameError (image := image) start.current.ready.state cut}
    (crash : NativeCheckpointManifestRenameCrash report) {input : System.FilePath}
    (observe : ∀ plan : crash.Plan, Nonempty (NativeCheckpointManifestRenameReads crash input plan))
    {cause : IO.Error} {reached : heap} {after : CensusDirectoryCache × image}
    (returned : runCheckpointOnOpenPhase report.synced.settled.runs.perform opened.phase opened.get opened.set
      (start.reached, report.synced.settled.runs.entry.image) = .error cause (reached, after)) :
    let state := start.current.ready.state
    opened.table.UsesOpenCheckpointSchedule state.session.directory opened.files opened.phase ∧
    cause = report.cause ∧ after = (state.cache, report.after) ∧
    opened.contents reached opened.phase = some .poisoned ∧
    ∃ next : NativeReadPosition start.current.history start.current.submissions,
      NativeCheckpointManifestRenameReopened start.current.ready crash input next ∧
      NativeExecutionStep start.current (.checkpointManifestRenameCrashRecovered input cause crash.pair.manifest)
        ⟨start.current.history, start.current.submissions, next⟩ ∧
      state.writer.target.range.watermark ≤ next.state.writer.target.range.watermark := by
  obtain ⟨source, diagnostic, image, poison⟩ := start.checkpointManifestRenameErrorFromReturn report returned
  obtain ⟨next, reopened⟩ := start.current.ready.recoversCheckpointManifestRenamePowerLoss crash observe
  subst cause
  exact ⟨source, rfl, image, poison, next, reopened,
    .recoverCheckpointManifestRenameError start.current crash next reopened, reopened.checkpointWatermark.1⟩

end Alvoki.Storage.DiskSession
