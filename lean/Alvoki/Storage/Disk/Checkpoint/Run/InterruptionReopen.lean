import Alvoki.Storage.Disk.Checkpoint.Run.Interruption
import Alvoki.Storage.Disk.Proofs.Checkpoint.CheckpointClientTrace

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting
open WalSegmentRepair (BootstrapReady FileImage)
open WAL.Boundary (WalInodeImage)

private abbrev Files := Cache (DescriptorInventory × DescriptorSlot) × WalInodeImage

variable {directory : DiskDirectory} {before : SegmentedWriterState}
  {attempt : SegmentedCheckpointReport directory before}
  {runs : ObservedCheckpointRunPrefix attempt}

private def countEffect : EStateM IO.Error Nat Unit := fun n => .ok () (n + 1)

private def countedCheckpoint (completed : List Step) (effective : Bool) :
    SegmentedCheckpointReport directory before :=
  { attempt with
    writeRun := fun _ _ => countEffect
    writeStage := fun _ _ => countEffect
    sync := fun _ => countEffect
    renameFile := fun _ _ => countEffect
    report := fun _ => .success
    cut := completed.length + (if effective then 1 else 0) }

private theorem countDispatch {completed : List Step} {effective : Bool} {step : Step}
    (member : step ∈ steps attempt.table.runs.length) (n : Nat) :
    (countedCheckpoint (attempt := attempt) completed effective).perform step n = .ok () (n + 1) := by
  cases step with
  | writeRun index =>
    have within : index < attempt.table.runs.length := by
      simpa [steps, runSteps, List.mem_flatMap, Publication.steps] using member
    have found : attempt.table.runs.toArray[index]? = some attempt.table.runs[index] := by
      rw [List.getElem?_toArray, List.getElem?_eq_getElem within]
    simp [countedCheckpoint, SegmentedCheckpointReport.perform, SegmentedCheckpointReport.prepared,
      CheckpointFileCallbacks.perform, performCheckpointFileStep, found, countEffect, Bind.bind, EStateM.bind,
      Pure.pure, EStateM.pure]
  | syncRun => rfl
  | syncRunsDirectory => rfl
  | manifest step => cases step <;> rfl

private theorem countPrefix {completed : List Step} {effective : Bool} (actions : List Step)
    (member : ∀ step ∈ actions, step ∈ steps attempt.table.runs.length) (n : Nat) :
    (actions.forM (countedCheckpoint (attempt := attempt) completed effective).perform) n =
      .ok () (n + actions.length) := by
  induction actions generalizing n with
  | nil => simp [List.forM_eq_forM, Pure.pure, EStateM.pure]
  | cons step pending ih =>
    have counted : (countedCheckpoint (attempt := attempt) completed effective).perform step n =
        .ok () (n + 1) :=
      countDispatch (member step List.mem_cons_self) n
    have remaining := ih (fun later present => member later (List.mem_cons_of_mem _ present)) (n + 1)
    change EStateM.bind ((countedCheckpoint (attempt := attempt) completed effective).perform step)
      (fun _ => pending.forM (countedCheckpoint (attempt := attempt) completed effective).perform) n = _
    simp only [EStateM.bind, counted, remaining, List.length_cons, Nat.add_right_comm, Nat.add_assoc]

/-- Count the exact returned prefix of the interrupted physical callback
schedule. The issued operation contributes only its reported effect bit. -/
def CheckpointRunInterruption.countedCut (observed : CheckpointRunInterruption runs) (effective : Bool) :
    CheckpointPowerCut directory before := by
  let checkpoint := countedCheckpoint (attempt := attempt) observed.completed effective
  let actions := steps attempt.table.runs.length
  let remaining := actions.drop (observed.completed.length + 1)
  have ordered : actions = observed.completed ++ observed.current :: remaining := by
    obtain ⟨later, split⟩ := observed.reaches.2.1
    change actions = observed.completed ++ observed.current :: later at split
    have tail : remaining = later := by
      simp [remaining, split, List.drop_append]
    rw [tail]
    exact split
  have inSchedule {step : Step} (member : step ∈ observed.completed) :
      step ∈ steps attempt.table.runs.length := by
    change step ∈ actions
    rw [ordered]
    exact List.mem_append_left _ member
  refine {
    checkpoint, flushed := runs.flushedTable, generationFits := runs.generationFits, runCountFits := runs.runCountFits
    encoded := runs.encoded, completed := observed.completed, current := observed.current, remaining, schedule := ordered
    observed := ?_, state := observed.completed.length, returned := ?_, tookEffect := effective, atCut := rfl }
  · intro done step todo split n _
    have member : step ∈ observed.completed := by rw [split]; simp
    change StepReport.Observes .success n (checkpoint.perform step n)
    rw [countDispatch (inSchedule member) n]
    rfl
  · simpa only [Nat.zero_add] using countPrefix (attempt := attempt) (effective := effective)
      (completed := observed.completed) observed.completed (fun _ => inSchedule) 0

/-- The crash map selected before run-directory sync feeds the same held
open and the same client replay proof as the other checkpoint cuts. -/
theorem CheckpointRunInterruption.reopensClient {input : FilePath} {writer initialDescriptor : Nat}
    {allowCollection : Bool} {log : List DatabaseSubmissions} {reads : List RecordedSnapshotRead}
    {first : LockedFileState WalSegmentRotation.State}
    (observed : CheckpointRunInterruption runs) (effective : Bool)
    (bootstrap : BootstrapReady first.image) (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads writer before)
    (entry : CheckpointRunPrefix.EntrySelection before (runs.view 0))
    {manifest : Files → Publication.Image} (frames : RunPrefixManifestFrames runs observed.reached manifest)
    {binding : Option ByteArray} (survives : binding ∈ (manifest observed.reached).crashImages)
    {files : RunFiles} (runSurvives : files ∈ (runs.runs observed.reached).crashImages)
    (retry : LockedFileState FileImage)
    (attempts : BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
      ⟨(CheckpointPowerCut.physical before before.published).crash ⟨binding, before.wal.directory.active.walBoundary⟩
        (some before.wal.active.bytes) [], before.owners.set (directory.file .lock) none⟩ retry)
    (reports : CheckpointHeldOpen.Reports input directory before retry before.published { before.published with durable := files }) :
    SelectedIntegrityCheckpoint files binding before.checkpoint ∧
      (observed.countedCut effective).ClientReopened input retry before.published binding files initialDescriptor
        (bootstrap.writerState first.owners) allowCollection log reads := by
  have ready := (trace.writes.preservesRetained (bootstrap.writerReady held).toRetained).1
  obtain ⟨_, agrees, selected⟩ := observed.selectsPrior ready entry frames survives runSurvives
  have admitted : binding ∈ before.published.manifest.crashImages := frames.preserves ▸ survives
  have exactProjection : before.published.executeVersioned (observed.countedCut effective).checkpoint.plan
      (observed.countedCut effective).checkpoint.cut = some before.published :=
    observed.projection effective
  exact ⟨selected, (observed.countedCut effective).reopensClient bootstrap held trace before.published
    exactProjection binding admitted files agrees retry attempts reports⟩

end Alvoki.Storage.DiskSession
