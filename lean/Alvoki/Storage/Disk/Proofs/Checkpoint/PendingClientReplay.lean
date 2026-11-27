import Alvoki.Storage.Disk.Proofs.Checkpoint.CheckpointManifestDirectoryCut
import Alvoki.Storage.Disk.Proofs.Recovery.PendingClientReplay

namespace Alvoki.Storage.DiskSession

open CheckpointPublication WalSegmentRepair System SyncHandleRouting
open WAL.Boundary (WalInodeImage)

/-- The selected physical checkpoint and WAL already explain the client
ledger before the recovery operation installs a new writer. -/
def CheckpointPowerCut.PendingReplay {directory : DiskDirectory} {before : SegmentedWriterState}
    (cut : CheckpointPowerCut directory before) (runs : RunUnlinkImage) (binding : Option ByteArray)
    (log : List DatabaseSubmissions) (reads : List RecordedSnapshotRead) : Prop :=
  (cut.tookEffect = true → binding = some cut.checkpoint.manifest) ∧
  ∃ checkpoint table model,
    SelectedIntegrityCheckpoint runs.guaranteed binding checkpoint ∧
    (((checkpoint.getD (.empty, 0)).2 = before.installed.generation ∧
      binding = before.wal.directory.active.manifest) ∨
      ((checkpoint.getD (.empty, 0)).2 = SegmentedCheckpointReport.generation before ∧
        binding = some cut.checkpoint.manifest)) ∧
    recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode before.history) = .ok table ∧
    table.committed.toNat = before.history.length ∧ table.Refines model ∧
    RepresentsWalHistory before.history model ∧ PendingClientReplay log reads before.history

/-- Every manifest reported to survive the reached checkpoint barrier
has its exact ordered run bytes. The selected checkpoint and unchanged
WAL reconstruct the old client history, even before any open returns. -/
theorem CheckpointManifestDirectoryCut.replaysPending {directory : DiskDirectory}
    {before : SegmentedWriterState} {writer : Nat}
    {cut : CheckpointPowerCut directory before} {published : Image}
    {runs : RunUnlinkImage} {manifests : List (Option ByteArray)}
    (observed : CheckpointManifestDirectoryCut cut published runs manifests)
    (ready : before.RetainedReady directory writer) (replay : PendingClientReplay log reads before.history)
    {binding : Option ByteArray} (survived : binding ∈ manifests) :
    cut.PendingReplay runs binding log reads := by
  obtain ⟨expected, ran, _, _, _, afterCrash⟩ := cut.selectsAcknowledgedHistory ready
  have same := Option.some.inj (ran.symm.trans observed.executed)
  subst expected
  let pair : DirectoryPublication.Bindings := ⟨binding, before.wal.directory.active.walBoundary⟩
  have pairSurvives : pair ∈ (published.segmentedCheckpointView before.wal).directory.crashImages :=
    List.mem_map.mpr ⟨binding, observed.admitted binding survived, rfl⟩
  obtain ⟨_, _, _, _, _, _, _, checkpoint, table, model, selected, generation, restored, clock, refinement, represents⟩ :=
    afterCrash pairSurvives
  have origin : binding = before.wal.directory.active.manifest ∨ binding = some cut.checkpoint.manifest :=
    generation.imp And.right And.right
  have sameRuns := cut.selectedRunAgreement ready published binding origin runs.guaranteed
    observed.newRuns observed.priorRuns
  refine ⟨?_, checkpoint, table, model, SelectedIntegrityCheckpoint.withRunMap selected sameRuns.symm, generation, restored,
    clock, refinement, represents, replay⟩
  intro effective
  rw [observed.effective effective] at survived
  exact List.mem_singleton.mp survived

/-- A bootstrap-origin trace supplies the pending ledger at the same
checkpoint cut. -/
theorem CheckpointManifestDirectoryCut.replaysClient {directory : DiskDirectory}
    {before : SegmentedWriterState} {first writer : Nat}
    {initial : EStateM.Result IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession}
    (start : BootstrapClientStart directory first initial)
    (trace : SegmentedClientReadTrace directory first start.writer allowCollection log reads writer before)
    {cut : CheckpointPowerCut directory before} {published : Image}
    {runs : RunUnlinkImage} {manifests : List (Option ByteArray)}
    (observed : CheckpointManifestDirectoryCut cut published runs manifests)
    {binding : Option ByteArray} (survived : binding ∈ manifests) :
    cut.PendingReplay runs binding log reads :=
  observed.replaysPending
    (trace.writes.preservesRetained (start.bootstrap.writerReady start.held).toRetained).1
    (trace.keyValueRefinement start.bootstrap start.held) survived

/-- The actual prepared checkpoint has poisoned the old session at its
issued directory barrier. The returned callbacks and reported survivors of
this invocation determine the pending client replay. -/
theorem CheckpointPowerCut.replaysClientAtManifestDirectory {directory : DiskDirectory}
    {before : SegmentedWriterState} {first writer : Nat}
    {initial : EStateM.Result IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession}
    (cut : CheckpointPowerCut directory before)
    (start : BootstrapClientStart directory first initial)
    (trace : SegmentedClientReadTrace directory first start.writer allowCollection log reads writer before)
    (calls : CheckpointManifestDirectoryCalls) (atRun : Nat → CheckpointManifestState)
    (runs : CheckpointManifestState → RunUnlinkImage)
    (runPrefix : CheckpointRunPrefix cut (calls.perform cut) atRun runs)
    (reached : CheckpointManifestDirectoryReached cut calls (atRun cut.checkpoint.table.runs.length) runs)
    (completed : cut.completed = runSteps cut.checkpoint.table.runs.length ++
      [.syncRunsDirectory, .manifest .writeStaged, .manifest .syncStaged, .manifest .renameStaged]) :
    let cache := (atRun cut.checkpoint.table.runs.length).1.consume (directory.file .stagedManifest)
    let atBarrier : CheckpointManifestState := (cache, reached.renamed)
    let interrupted : CheckpointManifestState := (cache, reached.interrupted)
    CheckpointIssue ((calls.callbacks directory).perform directory) (.ready before.installed)
      ⟨atRun 0, before.owners⟩ cut.checkpoint.prepared cut.checkpoint.manifest
      cut.completed (.manifest .syncDirectory) atBarrier ∧
    (∀ binding ∈ reached.crashBindings.flatMap (manifestCrashBytes reached.interrupted),
      cut.PendingReplay (runs interrupted) binding log reads) := by
  intro cache atBarrier interrupted
  have ready := (trace.writes.preservesRetained (start.bootstrap.writerReady start.held).toRetained).1
  obtain ⟨returned, _, _, _, _, physical⟩ := cut.atManifestDirectory ready calls atRun runs runPrefix reached completed
  have preflight := cut.checkpoint.preflight cut.flushed cut.generationFits cut.runCountFits cut.encoded
  have issued := preflight.reachesIssue ((calls.callbacks directory).perform directory)
    ⟨atRun 0, before.owners⟩ cut.schedule returned
  exact ⟨physical.current ▸ issued, fun _ survived => physical.replaysClient start trace survived⟩

end Alvoki.Storage.DiskSession
