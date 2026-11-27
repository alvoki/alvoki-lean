import Alvoki.Storage.Disk.CheckpointManifestDirectoryCut
import Alvoki.Storage.Disk.SegmentedFailureRelease

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting
open WAL.Boundary (WalInodeImage)

private abbrev DirectoryHandle := DescriptorInventory × DescriptorSlot
private abbrev DirectoryState := Cache DirectoryHandle × WalInodeImage

/-- The shared cut counts the prefix effects. This report adds the actual
returned error and its image. The effect flag settles crash choices while
the live manifest already names the new inode. -/
structure ObservedManifestDirectoryFailure {directory : DiskDirectory} {before : SegmentedWriterState}
    (cut : CheckpointPowerCut directory before) where
  calls : CheckpointManifestDirectoryCalls
  atRun : Nat → DirectoryState
  runs : DirectoryState → RunUnlinkImage
  runPrefix : CheckpointRunPrefix cut (calls.perform cut) atRun runs
  reached : CheckpointManifestDirectoryReached cut calls (atRun cut.checkpoint.table.runs.length) runs
  completed : cut.completed = runSteps cut.checkpoint.table.runs.length ++
    [.syncRunsDirectory, .manifest .writeStaged, .manifest .syncStaged, .manifest .renameStaged]
  cause : IO.Error
  failed : calls.fsync reached.directoryHandle reached.renamed = .error cause reached.interrupted
  liveBinding : reached.bindings reached.interrupted (directory.file .manifest) =
    reached.bindings reached.renamed (directory.file .manifest)
  liveBytes : reached.interrupted.visible (reached.stageHandle.1.inode reached.stageHandle.2.description) =
    reached.written.visible (reached.stageHandle.1.inode reached.stageHandle.2.description)
  stageRemoved : reached.bindings reached.interrupted (directory.file .stagedManifest) = none

namespace ObservedManifestDirectoryFailure

variable {directory : DiskDirectory} {before : SegmentedWriterState}
  {cut : CheckpointPowerCut directory before}

def error (report : ObservedManifestDirectoryFailure cut) : IO.Error :=
  IO.userError s!"sync failed for '{directory.path}': {report.cause}"

def after (report : ObservedManifestDirectoryFailure cut) : DirectoryState :=
  ((report.atRun cut.checkpoint.table.runs.length).1.consume (directory.file .stagedManifest), report.reached.interrupted)

/-- The returned error leaves the directory's new live manifest, its
reported crash choices and the exact settled run map. -/
def publication (report : ObservedManifestDirectoryFailure cut) : Image :=
  ⟨⟨(report.reached.bindings report.after.2 (directory.file .manifest)).map report.after.2.visible,
    report.reached.crashBindings.flatMap (manifestCrashBytes report.after.2), none⟩,
  (report.runs report.after).guaranteed⟩

theorem liveManifest (report : ObservedManifestDirectoryFailure cut) :
    report.publication.manifest.active = some cut.checkpoint.manifest := by
  change (report.reached.bindings report.reached.interrupted (directory.file .manifest)).map
    report.reached.interrupted.visible = _
  rw [report.liveBinding, report.reached.liveBinding, Option.map_some]
  change some (report.reached.interrupted.visible (report.reached.stageHandle.1.inode
    report.reached.stageHandle.2.description)) = _
  rw [report.liveBytes]
  exact congrArg some report.reached.stageBytes

/-- The exact reported prefix reaches the same retained directory fsync.
Its error is wrapped by the real grouped sync, which retains the
reached cache and filesystem state. -/
theorem returns (report : ObservedManifestDirectoryFailure cut) {writer : Nat}
    (ready : before.RetainedReady directory writer) :
    run cut.checkpoint.table.runs.length (report.calls.perform cut) (report.atRun 0) =
      .error report.error report.after := by
  obtain ⟨ran, _, _, routed, _, selected⟩ := cut.atManifestDirectory ready report.calls report.atRun report.runs
    report.runPrefix report.reached report.completed
  let cache := (report.atRun cut.checkpoint.table.runs.length).1.consume (directory.file .stagedManifest)
  let atBarrier : DirectoryState := (cache, report.reached.renamed)
  have prefixRan : (cut.completed.forM (report.calls.perform cut)) (report.atRun 0) = .ok () atBarrier := ran
  have failure : report.calls.perform cut cut.current atBarrier = .error report.error report.after := by
    change report.calls.perform cut cut.current atBarrier = .error report.error (cache, report.reached.interrupted)
    let cached (_ : FilePath) : EStateM IO.Error DirectoryState Unit :=
      fun (files, image) => withCache files (report.calls.fsync report.reached.directoryHandle image)
    rw [routed]
    change SyncPathGroup.run cached #[directory.path] atBarrier = _
    rw [SyncPathGroup.run_single cached]
    have raw : cached directory.path atBarrier = .error report.cause (cache, report.reached.interrupted) := by
      change withCache cache (report.calls.fsync report.reached.directoryHandle report.reached.renamed) = _
      rw [report.failed]
      rfl
    rw [raw]
    rfl
  have schedule : steps cut.checkpoint.table.runs.length = cut.completed ++ [cut.current] := by
    rw [report.completed, selected.current]
    simp [steps, Publication.steps, List.append_assoc]
  rw [run, schedule, List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM]
  change EStateM.bind (cut.completed.forM (report.calls.perform cut))
    (fun _ => [cut.current].forM (report.calls.perform cut)) (report.atRun 0) = _
  rw [show [cut.current].forM (report.calls.perform cut) = report.calls.perform cut cut.current by
    simp [List.forM_eq_forM, List.forM_cons, List.forM_nil]]
  simp only [EStateM.bind, prefixRan, failure]

/-- The publication error keeps the writer poisoned under its original
lock. Successful close or the reported last reference drop releases
exactly the returned files. -/
theorem poisonsAndReleases (report : ObservedManifestDirectoryFailure cut) {writer : Nat}
    (ready : before.RetainedReady directory writer) (release : SegmentedFailureRelease writer) :
    let poisoned : Phase Installed × LockedFileState DirectoryState := (.poisoned, ⟨report.after, before.owners⟩)
    let released : LockedFileState DirectoryState := ⟨report.after, before.owners.set (directory.file .lock) none⟩
    runPreparedCheckpoint cut.checkpoint.prepared (report.calls.perform cut)
      (.ready before.installed, ⟨report.atRun 0, before.owners⟩) = .error report.error poisoned ∧
    release.Observed (directory := directory) poisoned released ∧
    TryLockObserves released.owners directory (.ok true) := by
  obtain ⟨poisoned, closed, dropped, vacant⟩ := runPreparedCheckpoint_failure_handoff
    (before := ⟨report.atRun 0, before.owners⟩) before.installed cut.checkpoint.prepared
    (report.calls.perform cut) (report.returns ready) ready.held
  refine ⟨poisoned, ?_, vacant⟩
  cases release with
  | closed => exact closed
  | references held events last => exact dropped held events last

end ObservedManifestDirectoryFailure

end Alvoki.Storage.DiskSession
