import Alvoki.Storage.Disk.Checkpoint.Manifest.RenamePrefix
import Alvoki.Storage.Disk.Proofs.Checkpoint.PriorCheckpointLiveReopen
import Alvoki.Storage.Disk.Proofs.Recovery.SegmentedFailureRelease

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting
open WAL.Boundary (WalInodeImage)

private abbrev RunDirectoryHandle := DescriptorInventory × DescriptorSlot
private abbrev RunDirectoryState := Cache RunDirectoryHandle × WalInodeImage

/-- A returned error from syncing the run names. The directory slot is
the one in the reached cache, and its canonical binding and reference
are observed at the effect. The effect settles names without changing
inode bytes or reaching any manifest callback. -/
structure ObservedCheckpointRunDirectoryFailure {directory : DiskDirectory} {before : SegmentedWriterState}
    (cut : CheckpointPowerCut directory before) where
  calls : CheckpointManifestDirectoryCalls
  atRun : Nat → RunDirectoryState
  runs : RunDirectoryState → RunUnlinkImage
  manifest : RunDirectoryState → Publication.Image
  views : ∀ index, RunDirectoryInodeView directory (atRun index).2 (runs (atRun index))
  entry : CheckpointRunPrefix.EntrySelection before (views 0)
  pairs : ∀ index < cut.checkpoint.table.runs.length,
    Nonempty (CheckpointRunPairCustody directory (SegmentedCheckpointReport.generation before) cut.checkpoint.table
      (calls.perform cut) (atRun index) (atRun (index + 1)) (views index) (views (index + 1)) index)
  completed : cut.completed = runSteps cut.checkpoint.table.runs.length
  directoryHandle : RunDirectoryHandle
  captured : (atRun cut.checkpoint.table.runs.length).1.directory = some directoryHandle
  drops : List LockReferenceDrop
  retained : directoryHandle.2.reference ∈ (directoryHandle.1.afterDrops drops).references directoryHandle.2.description
  directoryBound : (views cut.checkpoint.table.runs.length).visible directory.path =
    some (directoryHandle.1.inode directoryHandle.2.description)
  cause : IO.Error
  reached : WalInodeImage
  failed : calls.fsync directoryHandle (atRun cut.checkpoint.table.runs.length).2 = .error cause reached
  unchangedBeforeEffect : cut.tookEffect = false → reached = (atRun cut.checkpoint.table.runs.length).2
  visibleBytes : reached.visible = (atRun cut.checkpoint.table.runs.length).2.visible
  crashBytes : reached.crashBytes = (atRun cut.checkpoint.table.runs.length).2.crashBytes
  names :
    let atBarrier := atRun cut.checkpoint.table.runs.length
    runs (atBarrier.1, reached) = if cut.tookEffect then (runs atBarrier).syncDirectory else runs atBarrier
  entryManifest : manifest (atRun 0) = before.published.manifest
  earlierManifest : ∀ index < cut.checkpoint.table.runs.length, manifest (atRun (index + 1)) = manifest (atRun index)
  reachedManifest : manifest ((atRun cut.checkpoint.table.runs.length).1, reached) =
    manifest (atRun cut.checkpoint.table.runs.length)

namespace ObservedCheckpointRunDirectoryFailure

variable {directory : DiskDirectory} {before : SegmentedWriterState} {cut : CheckpointPowerCut directory before}

def atBarrier (report : ObservedCheckpointRunDirectoryFailure cut) : RunDirectoryState :=
  report.atRun cut.checkpoint.table.runs.length

def after (report : ObservedCheckpointRunDirectoryFailure cut) : RunDirectoryState := (report.atBarrier.1, report.reached)

def error (report : ObservedCheckpointRunDirectoryFailure cut) : IO.Error :=
  IO.userError s!"sync failed for '{directory.path}': {report.cause}"

def publication (report : ObservedCheckpointRunDirectoryFailure cut) : Image :=
  (report.runs report.after).project (report.manifest report.after)

/-- The reached directory sync uses the captured live slot and the
canonical directory inode. Its callback is the same as the worker's. -/
theorem reachesDirectory (report : ObservedCheckpointRunDirectoryFailure cut) {writer : Nat}
    (ready : before.RetainedReady directory writer) :
    cut.current = .syncRunsDirectory ∧
    (cut.completed.forM (report.calls.perform cut)) (report.atRun 0) = .ok () report.atBarrier ∧
    report.directoryHandle.2.reference ∈
      (report.directoryHandle.1.afterDrops report.drops).references report.directoryHandle.2.description ∧
    (report.views cut.checkpoint.table.runs.length).visible directory.path =
      some (report.directoryHandle.1.inode report.directoryHandle.2.description) ∧
    report.calls.perform cut cut.current report.atBarrier =
      SyncPathGroup.run (m := EStateM IO.Error RunDirectoryState)
        (fun _ (cache, image) => withCache cache (report.calls.fsync report.directoryHandle image)) #[directory.path] report.atBarrier := by
  obtain ⟨current, ran, routed, _⟩ := cut.atRunDirectory ready report.completed report.calls.writeRun
    (fun path bytes => stageFreshWithCache path bytes report.calls.stage)
    report.calls.openRead report.calls.fsync report.calls.rename report.atRun report.after
    report.runs report.manifest report.views report.directoryHandle report.pairs report.entry report.captured
    report.names report.entryManifest report.earlierManifest report.reachedManifest
  exact ⟨current, ran, report.retained, report.directoryBound, routed⟩

/-- The exact reached cache and inode state is returned through the
single-path group. The first directory sync fails before staging the
manifest, so the full file schedule returns the path-wrapped error. -/
theorem returns (report : ObservedCheckpointRunDirectoryFailure cut) {writer : Nat}
    (ready : before.RetainedReady directory writer) :
    run cut.checkpoint.table.runs.length (report.calls.perform cut) (report.atRun 0) = .error report.error report.after := by
  obtain ⟨_, prefixRan, _, _, routed⟩ := report.reachesDirectory ready
  let perform : Step → EStateM IO.Error RunDirectoryState Unit := report.calls.perform cut
  let cached (_ : FilePath) : EStateM IO.Error RunDirectoryState Unit :=
    fun (cache, image) => withCache cache (report.calls.fsync report.directoryHandle image)
  have failure : perform cut.current report.atBarrier = .error report.error report.after := by
    change report.calls.perform cut cut.current report.atBarrier = _
    rw [routed]
    change SyncPathGroup.run cached #[directory.path] report.atBarrier = _
    rw [SyncPathGroup.run_single cached]
    have raw : cached directory.path report.atBarrier = .error report.cause report.after := by
      exact congrArg (withCache report.atBarrier.1) report.failed
    rw [raw]
    rfl
  rw [run, cut.schedule, List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM]
  change EStateM.bind (cut.completed.forM perform) (fun _ => (cut.current :: cut.remaining).forM perform) (report.atRun 0) = _
  change (cut.completed.forM perform) (report.atRun 0) = .ok () report.atBarrier at prefixRan
  simp only [EStateM.bind, prefixRan, List.forM_eq_forM, List.forM_cons, Bind.bind, failure]

/-- Both error timings keep the exact written run bytes and visible
names. An effective barrier makes the new names durable. A failure
before the effect keeps the reached run namespace unchanged. -/
theorem runEffects (report : ObservedCheckpointRunDirectoryFailure cut) {writer : Nat}
    (ready : before.RetainedReady directory writer) :
    (cut.tookEffect = false → report.after = report.atBarrier ∧ report.runs report.after = report.runs report.atBarrier) ∧
    (cut.tookEffect = true → report.runs report.after = (report.runs report.atBarrier).syncDirectory ∧
      ∀ index < cut.checkpoint.table.runs.length,
        report.publication.durable (SegmentedCheckpointReport.generation before) index = cut.checkpoint.plan.files[index]?) ∧
    report.after.2.visible = report.atBarrier.2.visible ∧ report.after.2.crashBytes = report.atBarrier.2.crashBytes := by
  have runPrefix := cut.reportedRunPrefix ready (report.calls.perform cut) report.atRun report.runs report.views report.pairs report.entry
  refine ⟨?_, ?_, report.visibleBytes, report.crashBytes⟩
  · intro took
    have same : report.after = report.atBarrier := Prod.ext rfl (report.unchangedBeforeEffect took)
    exact ⟨same, congrArg report.runs same⟩
  · intro took
    have names : report.runs report.after = if cut.tookEffect then (report.runs report.atBarrier).syncDirectory
        else report.runs report.atBarrier := report.names
    rw [took] at names
    have settled : report.runs report.after = (report.runs report.atBarrier).syncDirectory := names
    refine ⟨settled, ?_⟩
    intro index within
    change (report.runs report.after).guaranteed (SegmentedCheckpointReport.generation before) index = _
    rw [settled]
    have sameMap := congrArg Image.durable (RunUnlinkImage.project_settled (report.runs report.atBarrier).visible (.settled none))
    exact (congrFun (congrFun sameMap (SegmentedCheckpointReport.generation before)) index).trans (runPrefix.freshVisible index within)

/-- The run directory effect leaves the prior manifest, including its
scratch projection, at the same reached publication. -/
theorem priorManifest (report : ObservedCheckpointRunDirectoryFailure cut) :
    report.publication.manifest = before.published.manifest := by
  have framed (through : Nat) (bounded : through ≤ cut.checkpoint.table.runs.length) :
      report.manifest (report.atRun through) = before.published.manifest := by
    induction through with
    | zero => exact report.entryManifest
    | succ previous ih =>
      exact (report.earlierManifest previous bounded).trans (ih (Nat.le_trans (Nat.le_succ _) bounded))
  exact report.reachedManifest.trans (framed _ (Nat.le_refl _))

/-- Either directory outcome retains the earlier selected run bytes. -/
theorem priorRuns (report : ObservedCheckpointRunDirectoryFailure cut) {writer : Nat}
    (ready : before.RetainedReady directory writer) :
    SelectedRunsAgree before.wal.directory.active.manifest report.publication.durable before.published.durable := by
  have runPrefix := cut.reportedRunPrefix ready (report.calls.perform cut) report.atRun report.runs report.views report.pairs report.entry
  change SelectedRunsAgree before.wal.directory.active.manifest (report.runs report.after).guaranteed before.published.durable
  rw [show report.runs report.after = _ from report.names]
  cases took : cut.tookEffect
  · exact runPrefix.priorGuaranteed
  · change SelectedRunsAgree before.wal.directory.active.manifest (report.runs report.atBarrier).syncDirectory.guaranteed
      before.published.durable
    rw [show (report.runs report.atBarrier).syncDirectory.guaranteed = (report.runs report.atBarrier).visible from
      congrArg Image.durable (RunUnlinkImage.project_settled _ (.settled none))]
    exact runPrefix.priorVisible

/-- The failed directory sync leaves the checkpoint writer poisoned with
the original lock. Successful close or the observed last reference drop
releases the exact same reached files. -/
theorem poisonsAndReleases (report : ObservedCheckpointRunDirectoryFailure cut) {writer : Nat}
    (ready : before.RetainedReady directory writer) (release : SegmentedFailureRelease writer) :
    let poisoned : Phase Installed × LockedFileState RunDirectoryState := (.poisoned, ⟨report.after, before.owners⟩)
    let released : LockedFileState RunDirectoryState := ⟨report.after, before.owners.set (directory.file .lock) none⟩
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

/-- The actual held retry from the live image released after the first
directory error. The old checkpoint and exact reached run map are both
retained by the writer that it returns. -/
structure Reopened (report : ObservedCheckpointRunDirectoryFailure cut) {writer : Nat} {input : FilePath}
    {retry : LockedFileState WalSegmentRepair.FileImage} {layout : CanonicalKeeperLayout retry.image before.history}
    (release : SegmentedFailureRelease writer) (opened : CheckpointHeldOpen input directory layout report.publication)
    (session : SegmentedSession) (final : LockedFileState WalSegmentRepair.FileImage) (after : SegmentedWriterState) : Prop extends
      PriorCheckpointReopened opened session final after where
  poisoned : runCheckpointWithEffects ((report.calls.callbacks directory).perform directory)
      (.ready before.installed, ⟨report.atRun 0, before.owners⟩) =
    .error report.error (.poisoned, ⟨report.after, before.owners⟩)
  handoff : release.Observed (directory := directory) (.poisoned, ⟨report.after, before.owners⟩)
    ⟨report.after, before.owners.set (directory.file .lock) none⟩
  attempts : BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
    ⟨CheckpointPowerCut.physical before report.publication, before.owners.set (directory.file .lock) none⟩ retry

/-- The exact released physical image starts the bounded retry. The
original manifest still determines all read runs, even when the failed
barrier settled the new generation's names. The reported held open
installs the old checkpoint and replays the same committed WAL. -/
theorem reopens (report : ObservedCheckpointRunDirectoryFailure cut) {writer : Nat} {input : FilePath}
    (ready : before.RetainedReady directory writer) (release : SegmentedFailureRelease writer)
    (retry : LockedFileState WalSegmentRepair.FileImage) :
    let publication := report.publication
    let released := ⟨CheckpointPowerCut.physical before publication, before.owners.set (directory.file .lock) none⟩
    BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first) released retry →
    CheckpointHeldOpen.Reports input directory before retry publication publication →
    ∃ (layout : CanonicalKeeperLayout retry.image before.history)
      (opened : CheckpointHeldOpen input directory layout publication)
      (session : SegmentedSession) (final : LockedFileState WalSegmentRepair.FileImage) (after : SegmentedWriterState),
      report.Reopened release opened session final after := by
  intro publication released attempts reads
  have active : publication.manifest.active = before.wal.directory.active.manifest := by
    rw [report.priorManifest, ready.manifestFiles, ready.directoryFiles]
    rfl
  have choices : publication.manifest.crashImages = [before.wal.directory.active.manifest] := by
    rw [report.priorManifest, ready.manifestFiles, ready.directoryFiles]
    simp [DirectoryPublication.Image.project, DirectoryPublication.Bindings.get, ready.walDirectorySettled]
  obtain ⟨layout, opened, session, final, after, endpoint⟩ :=
    ready.reopensPriorCheckpointLive publication active choices (report.priorRuns ready) retry attempts reads
  obtain ⟨poisoned, handoff, _⟩ := report.poisonsAndReleases ready release
  exact ⟨layout, opened, session, final, after, endpoint,
    cut.preflight.publicationError (report.calls.callbacks directory) directory poisoned, handoff, attempts⟩

end ObservedCheckpointRunDirectoryFailure

end Alvoki.Storage.DiskSession
