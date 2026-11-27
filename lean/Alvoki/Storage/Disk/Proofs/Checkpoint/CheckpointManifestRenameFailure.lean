import Alvoki.Storage.Disk.Proofs.Checkpoint.CheckpointManifestRenameCut
import Alvoki.Storage.Disk.Proofs.Checkpoint.CheckpointLiveHeldReopen
import Alvoki.Storage.Disk.Proofs.Recovery.SegmentedFailureRelease

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication
open WAL.Boundary (WalInodeImage)

private abbrev RenameState := SyncHandleRouting.Cache (DescriptorInventory × DescriptorSlot) × WalInodeImage

/-- The callback reports an error after the atomic rename effect. The
replacement is visible, the stage name is gone, and an unsynced directory
can retain either previously admitted binding. The named inodes keep the
same payloads. -/
structure ManifestRenameApplied {directory : DiskDirectory} {before : SegmentedWriterState}
    {cut : CheckpointPowerCut directory before} {calls : CheckpointManifestDirectoryCalls}
    {runEnd : RenameState} {runs : RenameState → RunUnlinkImage}
    (issued : CheckpointManifestRenamePrefix cut calls runEnd runs)
    (reached : WalInodeImage) (candidates : List (Option Nat)) : Prop where
  live : issued.bindings reached (directory.file .manifest) = some issued.inode
  stageRemoved : issued.bindings reached (directory.file .stagedManifest) = none
  visible : reached.visible issued.inode = issued.written.visible issued.inode
  choices : ∀ binding ∈ candidates, binding = some issued.inode ∨ binding = issued.oldBinding
  bytes : ∀ binding ∈ candidates, manifestCrashBytes reached binding = manifestCrashBytes issued.atRename.2 binding

/-- The reached prepared checkpoint and the reported return of the
manifest rename. Its primitive report admits an untouched prefix or the
complete atomic replacement. Neither branch reaches the final sync. -/
structure ObservedManifestRenameFailure {directory : DiskDirectory} {before : SegmentedWriterState}
    (cut : CheckpointPowerCut directory before) where
  calls : CheckpointManifestDirectoryCalls
  atRun : Nat → RenameState
  runs : RenameState → RunUnlinkImage
  runPrefix : CheckpointRunPrefix cut (calls.perform cut) atRun runs
  issued : CheckpointManifestRenamePrefix cut calls (atRun cut.checkpoint.table.runs.length) runs
  completed : cut.completed = runSteps cut.checkpoint.table.runs.length ++
    [.syncRunsDirectory, .manifest .writeStaged, .manifest .syncStaged]
  reached : WalInodeImage
  cause : IO.Error
  failed : calls.rename (directory.file .stagedManifest) (directory.file .manifest) issued.atRename =
    .error cause (issued.atRename.1, reached)
  crashBindings : List (Option Nat)
  beforeEffect : cut.tookEffect = false → reached = issued.atRename.2 ∧ crashBindings = [issued.oldBinding]
  afterEffect : cut.tookEffect = true → ManifestRenameApplied issued reached crashBindings
  runNames : runs (issued.atRename.1, reached) = runs issued.atRename

namespace ObservedManifestRenameFailure

variable {directory : DiskDirectory} {before : SegmentedWriterState} {cut : CheckpointPowerCut directory before}

def after (report : ObservedManifestRenameFailure cut) : RenameState := (report.issued.atRename.1, report.reached)

/-- The exact post-error projection keeps synced scratch until the rename
effect. The live and crash bindings use the same reached inode image. -/
def publication (report : ObservedManifestRenameFailure cut) : Image :=
  ⟨⟨(report.issued.bindings report.reached (directory.file .manifest)).map report.reached.visible,
    report.crashBindings.flatMap (manifestCrashBytes report.reached),
    if cut.tookEffect then none else some (cut.checkpoint.manifest, true)⟩, (report.runs report.after).guaranteed⟩

theorem liveManifest (report : ObservedManifestRenameFailure cut) :
    report.publication.manifest.active = (if cut.tookEffect then some cut.checkpoint.manifest
      else before.wal.directory.active.manifest) := by
  change (report.issued.bindings report.reached (directory.file .manifest)).map report.reached.visible = _
  cases took : cut.tookEffect with
  | false =>
    rw [(report.beforeEffect took).1]
    exact report.issued.oldVisible
  | true =>
    have applied := report.afterEffect took
    rw [applied.live, Option.map_some, applied.visible]
    exact congrArg some report.issued.stageBytes

theorem oldCrashChoice (report : ObservedManifestRenameFailure cut) (beforeEffect : cut.tookEffect = false) :
    report.publication.manifest.crashImages = [before.wal.directory.active.manifest] := by
  change report.crashBindings.flatMap (manifestCrashBytes report.reached) = _
  obtain ⟨state, bindings⟩ := report.beforeEffect beforeEffect
  rw [state, bindings, List.flatMap_singleton]
  exact report.issued.priorCrashBytes

/-- Before the effect the exact synced scratch inode is still at its
original name. A reported atomic replacement removes that name. -/
theorem stageBinding (report : ObservedManifestRenameFailure cut) :
    report.issued.bindings report.reached (directory.file .stagedManifest) =
      (if cut.tookEffect then none else some report.issued.inode) := by
  cases took : cut.tookEffect with
  | false =>
    rw [(report.beforeEffect took).1]
    exact report.issued.stageBinding
  | true => exact (report.afterEffect took).stageRemoved

theorem settledRuns (report : ObservedManifestRenameFailure cut) :
    report.publication.durable = (report.runs (report.atRun cut.checkpoint.table.runs.length)).visible := by
  change (report.runs report.after).guaranteed = _
  rw [show report.runs report.after = _ from report.runNames, report.issued.runNamesSettled]
  exact congrArg Image.durable (RunUnlinkImage.project_settled _ (.settled none))

/-- Execute the actual checkpoint prefix and the reported rename. The
unwrapped rename error returns immediately from the full file schedule. -/
theorem returns (report : ObservedManifestRenameFailure cut) :
    run cut.checkpoint.table.runs.length (report.calls.perform cut) (report.atRun 0) =
      .error report.cause report.after := by
  let perform := report.calls.perform cut
  have order : steps cut.checkpoint.table.runs.length =
      cut.completed ++ [.manifest .renameStaged, .manifest .syncDirectory] := by
    rw [report.completed]
    simp [steps, Publication.steps, List.append_assoc]
  have prefixRan : (cut.completed.forM perform) (report.atRun 0) = .ok () report.issued.atRename := by
    rw [report.completed]
    exact report.issued.returns report.runPrefix
  have failed : perform (.manifest .renameStaged) report.issued.atRename = .error report.cause report.after := report.failed
  rw [run, order, List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM]
  change EStateM.bind (cut.completed.forM perform)
    (fun _ => [Step.manifest .renameStaged, .manifest .syncDirectory].forM perform) (report.atRun 0) = _
  simp only [EStateM.bind, prefixRan, List.forM_eq_forM, List.forM_cons, Bind.bind, failed]

/-- The poisoned writer retains the exact reported image and existing
lock until close or the reported last reference drop. -/
theorem poisonsAndReleases (report : ObservedManifestRenameFailure cut) {writer : Nat}
    (ready : before.RetainedReady directory writer) (release : SegmentedFailureRelease writer) :
    let poisoned : Phase Installed × LockedFileState RenameState := (.poisoned, ⟨report.after, before.owners⟩)
    let released : LockedFileState RenameState := ⟨report.after, before.owners.set (directory.file .lock) none⟩
    runPreparedCheckpoint cut.checkpoint.prepared (report.calls.perform cut)
      (.ready before.installed, ⟨report.atRun 0, before.owners⟩) = .error report.cause poisoned ∧
    release.Observed (directory := directory) poisoned released ∧
    TryLockObserves released.owners directory (.ok true) := by
  obtain ⟨poisoned, closed, dropped, vacant⟩ := runPreparedCheckpoint_failure_handoff
    (before := ⟨report.atRun 0, before.owners⟩) before.installed cut.checkpoint.prepared
    (report.calls.perform cut) report.returns ready.held
  refine ⟨poisoned, ?_, vacant⟩
  cases release with
  | closed => exact closed
  | references held events last => exact dropped held events last

private theorem modeledPublication (report : ObservedManifestRenameFailure cut) {writer : Nat}
    (ready : before.RetainedReady directory writer) :
    ∃ logical, before.published.executeVersioned cut.checkpoint.plan cut.checkpoint.cut = some logical ∧
      logical.manifest.active = (if cut.tookEffect then some cut.checkpoint.manifest else before.wal.directory.active.manifest) ∧
      logical.manifest.crashImages = (if cut.tookEffect then [some cut.checkpoint.manifest, before.wal.directory.active.manifest]
        else [before.wal.directory.active.manifest]) ∧
      (∀ index, logical.durable (SegmentedCheckpointReport.generation before) index = cut.checkpoint.plan.files[index]?) ∧
      ∀ older, older ≠ SegmentedCheckpointReport.generation before → ∀ index,
        logical.durable older index = before.published.durable older index := by
  let count := cut.checkpoint.table.runs.length
  have planCount : cut.checkpoint.plan.files.length = count := by simp [SegmentedCheckpointReport.plan, VersionedRunSet.integrity, count]
  have prior : before.published.manifest.active = before.wal.directory.active.manifest := by
    simp [ready.manifestFiles, ready.directoryFiles, DirectoryPublication.Image.project, DirectoryPublication.Bindings.get]
  have choices : before.published.manifest.crashImages = [before.wal.directory.active.manifest] := by
    simp [ready.manifestFiles, ready.directoryFiles, DirectoryPublication.Image.project, DirectoryPublication.Bindings.get,
      ready.walDirectorySettled]
  have cutLength : cut.checkpoint.cut = (runSteps count).length + 1 + (2 + if cut.tookEffect then 1 else 0) := by
    rw [cut.reachedCount.1, report.completed, List.length_append]
    simp [count] <;> omega
  obtain ⟨written, ran, same, durable, older⟩ := checkpoint_runs_complete before.published cut.checkpoint.plan.runSet
  have executes := before.published.executeVersioned_atManifestRename cut.checkpoint.plan written ran same planCount
    cut.plannedManifestBytes cut.tookEffect
  rw [← cutLength] at executes
  refine ⟨_, executes, ?_, ?_, durable, older⟩
  · cases cut.tookEffect <;> simp [prior]
  · cases cut.tookEffect <;> simp [choices]

/-- The same physical callback report rules out a replacement before the
rename effect. The old live binding may be a crash survivor
after the rename until a directory barrier takes effect. -/
theorem selection (report : ObservedManifestRenameFailure cut) (binding : Option ByteArray)
    (found : binding = report.publication.manifest.active ∨ binding ∈ report.publication.manifest.crashImages) :
    binding = before.wal.directory.active.manifest ∨ (cut.tookEffect = true ∧ binding = some cut.checkpoint.manifest) := by
  rcases found with active | survived
  · rw [report.liveManifest] at active
    cases took : cut.tookEffect <;> simp_all
  · cases took : cut.tookEffect with
    | false =>
      rw [report.oldCrashChoice took] at survived
      exact .inl (List.mem_singleton.mp survived)
    | true =>
      change binding ∈ report.crashBindings.flatMap (manifestCrashBytes report.reached) at survived
      obtain ⟨inode, member, bytes⟩ := List.mem_flatMap.mp survived
      have applied := report.afterEffect took
      rw [applied.bytes inode member] at bytes
      rcases applied.choices inode member with fresh | prior
      · rw [fresh, report.issued.stagedCrashBytes] at bytes
        exact .inr ⟨rfl, List.mem_singleton.mp bytes⟩
      · rw [prior, report.issued.priorCrashBytes] at bytes
        exact .inl (List.mem_singleton.mp bytes)

/-- Exact returned rename failure, handoff, and selected held reopen. -/
structure Reopened (report : ObservedManifestRenameFailure cut) {writer : Nat} {input : FilePath}
    {retry : LockedFileState WalSegmentRepair.FileImage} {layout : CanonicalKeeperLayout retry.image before.history}
    (release : SegmentedFailureRelease writer) (opened : CheckpointHeldOpen input directory layout report.publication)
    (session : SegmentedSession) (final : LockedFileState WalSegmentRepair.FileImage) (after : SegmentedWriterState) : Prop extends
      CheckpointLiveHeldReopened opened session final after where
  poisoned : runCheckpointWithEffects ((report.calls.callbacks directory).perform directory)
      (.ready before.installed, ⟨report.atRun 0, before.owners⟩) =
    .error report.cause (.poisoned, ⟨report.after, before.owners⟩)
  handoff : release.Observed (directory := directory) (.poisoned, ⟨report.after, before.owners⟩)
    ⟨report.after, before.owners.set (directory.file .lock) none⟩
  attempts : BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
    ⟨CheckpointPowerCut.physical before report.publication, before.owners.set (directory.file .lock) none⟩ retry
  choice : retry.image.directory.active.manifest = before.wal.directory.active.manifest ∨
    (cut.tookEffect = true ∧ retry.image.directory.active.manifest = some cut.checkpoint.manifest)

/-- Bounded retry starts at the exact released rename-error image. The
selected checkpoint uses only the same old or newly synced physical runs
and the admitted session replays the unchanged acknowledged WAL. -/
theorem reopens (report : ObservedManifestRenameFailure cut) {writer : Nat} {input : FilePath}
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
  obtain ⟨logical, executed, live, modeled, fresh, older⟩ := report.modeledPublication ready
  have choices (binding : Option ByteArray) (found : binding ∈ publication.manifest.crashImages) :
      binding ∈ logical.manifest.crashImages := by
    have allowed := report.selection binding (.inr found)
    rw [modeled]
    cases took : cut.tookEffect <;> simp_all [or_comm]
  have runMap : publication.durable = (report.runs (report.atRun cut.checkpoint.table.runs.length)).visible := report.settledRuns
  have newRuns : ∀ index < cut.checkpoint.table.runs.length,
      publication.durable (SegmentedCheckpointReport.generation before) index =
        logical.durable (SegmentedCheckpointReport.generation before) index := by
    intro index within
    rw [runMap, report.runPrefix.freshVisible index within, fresh index]
  have oldRuns : SelectedRunsAgree before.wal.directory.active.manifest publication.durable logical.durable := by
    intro bytes metadata binding decoded index within
    rw [runMap, report.runPrefix.priorVisible bytes metadata binding decoded index within,
      older _ (cut.priorSelectedGeneration ready binding decoded).2 _]
  have agrees (binding : Option ByteArray)
      (found : binding = publication.manifest.active ∨ binding ∈ publication.manifest.crashImages) :
      SelectedRunsAgree binding publication.durable logical.durable :=
    cut.selectedRunAgreement ready logical binding ((report.selection binding found).imp id And.right)
      publication.durable newRuns oldRuns
  obtain ⟨layout, opened, session, final, after, endpoint⟩ := cut.reopensFromLive ready logical publication executed
    (report.liveManifest.trans live.symm) choices agrees retry attempts reads
  obtain ⟨poisoned, handoff, _⟩ := report.poisonsAndReleases ready release
  exact ⟨layout, opened, session, final, after, endpoint,
    cut.preflight.publicationError (report.calls.callbacks directory) directory poisoned,
    handoff, attempts, report.selection _ endpoint.selectedManifest⟩

end ObservedManifestRenameFailure

end Alvoki.Storage.DiskSession
