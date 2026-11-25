import Alvoki.Storage.Disk.NativeReadyCheckpoint
import Alvoki.Storage.Disk.Checkpoint.PendingClientReplay

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting
open WalSegmentRepair (FileImage)

/-- The final checkpoint directory sync returns an error after the actual
run prefix and manifest rename. The descriptor report uses the same live
directory and writer slots reached by that prefix. -/
structure NativeCheckpointDirectoryError {image : Type} (state : NativeReadyState)
    (cut : CheckpointPowerCut state.session.directory state.writer) where
  callbacks : CheckpointFileCallbacks (CensusDirectoryCache × image)
  observed : ReturnedCheckpointPrefix
    (callbacks.perform state.session.directory cut.checkpoint.prepared cut.checkpoint.manifest)
    cut.checkpoint.table.runs.length
  callbackPrefix : NativeCheckpointPrefix state observed
  completed : cut.completed = manifestDirectoryPrefix cut.checkpoint.table.runs.length
  cause : IO.Error
  after : image
  failed : callbackPrefix.primitives.fsync (callbackPrefix.capturedDirectory, state.directorySlot, 0) observed.renamed.2 =
    .error cause after
  census : callbackPrefix.descriptors after = callbackPrefix.descriptors observed.renamed.2
  bindings : image → FilePath → Option Nat
  heldBindings : ∀ raw ∈ [(observed.atRun cut.checkpoint.table.runs.length).2, observed.renamed.2, after],
    bindings raw state.session.directory.path = some (state.census.inode state.directorySlot.description) ∧
    bindings raw (state.session.directory.file .lock) = some (state.census.inode state.owner.description)

namespace NativeCheckpointDirectoryError

variable {image : Type} {state : NativeReadyState}
  {cut : CheckpointPowerCut state.session.directory state.writer}

def error (report : NativeCheckpointDirectoryError (image := image) state cut) : IO.Error :=
  IO.userError s!"sync failed for '{state.session.directory.path}': {report.cause}"

noncomputable def run (report : NativeCheckpointDirectoryError (image := image) state cut) :=
  runCheckpointWithEffects (report.callbackPrefix.primitives.cached.perform state.session.directory)
    (state.session.phase, ⟨(state.cache, (report.observed.atRun 0).2), state.files.owners⟩)

theorem current (report : NativeCheckpointDirectoryError (image := image) state cut) :
    cut.current = .manifest .syncDirectory := by
  have ordered := cut.schedule
  rw [report.completed, manifestDirectoryPrefix_steps] at ordered
  exact (List.cons.inj (List.append_cancel_left ordered)).1.symm

/-- The sync error is interpreted by the actual checkpoint and grouped
sync. The original phase has become poisoned, and the reached native
image is returned with the same cache and logical lock owner. -/
theorem returns (report : NativeCheckpointDirectoryError (image := image) state cut)
    (valid : state.Valid) :
    report.run = .error report.error (.poisoned, ⟨(state.cache, report.after), state.files.owners⟩) := by
  have before := report.callbackPrefix.beforeFinalDirectory
  let dir := state.session.directory
  let primitives := report.callbackPrefix.primitives
  have final : primitives.cached.perform dir cut.checkpoint.prepared cut.checkpoint.manifest
      (.manifest .syncDirectory) report.observed.renamed =
      .error report.error (state.cache, report.after) := by
    have initial : report.observed.renamed = (state.cache, report.observed.renamed.2) :=
      Prod.ext before.1 rfl
    change SyncPathGroup.run (sync dir.path primitives.openRead primitives.fsync)
      #[dir.path] report.observed.renamed = _
    rw [SyncPathGroup.run_single]
    rw [initial]
    simp only [sync, Cache.resolve, beq_self_eq_true, ↓reduceIte, report.callbackPrefix.directoryCached]
    have failed : primitives.fsync (report.callbackPrefix.capturedDirectory, state.directorySlot, 0)
        report.observed.renamed.2 = .error report.cause report.after := report.failed
    simp only [failed, withCache]
    rfl
  have preflight := cut.checkpoint.preflight cut.flushed cut.generationFits cut.runCountFits cut.encoded
  have started : (state.cache, (report.observed.atRun 0).2) = report.observed.atRun 0 :=
    Prod.ext report.callbackPrefix.initialCache.symm rfl
  have sameDispatch := congrArg (fun callbacks : CheckpointFileCallbacks (CensusDirectoryCache × image) =>
    (manifestDirectoryPrefix cut.checkpoint.table.runs.length).forM
      (callbacks.perform dir cut.checkpoint.prepared cut.checkpoint.manifest)
      (state.cache, (report.observed.atRun 0).2)) report.callbackPrefix.callbacks
  have executed := sameDispatch.symm.trans (started.symm ▸ report.observed.returns)
  let files : LockedFileState (CensusDirectoryCache × image) :=
    ⟨(state.cache, (report.observed.atRun 0).2), state.files.owners⟩
  have issued := preflight.reachesIssue (primitives.cached.perform dir) files
    (manifestDirectoryPrefix_steps cut.checkpoint.table.runs.length) executed
  obtain ⟨remaining, schedule, tail⟩ := issued.continuation
  have suffix := List.append_cancel_left ((manifestDirectoryPrefix_steps cut.checkpoint.table.runs.length).symm.trans schedule)
  have empty : [] = remaining := (List.cons.inj suffix).2
  rw [← empty] at tail
  have returned : ([Step.manifest .syncDirectory].forM
      (primitives.cached.perform dir cut.checkpoint.prepared cut.checkpoint.manifest)) report.observed.renamed =
      .error report.error (state.cache, report.after) := by
    simp only [List.forM_eq_forM, List.forM_cons, Bind.bind, EStateM.bind, final]
  rw [returned] at tail
  simpa only [run, valid.phase] using tail

/-- The first directory sync and the failed final sync use the same
cached handle. Both issue states and the returned image retain the
original live directory and lock references at their canonical paths. -/
theorem custody (report : NativeCheckpointDirectoryError (image := image) state cut) (valid : state.Valid) :
    report.callbackPrefix.primitives.fsync (report.callbackPrefix.capturedDirectory, state.directorySlot, 0)
      (report.observed.atRun cut.checkpoint.table.runs.length).2 = .ok () report.observed.runsSettled.2 ∧
    ∀ raw ∈ [(report.observed.atRun cut.checkpoint.table.runs.length).2, report.observed.renamed.2, report.after],
      report.callbackPrefix.descriptors raw = state.census ∧
      state.directorySlot ∈ (report.callbackPrefix.descriptors raw).slots ∧
      state.owner ∈ (report.callbackPrefix.descriptors raw).slots ∧
      report.bindings raw state.session.directory.path =
        some (report.callbackPrefix.capturedDirectory.inode state.directorySlot.description) ∧
      report.bindings raw (state.session.directory.file .lock) = some (state.census.inode state.owner.description) := by
  obtain ⟨runCache, runCensus⟩ := report.callbackPrefix.beforeRunsDirectory _ (Nat.le_refl _)
  have before := report.callbackPrefix.beforeFinalDirectory.2
  refine ⟨report.callbackPrefix.directoryFsync runCache report.observed.syncRunsDirectory, ?_⟩
  intro raw reached
  have census : report.callbackPrefix.descriptors raw = state.census := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at reached
    rcases reached with rfl | rfl | rfl
    · exact runCensus
    · exact before
    · exact report.census.trans before
  obtain ⟨root, lock⟩ := report.heldBindings raw reached
  exact ⟨census, census.symm ▸ valid.directoryLive, census.symm ▸ valid.ownerLive,
    root.trans (congrArg some report.callbackPrefix.capturedInode.symm), lock⟩

/-- The file projections of the same returned callbacks. The joint
directory view keeps the manifest and WAL marker from one crash choice.
The final syscall reports whether its durability effect occurred. -/
structure Physical (report : NativeCheckpointDirectoryError (image := image) state cut) where
  files : image → FileImage
  runs : image → RunUnlinkImage
  initial : files (report.observed.atRun 0).2 = state.files.image
  walFrame : ∀ (done : List Step) step todo prior reached,
    manifestDirectoryPrefix cut.checkpoint.table.runs.length = done ++ step :: todo →
    (done.forM (report.callbacks.perform state.session.directory cut.checkpoint.prepared cut.checkpoint.manifest))
      (report.observed.atRun 0) = .ok () prior →
    report.callbacks.perform state.session.directory cut.checkpoint.prepared cut.checkpoint.manifest step prior =
      .ok () reached →
    CheckpointWalView.ofFiles (files reached.2) = CheckpointWalView.ofFiles (files prior.2)
  runDirectoryFrame : ∀ index < cut.checkpoint.table.runs.length,
    (files (report.observed.atRun (index + 1)).2).directory =
      (files (report.observed.atRun index).2).directory
  syncRunDirectory : (files report.observed.runsSettled.2).directory =
    (files (report.observed.atRun cut.checkpoint.table.runs.length).2).directory.syncDirectory
  runPrefix : ReturnedCheckpointRuns report.observed (fun pair => runs pair.2)
    (SegmentedCheckpointReport.generation state.writer) cut.checkpoint.plan.files
  priorRuns : SelectedRunsAgree state.writer.wal.directory.active.manifest
    (runs (report.observed.atRun 0).2).visible state.writer.published.durable
  priorRunFrame : ∀ index < cut.checkpoint.table.runs.length, ∀ generation,
    generation ≠ SegmentedCheckpointReport.generation state.writer → ∀ prior,
      (runs (report.observed.atRun (index + 1)).2).visible generation prior =
        (runs (report.observed.atRun index).2).visible generation prior
  stage : (files report.observed.runsSettled.2).directory.step .manifest cut.checkpoint.manifest .writeStaged =
    some (files report.observed.staged.2).directory
  sync : (files report.observed.staged.2).directory.step .manifest cut.checkpoint.manifest .syncStaged =
    some (files report.observed.stagedSynced.2).directory
  rename : (files report.observed.stagedSynced.2).directory.step .manifest cut.checkpoint.manifest .renameStaged =
    some (files report.observed.renamed.2).directory
  errorDirectory : (files report.after).directory = if cut.tookEffect
    then (files report.observed.renamed.2).directory.syncDirectory
    else (files report.observed.renamed.2).directory
  errorRuns : runs report.after = if cut.tookEffect then (runs report.observed.renamed.2).syncDirectory
    else runs report.observed.renamed.2
  errorWal : CheckpointWalView.ofFiles (files report.after) =
    CheckpointWalView.ofFiles (files report.observed.renamed.2)

namespace Physical

variable {report : NativeCheckpointDirectoryError (image := image) state cut}

theorem wal (physical : report.Physical) :
    CheckpointWalView.ofFiles (physical.files report.after) = CheckpointWalView.ofFiles state.files.image := by
  have ran := report.observed.returns
  have preserved := successfulFrame _ (fun pair => CheckpointWalView.ofFiles (physical.files pair.2)) ran physical.walFrame
  exact physical.errorWal.trans (preserved.trans (congrArg CheckpointWalView.ofFiles physical.initial))

theorem directory (physical : report.Physical) (valid : state.Valid) :
    let old := state.writer.wal.directory.active
    let new := old.replace .manifest cut.checkpoint.manifest
    (physical.files report.after).directory.active = new ∧
      (physical.files report.after).directory.crashImages = if cut.tookEffect then [new] else [new, old] := by
  intro old new
  let initial := state.writer.wal.directory
  let staged (synced : Bool) : DirectoryPublication.Image :=
    { initial with staged := fun entry =>
      if entry = .manifest then some (cut.checkpoint.manifest, synced) else initial.staged entry }
  have stage := physical.stage
  have previousDirectory (index : Nat) (within : index ≤ cut.checkpoint.table.runs.length) :
      (physical.files (report.observed.atRun index).2).directory = initial := by
    induction index with
    | zero => exact (congrArg FileImage.directory physical.initial).trans valid.retained.directoryFiles
    | succ index earlier =>
      exact (physical.runDirectoryFrame index within).trans (earlier (Nat.le_of_lt within))
  have priorDirectory : (physical.files report.observed.runsSettled.2).directory = initial := by
    rw [physical.syncRunDirectory, previousDirectory _ (Nat.le_refl _)]
    change { initial with crashImages := [initial.active] } = initial
    rw [← valid.retained.walDirectorySettled]

  rw [priorDirectory] at stage
  have written : (physical.files report.observed.staged.2).directory = staged false :=
    (Option.some.inj (show some (staged false) = _ from stage)).symm
  have sync := physical.sync
  rw [written] at sync
  have syncEffect : (staged false).step .manifest cut.checkpoint.manifest .syncStaged = some (staged true) := by
    change some (⟨initial.active, initial.crashImages,
      fun entry => if entry = .manifest then some (cut.checkpoint.manifest, true) else (staged false).staged entry⟩ :
        DirectoryPublication.Image) = some (staged true)
    congr 2
    funext entry
    cases entry <;> rfl
  have synced : (physical.files report.observed.stagedSynced.2).directory = staged true :=
    Option.some.inj (sync.symm.trans syncEffect)
  have renamed := physical.rename
  rw [synced] at renamed
  have visible := congrArg DirectoryPublication.Image.active (Option.some.inj (show some _ = some _ from renamed))
  have choices := congrArg DirectoryPublication.Image.crashImages (Option.some.inj (show some _ = some _ from renamed))
  change new = _ at visible
  change initial.crashImages.map (·.replace .manifest cut.checkpoint.manifest) ++ initial.crashImages = _ at choices
  rw [show initial.crashImages = [old] from valid.retained.walDirectorySettled] at choices
  rw [physical.errorDirectory]
  cases cut.tookEffect with
  | false => exact ⟨visible.symm, choices.symm⟩
  | true => exact ⟨visible.symm, congrArg (fun pair => [pair]) visible.symm⟩

theorem settledRuns (physical : report.Physical) :
    physical.runs report.after = .settled (physical.runs
      (report.observed.atRun cut.checkpoint.table.runs.length).2).visible := by
  have before : physical.runs report.observed.renamed.2 =
      (physical.runs (report.observed.atRun cut.checkpoint.table.runs.length).2).syncDirectory :=
    physical.runPrefix.renameRuns.trans
      (physical.runPrefix.syncRuns.trans (physical.runPrefix.stageRuns.trans physical.runPrefix.runNames))
  rw [physical.errorRuns, before]
  cases cut.tookEffect <;> rfl

/-- The actual returned file view selects exactly the newly encoded
manifest after an effective barrier, and admits the old and new manifest
before it. Both selections use the exact previously synced run bytes. -/
theorem selects (physical : report.Physical) (valid : state.Valid) :
    ∃ published, CheckpointManifestDirectoryCut cut published (physical.runs report.after)
      ((physical.files report.after).directory.project .manifest).crashImages := by
  obtain ⟨published, executed, visible, choices, newRuns, priorRuns⟩ :=
    cut.finalDirectoryPublication valid.retained report.completed
  obtain ⟨_, paths⟩ := physical.directory valid
  have survived : ((physical.files report.after).directory.project .manifest).crashImages =
      published.manifest.crashImages := by
    simp only [DirectoryPublication.Image.project, paths, choices]
    cases cut.tookEffect <;> rfl
  have runPayloads : (physical.runs report.after).guaranteed =
      (physical.runs (report.observed.atRun cut.checkpoint.table.runs.length).2).visible := by
    rw [physical.settledRuns]
    exact congrArg Image.durable (RunUnlinkImage.project_settled _ (.settled none))
  have fresh := visibleSyncedRunPrefix (fun index => (report.observed.atRun index).2) _
    physical.runs (SegmentedCheckpointReport.generation state.writer) cut.checkpoint.plan.files
    physical.runPrefix.syncedRun physical.runPrefix.previousRuns
  refine ⟨published, report.current, executed, visible, choices, ?_, ?_, ?_, ?_, ?_⟩
  · intro manifest member
    exact survived ▸ member
  · intro effective
    rw [survived, choices, effective]
    rfl
  · rw [physical.settledRuns]
    rfl
  · intro index inside
    rw [runPayloads, fresh index inside, newRuns index]
  · intro bytes metadata binding decoded index inside
    have unchanged := (cut.priorSelectedGeneration valid.retained binding decoded).2
    have older (through : Nat) (within : through ≤ cut.checkpoint.table.runs.length) :
        (physical.runs (report.observed.atRun through).2).visible metadata.header.generation index =
          (physical.runs (report.observed.atRun 0).2).visible metadata.header.generation index := by
      induction through with
      | zero => rfl
      | succ through earlier =>
        exact (physical.priorRunFrame through within _ unchanged index).trans (earlier (Nat.le_of_lt within))
    rw [runPayloads, older _ (Nat.le_refl _), physical.priorRuns bytes metadata binding decoded index inside,
      priorRuns _ unchanged _]

end Physical

end NativeCheckpointDirectoryError

/-- The native checkpoint error returns in the original retained
session, poisoned. Every joint manifest/marker choice in the returned
filesystem image selects the exact run bytes and replays the existing
acknowledgements and recorded reads. -/
theorem NativeReadyReadPrefix.checkpointDirectoryError
    {opened : EStateM.Result IO.Error CensusOpenState SegmentedSession}
    {initial state : NativeReadyState}
    (prior : NativeReadyReadPrefix opened initial history log reads state)
    {image : Type} {cut : CheckpointPowerCut state.session.directory state.writer}
    (report : NativeCheckpointDirectoryError (image := image) state cut) (physical : report.Physical) :
    report.run = .error report.error (.poisoned, ⟨(state.cache, report.after), state.files.owners⟩) ∧
    report.callbackPrefix.descriptors report.after = state.census ∧
    CheckpointWalView.ofFiles (physical.files report.after) = CheckpointWalView.ofFiles state.files.image ∧
    ∀ pair ∈ (physical.files report.after).directory.crashImages,
      pair.walBoundary = state.writer.wal.directory.active.walBoundary ∧
      cut.PendingReplay (physical.runs report.after) pair.manifest log reads := by
  obtain ⟨valid, history, replay⟩ := prior.refines
  obtain ⟨_, selected⟩ := physical.selects valid
  obtain ⟨_, choices⟩ := physical.directory valid
  have custody := (report.custody valid).2 report.after (by simp)
  refine ⟨report.returns valid, custody.1, physical.wal, ?_⟩
  intro pair survived
  have marker : pair.walBoundary = state.writer.wal.directory.active.walBoundary := by
    rw [choices] at survived
    split at survived
    · obtain rfl := List.mem_singleton.mp survived
      rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at survived
      rcases survived with rfl | rfl <;> rfl
  have binding : pair.manifest ∈ ((physical.files report.after).directory.project .manifest).crashImages :=
    List.mem_map_of_mem survived
  exact ⟨marker, selected.replaysPending valid.retained (history.symm ▸ replay) binding⟩

end Alvoki.Storage.DiskSession
