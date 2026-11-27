import Alvoki.Storage.Disk.Proofs.Native.Checkpoint.NativeReadyCheckpoint
import Alvoki.Storage.Disk.Proofs.Checkpoint.PendingClientReplay

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting
open WalSegmentRepair (FileImage)

/-- A native checkpoint has returned from every callback through the
manifest rename. Its next scheduled operation uses the cached directory
handle, with no outcome attached to that operation yet. -/
structure NativeCheckpointFinalBarrier {image : Type} (state : NativeReadyState)
    (cut : CheckpointPowerCut state.session.directory state.writer) where
  callbacks : CheckpointFileCallbacks (CensusDirectoryCache × image)
  observed : ReturnedCheckpointPrefix
    (callbacks.perform state.session.directory cut.checkpoint.prepared cut.checkpoint.manifest)
    cut.checkpoint.table.runs.length
  callbackPrefix : NativeCheckpointPrefix state observed
  completed : cut.completed = manifestDirectoryPrefix cut.checkpoint.table.runs.length
  bindings : image → FilePath → Option Nat
  issueBindings : ∀ raw ∈ [(observed.atRun cut.checkpoint.table.runs.length).2, observed.renamed.2],
    bindings raw state.session.directory.path = some (state.census.inode state.directorySlot.description) ∧
    bindings raw (state.session.directory.file .lock) = some (state.census.inode state.owner.description)

namespace NativeCheckpointFinalBarrier

variable {image : Type} {state : NativeReadyState}
  {cut : CheckpointPowerCut state.session.directory state.writer}

def handle (barrier : NativeCheckpointFinalBarrier (image := image) state cut) : CheckpointOpenHandle :=
  (barrier.callbackPrefix.capturedDirectory, state.directorySlot, 0)

def entry (barrier : NativeCheckpointFinalBarrier (image := image) state cut) :
    LockedFileState (CensusDirectoryCache × image) :=
  ⟨(state.cache, (barrier.observed.atRun 0).2), state.files.owners⟩

noncomputable def perform (barrier : NativeCheckpointFinalBarrier (image := image) state cut) :=
  barrier.callbackPrefix.primitives.cached.perform state.session.directory

theorem current (barrier : NativeCheckpointFinalBarrier (image := image) state cut) :
    cut.current = .manifest .syncDirectory := by
  have ordered := cut.schedule
  rw [barrier.completed, manifestDirectoryPrefix_steps] at ordered
  exact (List.cons.inj (List.append_cancel_left ordered)).1.symm

/-- The actual preflight and ordered callbacks issue the last directory
sync from the poisoned phase with the original lock owner. -/
theorem issues (barrier : NativeCheckpointFinalBarrier (image := image) state cut) (valid : state.Valid) :
    CheckpointIssue barrier.perform state.session.phase barrier.entry cut.checkpoint.prepared cut.checkpoint.manifest
      cut.completed (.manifest .syncDirectory) barrier.observed.renamed := by
  let dir := state.session.directory
  let primitives := barrier.callbackPrefix.primitives
  have preflight := cut.preflight
  have started : barrier.entry.image = barrier.observed.atRun 0 :=
    Prod.ext barrier.callbackPrefix.initialCache.symm rfl
  have dispatch := congrArg (fun callbacks : CheckpointFileCallbacks (CensusDirectoryCache × image) =>
    (manifestDirectoryPrefix cut.checkpoint.table.runs.length).forM
      (callbacks.perform dir cut.checkpoint.prepared cut.checkpoint.manifest) barrier.entry.image)
    barrier.callbackPrefix.callbacks
  have executed := dispatch.symm.trans (started.symm ▸ barrier.observed.returns)
  rw [valid.phase, barrier.completed]
  exact preflight.reachesIssue (primitives.cached.perform dir) barrier.entry
    (manifestDirectoryPrefix_steps cut.checkpoint.table.runs.length) executed

/-- The singleton group's route resolves the same cached descriptor
before any raw syscall can return. -/
theorem routes (barrier : NativeCheckpointFinalBarrier (image := image) state cut) :
    let atDirectory : FilePath → EStateM IO.Error (CensusDirectoryCache × image) Unit :=
      fun _ (cache, files) => withCache cache (barrier.callbackPrefix.primitives.fsync barrier.handle files)
    barrier.perform cut.checkpoint.prepared cut.checkpoint.manifest (.manifest .syncDirectory)
      barrier.observed.renamed =
        SyncPathGroup.run atDirectory #[state.session.directory.path] barrier.observed.renamed := by
  intro atDirectory
  let dir := state.session.directory
  let primitives := barrier.callbackPrefix.primitives
  have reached : barrier.observed.renamed = (state.cache, barrier.observed.renamed.2) :=
    Prod.ext barrier.callbackPrefix.beforeFinalDirectory.1 rfl
  change SyncPathGroup.run (sync dir.path primitives.openRead primitives.fsync) #[dir.path] barrier.observed.renamed = _
  rw [SyncPathGroup.run_single, SyncPathGroup.run_single, reached]
  simp only [sync, Cache.resolve, beq_self_eq_true, ↓reduceIte, barrier.callbackPrefix.directoryCached]
  rfl

/-- Both directory barriers address the same held directory. The actual
run and staged-manifest temporary handle releases lead to the exact
census in which the last syscall issues. -/
theorem custody (barrier : NativeCheckpointFinalBarrier (image := image) state cut) (valid : state.Valid) :
    barrier.callbackPrefix.primitives.fsync barrier.handle
      (barrier.observed.atRun cut.checkpoint.table.runs.length).2 = .ok () barrier.observed.runsSettled.2 ∧
    ∀ raw ∈ [(barrier.observed.atRun cut.checkpoint.table.runs.length).2, barrier.observed.renamed.2],
      barrier.callbackPrefix.descriptors raw = state.census ∧
      state.directorySlot ∈ (barrier.callbackPrefix.descriptors raw).slots ∧
      state.owner ∈ (barrier.callbackPrefix.descriptors raw).slots ∧
      barrier.bindings raw state.session.directory.path = some (barrier.handle.1.inode state.directorySlot.description) ∧
      barrier.bindings raw (state.session.directory.file .lock) = some (state.census.inode state.owner.description) := by
  obtain ⟨runCache, runCensus⟩ := barrier.callbackPrefix.beforeRunsDirectory _ (Nat.le_refl _)
  refine ⟨barrier.callbackPrefix.directoryFsync runCache barrier.observed.syncRunsDirectory, ?_⟩
  intro raw reached
  have census : barrier.callbackPrefix.descriptors raw = state.census := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at reached
    rcases reached with rfl | rfl
    · exact runCensus
    · exact barrier.callbackPrefix.beforeFinalDirectory.2
  obtain ⟨root, lock⟩ := barrier.issueBindings raw reached
  exact ⟨census, census.symm ▸ valid.directoryLive, census.symm ▸ valid.ownerLive,
    root.trans (congrArg some barrier.callbackPrefix.capturedInode.symm), lock⟩

end NativeCheckpointFinalBarrier

/-- The final checkpoint directory sync returns an error after the actual
run prefix and manifest rename. The descriptor report uses the same live
directory and writer slots reached by that prefix. -/
structure NativeCheckpointDirectoryError {image : Type} (state : NativeReadyState)
    (cut : CheckpointPowerCut state.session.directory state.writer)
    extends NativeCheckpointFinalBarrier (image := image) state cut where
  cause : IO.Error
  after : image
  failed : callbackPrefix.primitives.fsync (callbackPrefix.capturedDirectory, state.directorySlot, 0) observed.renamed.2 =
    .error cause after
  census : callbackPrefix.descriptors after = callbackPrefix.descriptors observed.renamed.2
  afterBindings : bindings after state.session.directory.path = some (state.census.inode state.directorySlot.description) ∧
    bindings after (state.session.directory.file .lock) = some (state.census.inode state.owner.description)

namespace NativeCheckpointDirectoryError

variable {image : Type} {state : NativeReadyState}
  {cut : CheckpointPowerCut state.session.directory state.writer}

def error (report : NativeCheckpointDirectoryError (image := image) state cut) : IO.Error :=
  IO.userError s!"sync failed for '{state.session.directory.path}': {report.cause}"

noncomputable def run (report : NativeCheckpointDirectoryError (image := image) state cut) :=
  runCheckpointWithEffects (report.callbackPrefix.primitives.cached.perform state.session.directory)
    (state.session.phase, ⟨(state.cache, (report.observed.atRun 0).2), state.files.owners⟩)

abbrev barrier (report : NativeCheckpointDirectoryError (image := image) state cut) :
    NativeCheckpointFinalBarrier (image := image) state cut :=
  report.toNativeCheckpointFinalBarrier

theorem heldBindings (report : NativeCheckpointDirectoryError (image := image) state cut)
    (raw : image) (reached : raw ∈ [(report.observed.atRun cut.checkpoint.table.runs.length).2,
      report.observed.renamed.2, report.after]) :
    report.bindings raw state.session.directory.path = some (state.census.inode state.directorySlot.description) ∧
    report.bindings raw (state.session.directory.file .lock) = some (state.census.inode state.owner.description) := by
  rcases List.mem_cons.mp reached with atRuns | later
  · exact report.issueBindings raw (List.mem_cons.mpr (.inl atRuns))
  rcases List.mem_cons.mp later with atRename | atReturn
  · exact report.issueBindings raw (List.mem_cons_of_mem _ (List.mem_singleton.mpr atRename))
  cases List.mem_singleton.mp atReturn
  exact report.afterBindings

theorem current (report : NativeCheckpointDirectoryError (image := image) state cut) :
    cut.current = .manifest .syncDirectory :=
  report.barrier.current

/-- The grouped sync wraps the raw cause. The original phase has become
poisoned, and the reached native image is returned with the same cache
and logical lock owner. -/
theorem returns (report : NativeCheckpointDirectoryError (image := image) state cut)
    (valid : state.Valid) :
    report.run = .error report.error (.poisoned, ⟨(state.cache, report.after), state.files.owners⟩) := by
  let barrier := report.barrier
  have final : barrier.perform cut.checkpoint.prepared cut.checkpoint.manifest
      (.manifest .syncDirectory) barrier.observed.renamed =
      .error report.error (state.cache, report.after) := by
    rw [barrier.routes]
    let cached : FilePath → EStateM IO.Error (CensusDirectoryCache × image) Unit :=
      fun _ (cache, files) => withCache cache (barrier.callbackPrefix.primitives.fsync barrier.handle files)
    change SyncPathGroup.run cached #[state.session.directory.path] report.observed.renamed = _
    rw [SyncPathGroup.run_single cached]
    have started : report.observed.renamed = (state.cache, report.observed.renamed.2) :=
      Prod.ext report.callbackPrefix.beforeFinalDirectory.1 rfl
    rw [started]
    have failed : cached state.session.directory.path (state.cache, report.observed.renamed.2) =
        .error report.cause (state.cache, report.after) := by
      change withCache state.cache (report.callbackPrefix.primitives.fsync
        (report.callbackPrefix.capturedDirectory, state.directorySlot, 0) report.observed.renamed.2) = _
      rw [report.failed]
      rfl
    rw [failed]
    rfl
  obtain ⟨remaining, schedule, tail⟩ := (barrier.issues valid).continuation
  rw [report.completed] at schedule
  have suffix := List.append_cancel_left ((manifestDirectoryPrefix_steps cut.checkpoint.table.runs.length).symm.trans schedule)
  have empty : [] = remaining := (List.cons.inj suffix).2
  rw [← empty] at tail
  have returned : ([Step.manifest .syncDirectory].forM
      (barrier.perform cut.checkpoint.prepared cut.checkpoint.manifest)) barrier.observed.renamed =
      .error report.error (state.cache, report.after) := by
    simp only [List.forM_eq_forM, List.forM_cons, Bind.bind, EStateM.bind, final]
  rw [returned] at tail
  exact tail

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
  obtain ⟨synced, atIssue⟩ := report.barrier.custody valid
  refine ⟨synced, ?_⟩
  intro raw reached
  simp only [List.mem_cons, List.not_mem_nil, or_false] at reached
  rcases reached with atRuns | atRename | rfl
  · exact atIssue raw (List.mem_cons.mpr (.inl atRuns))
  · exact atIssue raw (List.mem_cons_of_mem _ (List.mem_singleton.mpr atRename))
  have census := report.census.trans report.callbackPrefix.beforeFinalDirectory.2
  obtain ⟨root, lock⟩ := report.afterBindings
  exact ⟨census, census.symm ▸ valid.directoryLive, census.symm ▸ valid.ownerLive,
    root.trans (congrArg some report.callbackPrefix.capturedInode.symm), lock⟩

end NativeCheckpointDirectoryError

variable {image : Type} {state : NativeReadyState}
  {cut : CheckpointPowerCut state.session.directory state.writer}

/-- The file projections of the same returned callbacks. The joint
directory view keeps the manifest and WAL marker from one crash choice.
It applies to either an interrupted operation or a reported error.
The final syscall reports whether its durability effect occurred. -/
structure NativeCheckpointFinalBarrier.Physical
    (barrier : NativeCheckpointFinalBarrier (image := image) state cut) (after : image) where
  files : image → FileImage
  runs : image → RunUnlinkImage
  initial : files (barrier.observed.atRun 0).2 = state.files.image
  walFrame : ∀ (done : List Step) step todo prior reached,
    manifestDirectoryPrefix cut.checkpoint.table.runs.length = done ++ step :: todo →
    (done.forM (barrier.callbacks.perform state.session.directory cut.checkpoint.prepared cut.checkpoint.manifest))
      (barrier.observed.atRun 0) = .ok () prior →
    barrier.callbacks.perform state.session.directory cut.checkpoint.prepared cut.checkpoint.manifest step prior =
      .ok () reached →
    CheckpointWalView.ofFiles (files reached.2) = CheckpointWalView.ofFiles (files prior.2)
  runDirectoryFrame : ∀ index < cut.checkpoint.table.runs.length,
    (files (barrier.observed.atRun (index + 1)).2).directory =
      (files (barrier.observed.atRun index).2).directory
  syncRunDirectory : (files barrier.observed.runsSettled.2).directory =
    (files (barrier.observed.atRun cut.checkpoint.table.runs.length).2).directory.syncDirectory
  runPrefix : ReturnedCheckpointRuns barrier.observed (fun pair => runs pair.2)
    (SegmentedCheckpointReport.generation state.writer) cut.checkpoint.plan.files
  priorRuns : SelectedRunsAgree state.writer.wal.directory.active.manifest
    (runs (barrier.observed.atRun 0).2).visible state.writer.published.durable
  priorRunFrame : ∀ index < cut.checkpoint.table.runs.length, ∀ generation,
    generation ≠ SegmentedCheckpointReport.generation state.writer → ∀ prior,
      (runs (barrier.observed.atRun (index + 1)).2).visible generation prior =
        (runs (barrier.observed.atRun index).2).visible generation prior
  stage : (files barrier.observed.runsSettled.2).directory.step .manifest cut.checkpoint.manifest .writeStaged =
    some (files barrier.observed.staged.2).directory
  sync : (files barrier.observed.staged.2).directory.step .manifest cut.checkpoint.manifest .syncStaged =
    some (files barrier.observed.stagedSynced.2).directory
  rename : (files barrier.observed.stagedSynced.2).directory.step .manifest cut.checkpoint.manifest .renameStaged =
    some (files barrier.observed.renamed.2).directory
  directoryEffect : (files after).directory = if cut.tookEffect
    then (files barrier.observed.renamed.2).directory.syncDirectory
    else (files barrier.observed.renamed.2).directory
  runEffect : runs after = if cut.tookEffect then (runs barrier.observed.renamed.2).syncDirectory
    else runs barrier.observed.renamed.2
  walEffect : CheckpointWalView.ofFiles (files after) =
    CheckpointWalView.ofFiles (files barrier.observed.renamed.2)

namespace NativeCheckpointFinalBarrier.Physical

variable {image : Type} {state : NativeReadyState}
  {cut : CheckpointPowerCut state.session.directory state.writer}
  {barrier : NativeCheckpointFinalBarrier (image := image) state cut} {after : image}

theorem wal (physical : barrier.Physical after) :
    CheckpointWalView.ofFiles (physical.files after) = CheckpointWalView.ofFiles state.files.image := by
  have ran := barrier.observed.returns
  have preserved := successfulFrame _ (fun pair => CheckpointWalView.ofFiles (physical.files pair.2)) ran physical.walFrame
  exact physical.walEffect.trans (preserved.trans (congrArg CheckpointWalView.ofFiles physical.initial))

theorem directory (physical : barrier.Physical after) (valid : state.Valid) :
    let old := state.writer.wal.directory.active
    let new := old.replace .manifest cut.checkpoint.manifest
    (physical.files after).directory.active = new ∧
      (physical.files after).directory.crashImages = if cut.tookEffect then [new] else [new, old] := by
  intro old new
  let initial := state.writer.wal.directory
  let staged (synced : Bool) : DirectoryPublication.Image :=
    { initial with staged := fun entry =>
      if entry = .manifest then some (cut.checkpoint.manifest, synced) else initial.staged entry }
  have stage := physical.stage
  have previousDirectory (index : Nat) (within : index ≤ cut.checkpoint.table.runs.length) :
      (physical.files (barrier.observed.atRun index).2).directory = initial := by
    induction index with
    | zero => exact (congrArg FileImage.directory physical.initial).trans valid.retained.directoryFiles
    | succ index earlier =>
      exact (physical.runDirectoryFrame index within).trans (earlier (Nat.le_of_lt within))
  have priorDirectory : (physical.files barrier.observed.runsSettled.2).directory = initial := by
    rw [physical.syncRunDirectory, previousDirectory _ (Nat.le_refl _)]
    change { initial with crashImages := [initial.active] } = initial
    rw [← valid.retained.walDirectorySettled]

  rw [priorDirectory] at stage
  have written : (physical.files barrier.observed.staged.2).directory = staged false :=
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
  have synced : (physical.files barrier.observed.stagedSynced.2).directory = staged true :=
    Option.some.inj (sync.symm.trans syncEffect)
  have renamed := physical.rename
  rw [synced] at renamed
  have visible := congrArg DirectoryPublication.Image.active (Option.some.inj (show some _ = some _ from renamed))
  have choices := congrArg DirectoryPublication.Image.crashImages (Option.some.inj (show some _ = some _ from renamed))
  change new = _ at visible
  change initial.crashImages.map (·.replace .manifest cut.checkpoint.manifest) ++ initial.crashImages = _ at choices
  rw [show initial.crashImages = [old] from valid.retained.walDirectorySettled] at choices
  rw [physical.directoryEffect]
  cases cut.tookEffect with
  | false => exact ⟨visible.symm, choices.symm⟩
  | true => exact ⟨visible.symm, congrArg (fun pair => [pair]) visible.symm⟩

theorem settledRuns (physical : barrier.Physical after) :
    physical.runs after = .settled (physical.runs
      (barrier.observed.atRun cut.checkpoint.table.runs.length).2).visible := by
  have before : physical.runs barrier.observed.renamed.2 =
      (physical.runs (barrier.observed.atRun cut.checkpoint.table.runs.length).2).syncDirectory :=
    physical.runPrefix.renameRuns.trans
      (physical.runPrefix.syncRuns.trans (physical.runPrefix.stageRuns.trans physical.runPrefix.runNames))
  rw [physical.runEffect, before]
  cases cut.tookEffect <;> rfl

/-- The reached file view selects exactly the newly encoded
manifest after an effective barrier, and admits the old and new manifest
before it. Both selections use the exact previously synced run bytes. -/
theorem selects (physical : barrier.Physical after) (valid : state.Valid) :
    ∃ published, CheckpointManifestDirectoryCut cut published (physical.runs after)
      ((physical.files after).directory.project .manifest).crashImages := by
  obtain ⟨published, executed, visible, choices, newRuns, priorRuns⟩ :=
    cut.finalDirectoryPublication valid.retained barrier.completed
  obtain ⟨_, paths⟩ := physical.directory valid
  have survived : ((physical.files after).directory.project .manifest).crashImages =
      published.manifest.crashImages := by
    simp only [DirectoryPublication.Image.project, paths, choices]
    cases cut.tookEffect <;> rfl
  have runPayloads : (physical.runs after).guaranteed =
      (physical.runs (barrier.observed.atRun cut.checkpoint.table.runs.length).2).visible := by
    rw [physical.settledRuns]
    exact congrArg Image.durable (RunUnlinkImage.project_settled _ (.settled none))
  have fresh := visibleSyncedRunPrefix (fun index => (barrier.observed.atRun index).2) _
    physical.runs (SegmentedCheckpointReport.generation state.writer) cut.checkpoint.plan.files
    physical.runPrefix.syncedRun physical.runPrefix.previousRuns
  refine ⟨published, barrier.current, executed, visible, choices, ?_, ?_, ?_, ?_, ?_⟩
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
        (physical.runs (barrier.observed.atRun through).2).visible metadata.header.generation index =
          (physical.runs (barrier.observed.atRun 0).2).visible metadata.header.generation index := by
      induction through with
      | zero => rfl
      | succ through earlier =>
        exact (physical.priorRunFrame through within _ unchanged index).trans (earlier (Nat.le_of_lt within))
    rw [runPayloads, older _ (Nat.le_refl _), physical.priorRuns bytes metadata binding decoded index inside,
      priorRuns _ unchanged _]

/-- A reported joint survivor keeps the WAL marker and explains the
same acknowledged submissions and recorded reads using its own runs. -/
theorem replaysSurvivor (physical : barrier.Physical after) (valid : state.Valid)
    (pending : PendingClientReplay log reads state.writer.history)
    {pair : DirectoryPublication.Bindings} (survived : pair ∈ (physical.files after).directory.crashImages) :
    pair.walBoundary = state.writer.wal.directory.active.walBoundary ∧
      cut.PendingReplay (physical.runs after) pair.manifest log reads := by
  obtain ⟨_, selected⟩ := physical.selects valid
  obtain ⟨_, choices⟩ := physical.directory valid
  have marker : pair.walBoundary = state.writer.wal.directory.active.walBoundary := by
    have joint := survived
    rw [choices] at joint
    split at joint
    · obtain rfl := List.mem_singleton.mp joint
      rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at joint
      rcases joint with rfl | rfl <;> rfl
  have binding : pair.manifest ∈ ((physical.files after).directory.project .manifest).crashImages :=
    List.mem_map_of_mem survived
  exact ⟨marker, selected.replaysPending valid.retained pending binding⟩

end NativeCheckpointFinalBarrier.Physical

namespace NativeCheckpointDirectoryError

variable {image : Type} {state : NativeReadyState}
  {cut : CheckpointPowerCut state.session.directory state.writer}
  {report : NativeCheckpointDirectoryError (image := image) state cut}

abbrev Physical (report : NativeCheckpointDirectoryError (image := image) state cut) :=
  report.barrier.Physical report.after

namespace Physical

theorem wal (physical : report.Physical) :
    CheckpointWalView.ofFiles (physical.files report.after) = CheckpointWalView.ofFiles state.files.image :=
  NativeCheckpointFinalBarrier.Physical.wal physical

theorem directory (physical : report.Physical) (valid : state.Valid) :
    let old := state.writer.wal.directory.active
    let new := old.replace .manifest cut.checkpoint.manifest
    (physical.files report.after).directory.active = new ∧
      (physical.files report.after).directory.crashImages = if cut.tookEffect then [new] else [new, old] :=
  NativeCheckpointFinalBarrier.Physical.directory physical valid

theorem selects (physical : report.Physical) (valid : state.Valid) :
    ∃ published, CheckpointManifestDirectoryCut cut published (physical.runs report.after)
      ((physical.files report.after).directory.project .manifest).crashImages :=
  NativeCheckpointFinalBarrier.Physical.selects physical valid

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
  have custody := (report.custody valid).2 report.after (by simp)
  exact ⟨report.returns valid, custody.1, physical.wal,
    fun _ survived => NativeCheckpointFinalBarrier.Physical.replaysSurvivor physical valid (history.symm ▸ replay) survived⟩

end Alvoki.Storage.DiskSession
