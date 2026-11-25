import Alvoki.Storage.Disk.CheckpointObservedCompletion
import Alvoki.Storage.Disk.CheckpointRunPrefixCustody

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting
open WAL.Boundary (WalInodeImage)

/-- Selection and namespace effects at the first run-directory barrier.
The reached map contains the freshly synced file contents, even when its
new bindings have yet to become durable. -/
structure CheckpointRunBarrierCut {directory : DiskDirectory} {before : SegmentedWriterState}
    (cut : CheckpointPowerCut directory before) (published : Image)
    (reached interrupted : RunUnlinkImage) : Prop where
  current : cut.current = .syncRunsDirectory
  executed : before.published.executeVersioned cut.checkpoint.plan cut.checkpoint.cut = some published
  manifestChoices : published.manifest.crashImages = [before.wal.directory.active.manifest]
  olderRuns : ∀ older, older ≠ SegmentedCheckpointReport.generation before → ∀ index,
    published.durable older index = before.published.durable older index
  namespaceCut : interrupted = if cut.tookEffect then reached.syncDirectory else reached
  priorBindings : SelectedRunsAgree before.wal.directory.active.manifest reached.guaranteed before.published.durable

/-- The retained writer's selected manifest names its installed generation,
which differs from the next checkpoint generation. -/
theorem CheckpointPowerCut.priorSelectedGeneration {directory : DiskDirectory} {before : SegmentedWriterState}
    {writer : Nat} (cut : CheckpointPowerCut directory before) (ready : before.RetainedReady directory writer)
    {bytes : ByteArray} {metadata : Manifest.IntegrityCheckpoint}
    (visible : before.wal.directory.active.manifest = some bytes)
    (decoded : Manifest.IntegrityCheckpoint.decode bytes = .ok metadata) :
    metadata.header.generation = before.installed.generation ∧
      metadata.header.generation ≠ SegmentedCheckpointReport.generation before := by
  have parsed := CheckpointPowerCut.selectedGeneration ready.resumed.selected
  rw [← ready.resumed.generation, ← ready.walPair, visible, Option.mapM, decoded] at parsed
  have previous : metadata.header.generation = before.installed.generation := Except.ok.inj parsed
  refine ⟨previous, ?_⟩
  rw [previous]
  intro same
  have values := congrArg UInt64.toNat same
  unfold SegmentedCheckpointReport.generation at values
  rw [UInt64.toNat_ofNat_of_lt' cut.generationFits] at values
  omega

/-- All run-file barriers can complete before power is lost at the first
directory barrier. The ordered native prefix reaches that exact callback
with the directory handle in the reached cache. An observed effective cut settles the
new run names. The old manifest remains selected on either outcome. -/
theorem CheckpointPowerCut.atRunDirectory {directory : DiskDirectory} {before : SegmentedWriterState}
    {writer : Nat} {handle : Type}
    (cut : CheckpointPowerCut directory before) (ready : before.RetainedReady directory writer)
    (completedRuns : cut.completed = runSteps cut.checkpoint.table.runs.length)
    (writeRun writeStage : FilePath → ByteArray → EStateM IO.Error (Cache handle × WalInodeImage) Unit)
    (openRead : FilePath → EStateM IO.Error WalInodeImage handle)
    (fsync : handle → EStateM IO.Error WalInodeImage Unit)
    (rename : FilePath → FilePath → EStateM IO.Error (Cache handle × WalInodeImage) Unit)
    (atRun : Nat → Cache handle × WalInodeImage) (interrupted : Cache handle × WalInodeImage)
    (runs : Cache handle × WalInodeImage → RunUnlinkImage)
    (manifest : Cache handle × WalInodeImage → Publication.Image)
    (views : ∀ index, RunDirectoryInodeView directory (atRun index).2 (runs (atRun index)))
    (directoryHandle : handle) :
    let count := cut.checkpoint.table.runs.length
    let generation := SegmentedCheckpointReport.generation before
    let perform := performCheckpointFileStep directory generation cut.checkpoint.table.runs.toArray
      (directory.file .stagedManifest) cut.checkpoint.manifest
      (fun found => match found with
        | some run => pure run
        | none => throw (IO.userError "checkpoint run index is out of bounds"))
      writeRun writeStage (SyncPathGroup.run (sync directory.path openRead fsync)) rename
    (∀ index < count,
      Nonempty (CheckpointRunPairCustody directory generation cut.checkpoint.table perform
        (atRun index) (atRun (index + 1)) (views index) (views (index + 1)) index)) →
    (∀ bytes metadata, before.wal.directory.active.manifest = some bytes →
      Manifest.IntegrityCheckpoint.decode bytes = .ok metadata →
      ∀ index < metadata.header.runCount.toNat, ∀ payload,
        before.published.durable metadata.header.generation index = some payload →
        ∃ inode, (views 0).Stable (directory.file (.run metadata.header.generation index)) inode payload) →
    (atRun count).1.directory = some directoryHandle →
    runs interrupted = (if cut.tookEffect then (runs (atRun count)).syncDirectory else runs (atRun count)) →
    manifest (atRun 0) = before.published.manifest →
    (∀ index < count, manifest (atRun (index + 1)) = manifest (atRun index)) →
    manifest interrupted = manifest (atRun count) →
    cut.current = .syncRunsDirectory ∧
    (cut.completed.forM perform) (atRun 0) = .ok () (atRun count) ∧
    perform cut.current (atRun count) =
      SyncPathGroup.run (m := EStateM IO.Error (Cache handle × WalInodeImage))
        (fun _ (cache, image) => withCache cache (fsync directoryHandle image))
        #[directory.path] (atRun count) ∧
    ∃ published, CheckpointRunBarrierCut cut published (runs (atRun count)) (runs interrupted) ∧
      manifest interrupted = published.manifest ∧
      (cut.tookEffect = false → published = before.published) ∧
      (∀ index < count, (runs (atRun count)).visible generation index = cut.checkpoint.plan.files[index]?) ∧
      (cut.tookEffect = true →
        ∀ index < count, (runs interrupted).guaranteed generation index = published.durable generation index) := by
  intro count generation perform writes entry captured namespaceCut
    initialManifest frameManifest cutManifest
  have current : cut.current = .syncRunsDirectory := by
    have suffix : .syncRunsDirectory :: Publication.steps.map Step.manifest = cut.current :: cut.remaining := by
      apply List.append_cancel_left (as := runSteps count)
      have schedule := cut.schedule
      rw [completedRuns] at schedule
      simpa only [steps, List.append_assoc, List.cons_append, List.nil_append] using schedule
    exact (List.cons.inj suffix).1.symm
  have exactCount := cut.reachedCount.1
  rw [completedRuns] at exactCount
  have prefixRan := runSteps_returned perform count atRun (fun index within =>
    let ⟨pair⟩ := writes index within
    pair.returned)
  have freshRuns (through : Nat) (bounded : through ≤ count) : ∀ index < through,
      ∃ (run : Compaction.CheckedRun) (inode : Nat), cut.checkpoint.table.runs.toArray[index]? = some run ∧
        (views through).visible (directory.file (.run generation index)) = some inode ∧
        (atRun through).2.visible inode = run.run.bytes := by
    induction through with
    | zero => simp
    | succ through ih =>
      intro index within
      obtain ⟨pair⟩ := writes through bounded
      by_cases same : index = through
      · subst index
        exact ⟨pair.run, pair.inode, pair.selected, pair.bound,
          pair.synced.symm ▸ pair.bytes⟩
      · obtain ⟨run, inode, selected, bound, bytes⟩ := ih (Nat.le_trans (Nat.le_succ _) bounded) index (by omega)
        have different : directory.file (.run generation index) ≠ directory.file (.run generation through) :=
          runPath_ne directory (fun paths => same (congrArg Prod.snd paths))
        have framed := pair.frame.keepsVisible pair.synced pair.privateBinding different bound bytes
        exact ⟨run, inode, selected, framed.2⟩
  have visible : ∀ index < count, (runs (atRun count)).visible generation index = cut.checkpoint.plan.files[index]? := by
    intro index within
    obtain ⟨run, inode, selected, bound, bytes⟩ := freshRuns count (Nat.le_refl _) index within
    rw [(views count).visibleProjects generation index inode bound, bytes]
    change some run.run.bytes = (cut.checkpoint.table.runs.map (·.run.bytes))[index]?
    rw [List.getElem?_map, ← List.getElem?_toArray, selected]
    rfl
  have oldSelected := ready.resumed.selected
  rw [← ready.walPair] at oldSelected
  have priorBindings : SelectedRunsAgree before.wal.directory.active.manifest
      (runs (atRun count)).guaranteed before.published.durable := by
    intro bytes metadata binding decoded index within
    have differentGeneration := (cut.priorSelectedGeneration ready binding decoded).2
    obtain ⟨payload, stored⟩ := oldSelected.runExists binding decoded within
    obtain ⟨inode, reported⟩ := entry bytes metadata binding decoded index within payload stored
    let path := directory.file (.run metadata.header.generation index)
    have retained (through : Nat) (bounded : through ≤ count) : (views through).Stable path inode payload := by
      induction through with
      | zero => exact reported
      | succ through ih =>
        obtain ⟨pair⟩ := writes through bounded
        have distinct : path ≠ directory.file (.run generation through) :=
          runPath_ne directory (fun same => differentGeneration (congrArg Prod.fst same))
        exact pair.frame.keepsStable pair.synced pair.privateBinding distinct
          (ih (Nat.le_trans (Nat.le_succ _) bounded))
    exact ((retained count (Nat.le_refl _)).guaranteed).trans stored.symm
  have allManifests (through : Nat) (within : through ≤ count) :
      manifest (atRun through) = before.published.manifest := by
    induction through with
    | zero => exact initialManifest
    | succ through ih =>
      rw [frameManifest through within]
      exact ih (Nat.le_trans (Nat.le_succ _) within)
  obtain ⟨published, executed, sameManifest, beforeEffect, afterEffect, oldRuns⟩ :=
    before.published.executeVersioned_atRunDirectory cut.checkpoint.plan cut.tookEffect
  have planCount : cut.checkpoint.plan.files.length = count := by
    simp [SegmentedCheckpointReport.plan, VersionedRunSet.integrity, count]
  rw [planCount, ← exactCount] at executed
  have settled : before.published.manifest.crashImages = [before.wal.directory.active.manifest] := by
    rw [ready.manifestFiles, ready.directoryFiles]
    have directorySettled := ready.walDirectorySettled
    simp [DirectoryPublication.Image.project, DirectoryPublication.Bindings.get, directorySettled]
  have selected : published.manifest.crashImages = [before.wal.directory.active.manifest] := by
    rw [sameManifest]
    exact settled
  refine ⟨current, completedRuns.symm ▸ prefixRan, ?_, published,
    ⟨current, executed, selected, oldRuns, namespaceCut, priorBindings⟩,
    cutManifest.trans ((allManifests count (Nat.le_refl _)).trans sameManifest.symm),
    beforeEffect, visible, ?_⟩
  · rw [current]
    let cached (_ : FilePath) : EStateM IO.Error (Cache handle × WalInodeImage) Unit :=
      fun (cache, image) => withCache cache (fsync directoryHandle image)
    change SyncPathGroup.run (sync directory.path openRead fsync) #[directory.path] (atRun count) =
      SyncPathGroup.run cached #[directory.path] (atRun count)
    have selected : sync directory.path openRead fsync directory.path (atRun count) =
        cached directory.path (atRun count) := by
      simp [sync, Cache.resolve, captured, cached]
    rw [SyncPathGroup.run_single (sync directory.path openRead fsync), SyncPathGroup.run_single cached, selected]
  · intro effective index within
    simp only [namespaceCut, effective, ↓reduceIte]
    have runBytes := congrArg Image.durable
      (RunUnlinkImage.project_settled (runs (atRun count)).visible (.settled none))
    exact (congrFun (congrFun runBytes generation) index).trans
      ((visible index within).trans (afterEffect effective index).symm)

end Alvoki.Storage.DiskSession
