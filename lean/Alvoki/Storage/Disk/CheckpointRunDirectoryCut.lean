import Alvoki.Storage.Disk.CheckpointObservedCompletion

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
    (bindings : WalInodeImage → FilePath → Option Nat) (directoryHandle : handle) :
    let count := cut.checkpoint.table.runs.length
    let generation := SegmentedCheckpointReport.generation before
    let perform := performCheckpointFileStep directory generation cut.checkpoint.table.runs.toArray
      (directory.file .stagedManifest) cut.checkpoint.manifest
      (fun found => match found with
        | some run => pure run
        | none => throw (IO.userError "checkpoint run index is out of bounds"))
      writeRun writeStage (SyncPathGroup.run (sync directory.path openRead fsync)) rename
    (∀ index < count, (perform (.writeRun index) >>= fun _ => perform (.syncRun index)) (atRun index) =
      .ok () (atRun (index + 1))) →
    (∀ index < count, let reached := atRun (index + 1)
      (runs reached).visible generation index =
        knownSyncedRunBytes directory (bindings reached.2) reached.2 generation index) →
    (∀ index < count,
      ∃ (run : Compaction.CheckedRun) (cache : Cache handle) (flushed : WalInodeImage) (inode : Nat),
        let pathname := directory.file (.run generation index)
        cut.checkpoint.table.runs.toArray[index]? = some run ∧
        (perform (.writeRun index) >>= fun _ => perform (.syncRun index)) (atRun index) =
          .ok () (cache, flushed.completeFileSync inode) ∧
        bindings flushed pathname = some inode ∧
        bindings (flushed.completeFileSync inode) pathname = bindings flushed pathname ∧
        flushed.visible inode = run.run.bytes) →
    (∀ index < count, ∀ prior < index,
      (runs (atRun (index + 1))).visible generation prior = (runs (atRun index)).visible generation prior) →
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
  intro count generation perform pairs projects writes preserves captured namespaceCut
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
  have prefixRan := runSteps_returned perform count atRun pairs
  have known := syncedRunsFromInodes directory generation cut.checkpoint.table atRun pairs runs bindings projects writes
  have visible := visibleSyncedRunPrefix atRun count runs generation
    cut.checkpoint.plan.files known preserves
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
  refine ⟨current, completedRuns.symm ▸ prefixRan, ?_, published, ⟨current, executed, selected, oldRuns, namespaceCut⟩,
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
