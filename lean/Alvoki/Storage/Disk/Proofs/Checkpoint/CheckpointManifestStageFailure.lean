import Alvoki.Storage.Disk.Proofs.Checkpoint.CheckpointRunPrefixReports
import Alvoki.Storage.Disk.Proofs.Recovery.SegmentedCheckpointStep
import Alvoki.Storage.Disk.SegmentedFailureRelease
import Alvoki.Storage.Disk.Proofs.Filesystem.StagedHandleCustody
import Alvoki.Storage.Disk.Proofs.WAL.ReplacedWalDescriptor
import Alvoki.Storage.Disk.Proofs.Filesystem.DescriptorInventory

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting
open WAL.Boundary (WalInodeImage)

private abbrev Handle := DescriptorInventory × DescriptorSlot
private abbrev State := Cache Handle × WalInodeImage
private abbrev Stage := FilePath → ByteArray → EStateM IO.Error WalInodeImage Handle
private abbrev Fsync := Handle → EStateM IO.Error WalInodeImage Unit

/-- The returned error comes from the fresh stage write or from syncing
the exact description that the successful write kept pending. A failed
write may leave partial scratch. A failed sync can still be effective. -/
inductive ManifestStageFailure (stage : Stage) (fsync : Fsync) (path livePath : FilePath) (bytes : ByteArray)
    (bindings : WalInodeImage → FilePath → Option Nat) (initial : State) : IO.Error → State → Prop where
  | write (failed : stage path bytes initial.2 = .error cause reached) :
      ManifestStageFailure stage fsync path livePath bytes bindings initial cause (initial.1, reached)
  | sync (handle : Handle) (written : WalInodeImage) (effective : Bool)
      (opened : stage path bytes initial.2 = .ok handle written)
      (live : handle.2 ∈ handle.1.slots)
      (bound : bindings written path = some (handle.1.inode handle.2.description))
      (distinct : bindings written livePath ≠ some (handle.1.inode handle.2.description))
      (contents : written.visible (handle.1.inode handle.2.description) = bytes)
      (failed : fsync handle written =
        .error cause (if effective then written.completeFileSync (handle.1.inode handle.2.description) else written)) :
      ManifestStageFailure stage fsync path livePath bytes bindings initial (IO.userError s!"sync failed for '{path}': {cause}")
        (initial.1.consume path, if effective then written.completeFileSync (handle.1.inode handle.2.description) else written)

private theorem stagedManifest_ne_directory (directory : DiskDirectory) :
    directory.file .stagedManifest ≠ directory.path := by
  intro same
  have length := congrArg (fun path : FilePath => path.toString.length) same
  change (directory.path.toString ++ "/" ++ "MANIFEST.next").length = directory.path.toString.length at length
  simp only [String.length_append] at length
  have slash : "/".length = 1 := rfl
  omega

/-- Reached native callbacks through a returned failure before rename.
The same cache supplies the first directory sync and then the reached
manifest callbacks. The proof supplies the full writer schedule result. -/
structure ObservedManifestStageFailure {directory : DiskDirectory} {before : SegmentedWriterState}
    (attempt : SegmentedCheckpointReport directory before) where
  flushed : (flushForCheckpoint before.installed.table id : Except String PackedTable) = .ok attempt.table
  generationFits : before.installed.generation.toNat + 1 < UInt64.size
  runCountFits : attempt.table.runs.length < UInt64.size
  encoded : encodeCheckpointIntegrityManifest attempt.table (SegmentedCheckpointReport.generation before) = .ok attempt.manifest
  writeRun : FilePath → ByteArray → EStateM IO.Error State Unit
  stage : Stage
  openRead : FilePath → EStateM IO.Error WalInodeImage Handle
  fsync : Fsync
  rename : FilePath → FilePath → EStateM IO.Error State Unit
  bindings : WalInodeImage → FilePath → Option Nat
  atRun : Nat → State
  directoryHandle : Handle
  directorySettled : WalInodeImage
  cause : IO.Error
  reached : State
  pairs : ∀ index < attempt.table.runs.length,
    let perform := performCheckpointFileStep directory (SegmentedCheckpointReport.generation before)
      attempt.table.runs.toArray (directory.file .stagedManifest) attempt.manifest
      (fun found => match found with
        | some run => pure run
        | none => throw (IO.userError "checkpoint run index is out of bounds"))
      writeRun (fun path bytes => stageFreshWithCache path bytes stage)
      (SyncPathGroup.run (sync directory.path openRead fsync)) rename
    (perform (.writeRun index) >>= fun _ => perform (.syncRun index)) (atRun index) = .ok () (atRun (index + 1))
  captured : (atRun attempt.table.runs.length).1.directory = some directoryHandle
  synced : fsync directoryHandle (atRun attempt.table.runs.length).2 = .ok () directorySettled
  stageFailed : ManifestStageFailure stage fsync (directory.file .stagedManifest) (directory.file .manifest)
    attempt.manifest bindings ((atRun attempt.table.runs.length).1, directorySettled) cause reached

namespace ObservedManifestStageFailure

variable {directory : DiskDirectory} {before : SegmentedWriterState}
  {attempt : SegmentedCheckpointReport directory before}

noncomputable def callbacks (report : ObservedManifestStageFailure attempt) : CheckpointFileCallbacks State :=
  ⟨report.writeRun, fun path bytes => stageFreshWithCache path bytes report.stage,
    SyncPathGroup.run (sync directory.path report.openRead report.fsync), report.rename⟩

noncomputable def perform (report : ObservedManifestStageFailure attempt) : Step → EStateM IO.Error State Unit :=
  report.callbacks.perform directory attempt.prepared attempt.manifest

/-- The ordered run pairs and retained directory sync reach the stage
write. Once a manifest callback fails, neither rename nor final
directory sync is reached. -/
theorem returns (report : ObservedManifestStageFailure attempt) :
    run attempt.table.runs.length report.perform (report.atRun 0) = .error report.cause report.reached := by
  let count := attempt.table.runs.length
  let initial : State := ((report.atRun count).1, report.directorySettled)
  let path := directory.file .stagedManifest
  have pairs := runSteps_returned report.perform count report.atRun report.pairs
  have directorySync : report.perform .syncRunsDirectory (report.atRun count) = .ok () initial := by
    change SyncPathGroup.run (sync directory.path report.openRead report.fsync)
      #[directory.path] (report.atRun count) = _
    have routed : sync directory.path report.openRead report.fsync directory.path (report.atRun count) =
        withCache (report.atRun count).1 (report.fsync report.directoryHandle (report.atRun count).2) := by
      simp [sync, Cache.resolve, count, report.captured]
    rw [SyncPathGroup.run_single (sync directory.path report.openRead report.fsync), routed, report.synced]
    rfl
  have failed := report.stageFailed
  change ManifestStageFailure report.stage report.fsync path (directory.file .manifest)
    attempt.manifest report.bindings initial report.cause report.reached at failed
  have manifestSteps : ((Publication.steps.map Step.manifest).forM report.perform) initial =
      .error report.cause report.reached := by
    generalize report.cause = cause at failed ⊢
    generalize report.reached = reached at failed ⊢
    cases failed with
    | write failed =>
      have writes : report.perform (.manifest .writeStaged) initial =
          .error _ (initial.1, _) := stageFreshWithCache_error initial.1 path attempt.manifest report.stage failed
      simp only [Publication.steps, List.map_cons, List.map_nil, List.forM_eq_forM, List.forM_cons, Bind.bind,
        EStateM.bind, writes]
    | @sync rawCause handle written effective opened live bound distinct contents failed =>
      have writes : report.perform (.manifest .writeStaged) initial =
          .ok () (initial.1.remember path handle, written) := by
        change stageFreshWithCache path attempt.manifest report.stage initial = _
        simp only [stageFreshWithCache, opened]
      have synced : report.perform (.manifest .syncStaged) (initial.1.remember path handle, written) =
          .error (IO.userError s!"sync failed for '{path}': {rawCause}")
            (initial.1.consume path, if effective then written.completeFileSync (handle.1.inode handle.2.description) else written) := by
        change SyncPathGroup.run (sync directory.path report.openRead report.fsync) #[path]
          (initial.1.remember path handle, written) = _
        have separate : path ≠ directory.path := stagedManifest_ne_directory directory
        rw [SyncPathGroup.run_single, syncRemembered separate handle report.openRead report.fsync written, failed]
        rfl
      simp only [Publication.steps, List.map_cons, List.map_nil, List.forM_eq_forM, List.forM_cons, Bind.bind,
        EStateM.bind, writes, synced]
  simp only [run, steps, List.forM_eq_forM, List.forM_append]
  change EStateM.bind (EStateM.bind ((runSteps count).forM report.perform)
    (fun _ => [Step.syncRunsDirectory].forM report.perform))
    (fun _ => (Publication.steps.map Step.manifest).forM report.perform) (report.atRun 0) = _
  simp only [EStateM.bind, pairs, List.forM_eq_forM, List.forM_cons, List.forM_nil, Bind.bind, directorySync,
    Pure.pure, EStateM.pure]
  exact manifestSteps

/-- A returned stage failure poisons the still-held writer at the
reported physical image. Explicit successful close or the observed last
drop releases the same lock and leaves exactly that image available. -/
theorem poisonsAndReleases (report : ObservedManifestStageFailure attempt)
    {writer : Nat} (ownership : before.owners.Owns directory writer)
    (releases : SegmentedFailureRelease writer) :
    let poisoned : Phase Installed × LockedFileState State := (.poisoned, ⟨report.reached, before.owners⟩)
    let released : LockedFileState State := ⟨report.reached, before.owners.set (directory.file .lock) none⟩
    runPreparedCheckpoint attempt.prepared report.perform (.ready before.installed, ⟨report.atRun 0, before.owners⟩) =
        .error report.cause poisoned ∧
      releases.Observed (directory := directory) poisoned released ∧
      TryLockObserves released.owners directory (.ok true) := by
  have publication : run attempt.prepared.table.runs.length report.perform (report.atRun 0) =
      .error report.cause report.reached := report.returns
  obtain ⟨poisoned, closed, drops, vacant⟩ := runPreparedCheckpoint_failure_handoff
    (before := ⟨report.atRun 0, before.owners⟩) before.installed attempt.prepared report.perform publication ownership
  refine ⟨poisoned, ?_, vacant⟩
  cases releases with
  | closed => exact closed
  | references held events last => exact drops held events last

end ObservedManifestStageFailure

end Alvoki.Storage.DiskSession
