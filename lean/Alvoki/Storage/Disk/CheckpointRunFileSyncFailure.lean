import Alvoki.Storage.Disk.CheckpointRunDirectoryCut
import Alvoki.Storage.Disk.SegmentedFailureRelease

namespace Alvoki.Storage.CheckpointPublication

open System DiskSession SyncHandleRouting
open WAL.Boundary (WalInodeImage)

/-- The run's write frame also holds when file sync returns before its
effect. A completed file effect only changes the target inode. -/
theorem RunWriteInodeFrame.keepsStableOnSyncError {directory : DiskDirectory} {before after flushed : WalInodeImage}
    {oldRuns newRuns : RunUnlinkImage} {path held : FilePath} {inode oldInode : Nat}
    {bytes : ByteArray} {entry : RunDirectoryInodeView directory before oldRuns}
    {reached : RunDirectoryInodeView directory after newRuns}
    (effect : RunWriteInodeFrame path inode flushed entry reached)
    {effective : Bool} (synced : after = if effective then flushed.completeFileSync inode else flushed)
    (privateBinding : ∀ other, entry.visible other = some inode → other = path)
    (different : held ≠ path) (stable : entry.Stable held oldInode bytes) :
    reached.Stable held oldInode bytes := by
  cases effective with
  | true => exact effect.keepsStable synced privateBinding different stable
  | false =>
    have distinct : oldInode ≠ inode := by
      intro same
      exact different (privateBinding held (same ▸ stable.visibleBinding))
    refine ⟨(effect.visibleNames held different).trans stable.visibleBinding, ?_, ?_, ?_⟩
    · intro bindings survives
      obtain ⟨prior, possible, preserved⟩ := effect.crashNames bindings survives
      exact (preserved held different).trans (stable.crashBinding prior possible)
    · rw [synced]
      exact (effect.visibleBytes oldInode distinct).trans stable.visibleBytes
    · rw [synced]
      exact (effect.crashBytes oldInode distinct).trans stable.crashBytes

/-- The exact earlier run pairs precede the selected pair. -/
theorem steps_atRunPair {count index : Nat} (within : index < count) :
    ∃ later, steps count = runSteps index ++ [.writeRun index, .syncRun index] ++ later := by
  let tail := count - (index + 1)
  have length : index + 1 + tail = count := by dsimp [tail]; omega
  have split : List.range count = List.range (index + 1) ++ List.range' (index + 1) tail := by
    have range := List.range'_append (s := 0) (m := index + 1) (n := tail) (step := 1)
    simpa only [List.range_eq_range', Nat.one_mul, Nat.zero_add, length] using range.symm
  have order : List.range count = List.range index ++ [index] ++ List.range' (index + 1) tail := by
    rw [split, List.range_succ]
  refine ⟨(List.range' (index + 1) tail).flatMap (fun pos => [.writeRun pos, .syncRun pos]) ++
    [.syncRunsDirectory] ++ Publication.steps.map Step.manifest, ?_⟩
  simp [steps, runSteps, order, List.append_assoc]

end Alvoki.Storage.CheckpointPublication

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting
open WAL.Boundary (WalInodeImage)

private abbrev Handle := DescriptorInventory × DescriptorSlot
private abbrev State := Cache Handle × WalInodeImage
private abbrev Write := FilePath → ByteArray → EStateM IO.Error State Unit
private abbrev Rename := FilePath → FilePath → EStateM IO.Error State Unit

private def dispatch {directory : DiskDirectory} {before : SegmentedWriterState}
    (attempt : SegmentedCheckpointReport directory before) (writeRun writeStage : Write) (rename : Rename)
    (openRead : FilePath → EStateM IO.Error WalInodeImage Handle)
    (fsync : Handle → EStateM IO.Error WalInodeImage Unit) : Step → EStateM IO.Error State Unit :=
  performCheckpointFileStep directory (SegmentedCheckpointReport.generation before)
    attempt.table.runs.toArray (directory.file .stagedManifest) attempt.manifest
    (fun found => match found with
      | some run => pure run
      | none => throw (IO.userError "checkpoint run index is out of bounds"))
    writeRun writeStage (SyncPathGroup.run (sync directory.path openRead fsync)) rename

/-- The exact successful run pairs preceding a selected run callback. -/
structure ObservedCheckpointRunPrefix {directory : DiskDirectory} {before : SegmentedWriterState}
    (attempt : SegmentedCheckpointReport directory before) where
  flushedTable : (flushForCheckpoint before.installed.table id : Except String PackedTable) = .ok attempt.table
  generationFits : before.installed.generation.toNat + 1 < UInt64.size
  runCountFits : attempt.table.runs.length < UInt64.size
  encoded : encodeCheckpointIntegrityManifest attempt.table (SegmentedCheckpointReport.generation before) = .ok attempt.manifest
  writeRun : Write
  writeStage : Write
  rename : Rename
  openRead : FilePath → EStateM IO.Error WalInodeImage Handle
  fsync : Handle → EStateM IO.Error WalInodeImage Unit
  index : Nat
  within : index < attempt.table.runs.length
  run : Compaction.CheckedRun
  selected : attempt.table.runs.toArray[index]? = some run
  atRun : Nat → State
  runs : State → RunUnlinkImage
  view : ∀ i, RunDirectoryInodeView directory (atRun i).2 (runs (atRun i))
  prefixPairs : ∀ i < index, Nonempty (CheckpointRunPairCustody directory (SegmentedCheckpointReport.generation before)
    attempt.table (dispatch attempt writeRun writeStage rename openRead fsync) (atRun i) (atRun (i + 1))
    (view i) (view (i + 1)) i)
/-- This reported run completed the guarded open, write and flush. Its
own file sync returns an error after the preceding private run pairs.
The write projection and off-target frame concern the same callback,
opened description and reached namespace. -/
structure ObservedCheckpointRunSyncFailure {directory : DiskDirectory} {before : SegmentedWriterState}
    (attempt : SegmentedCheckpointReport directory before) extends ObservedCheckpointRunPrefix attempt where
  inventory : DescriptorInventory
  slot : DescriptorSlot
  flushed : WalInodeImage
  writes : RunWriteReports (directory.file (.run (SegmentedCheckpointReport.generation before) index))
    run.run.bytes (atRun index).2 flushed (inventory, slot)
  projected :
    let path := directory.file (.run (SegmentedCheckpointReport.generation before) index)
    writeRun path run.run.bytes (atRun index) =
      stageFreshWithCache path run.run.bytes
        (fun name bytes => writeCheckpointRunWith writes.lookup writes.openWrite writes.write writes.flush name bytes pure)
        (atRun index)
  links : RunOpenLinkReports writes (view index).visible (inventory.inode slot.description)
  drops : List LockReferenceDrop
  issues : slot.reference ∈ (inventory.afterDrops drops).references slot.description
  effective : Bool
  cause : IO.Error
  failed : fsync (inventory, slot) flushed =
    .error cause (if effective then flushed.completeFileSync (inventory.inode slot.description) else flushed)
  bytes : flushed.visible (inventory.inode slot.description) = run.run.bytes
  flushedBindings : FilePath → Option Nat
  bound : flushedBindings (directory.file (.run (SegmentedCheckpointReport.generation before) index)) =
    some (inventory.inode slot.description)
  reachedView : RunDirectoryInodeView directory
    (if effective then flushed.completeFileSync (inventory.inode slot.description) else flushed)
    (runs ((atRun index).1.consume (directory.file (.run (SegmentedCheckpointReport.generation before) index)),
      if effective then flushed.completeFileSync (inventory.inode slot.description) else flushed))
  sameNames : reachedView.visible = flushedBindings
  frame : RunWriteInodeFrame (directory.file (.run (SegmentedCheckpointReport.generation before) index))
    (inventory.inode slot.description) flushed (view index) reachedView

namespace ObservedCheckpointRunPrefix

variable {directory : DiskDirectory} {before : SegmentedWriterState}
  {attempt : SegmentedCheckpointReport directory before}

abbrev path (report : ObservedCheckpointRunPrefix attempt) : FilePath :=
  directory.file (.run (SegmentedCheckpointReport.generation before) report.index)

abbrev perform (report : ObservedCheckpointRunPrefix attempt) : Step → EStateM IO.Error State Unit :=
  dispatch attempt report.writeRun report.writeStage report.rename report.openRead report.fsync

/-- A returned error at the selected pair stops the real ordered schedule
after the previously completed pairs. -/
theorem returnsError (report : ObservedCheckpointRunPrefix attempt) {cause : IO.Error} {reached : State}
    (failed : ((report.perform (.writeRun report.index) >>= fun _ => report.perform (.syncRun report.index))
      (report.atRun report.index)) = .error cause reached) :
    CheckpointPublication.run attempt.table.runs.length report.perform (report.atRun 0) = .error cause reached := by
  obtain ⟨remaining, schedule⟩ := steps_atRunPair report.within
  have past := runSteps_returned report.perform report.index report.atRun (fun i earlier =>
    let ⟨pair⟩ := report.prefixPairs i earlier
    pair.returned)
  change ((steps attempt.table.runs.length).forM report.perform) (report.atRun 0) = _
  rw [schedule, List.append_assoc, List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM]
  simp only [Bind.bind, EStateM.bind, past]
  have suffix : ([Step.writeRun report.index, Step.syncRun report.index] ++ remaining).forM report.perform =
      ((report.perform (.writeRun report.index) >>= fun _ => report.perform (.syncRun report.index)) >>=
        fun _ => remaining.forM report.perform) := by
    simp [List.forM_eq_forM, List.forM_cons, List.cons_append, bind_assoc]
  rw [suffix]
  simp only [Bind.bind, EStateM.bind] at failed ⊢
  rw [failed]

/-- The selected pair returns the exact poisoned writer. A successful
close or final drop makes the reached files available for another open. -/
theorem poisonsAndReleases (report : ObservedCheckpointRunPrefix attempt) {writer : Nat} {cause : IO.Error} {reached : State}
    (failed : CheckpointPublication.run attempt.table.runs.length report.perform (report.atRun 0) = .error cause reached)
    (ownership : before.owners.Owns directory writer) (release : SegmentedFailureRelease writer) :
    let poisoned : Phase Installed × LockedFileState State := (.poisoned, ⟨reached, before.owners⟩)
    let released : LockedFileState State := ⟨reached, before.owners.set (directory.file .lock) none⟩
    runPreparedCheckpoint attempt.prepared report.perform (.ready before.installed, ⟨report.atRun 0, before.owners⟩) =
        .error cause poisoned ∧
      release.Observed (directory := directory) poisoned released ∧
      TryLockObserves released.owners directory (.ok true) := by
  have publication : CheckpointPublication.run attempt.prepared.table.runs.length report.perform (report.atRun 0) =
      .error cause reached := failed
  obtain ⟨poisoned, closed, drops, vacant⟩ := runPreparedCheckpoint_failure_handoff
    (before := ⟨report.atRun 0, before.owners⟩) before.installed attempt.prepared report.perform publication ownership
  refine ⟨poisoned, ?_, vacant⟩
  cases release with
  | closed => exact closed
  | references held events last => exact drops held events last

/-- The earlier completed run pairs preserve the inodes and payloads
selected by the old manifest. The returned path separation also applies
to the selected next run. -/
theorem priorStable (report : ObservedCheckpointRunPrefix attempt) {writer : Nat}
    (ready : before.RetainedReady directory writer)
    (entry : CheckpointRunPrefix.EntrySelection before (report.view 0))
    {raw : ByteArray} {metadata : Manifest.IntegrityCheckpoint}
    (binding : before.wal.directory.active.manifest = some raw)
    (decoded : Manifest.IntegrityCheckpoint.decode raw = .ok metadata)
    {index : Nat} (within : index < metadata.header.runCount.toNat) :
    let path := directory.file (.run metadata.header.generation index)
    ∃ payload inode, before.published.durable metadata.header.generation index = some payload ∧
      (report.view report.index).Stable path inode payload ∧ path ≠ report.path := by
  intro path
  have prior := ready.resumed.selected
  rw [← ready.walPair] at prior
  obtain ⟨payload, stored⟩ := prior.runExists binding decoded within
  obtain ⟨inode, captured⟩ := entry raw metadata binding decoded index within payload stored
  have liveManifest : before.published.manifest.active = some raw := by
    rw [ready.manifestFiles, ready.directoryFiles]
    exact binding
  have distinctGeneration := CheckpointPowerCut.freshGeneration ready report.generationFits raw (.inl liveManifest)
    (.integrity metadata) (Manifest.VersionedCheckpoint.decode_integrity decoded)
  have separated (i : Nat) : path ≠ directory.file (.run (SegmentedCheckpointReport.generation before) i) :=
    runPath_ne directory (fun same => distinctGeneration (congrArg Prod.fst same))
  have stable (through : Nat) (limited : through ≤ report.index) :
      (report.view through).Stable path inode payload := by
    induction through with
    | zero => exact captured
    | succ previous ih =>
      obtain ⟨pair⟩ := report.prefixPairs previous limited
      exact pair.frame.keepsStable pair.synced pair.privateBinding (separated previous)
        (ih (Nat.le_trans (Nat.le_succ _) limited))
  exact ⟨payload, inode, stored, stable report.index (Nat.le_refl _), separated report.index⟩

end ObservedCheckpointRunPrefix

namespace ObservedCheckpointRunSyncFailure

variable {directory : DiskDirectory} {before : SegmentedWriterState}
  {attempt : SegmentedCheckpointReport directory before}

abbrev path (report : ObservedCheckpointRunSyncFailure attempt) : FilePath :=
  directory.file (.run (SegmentedCheckpointReport.generation before) report.index)

def reached (report : ObservedCheckpointRunSyncFailure attempt) : State :=
  ((report.atRun report.index).1.consume report.path,
    if report.effective then report.flushed.completeFileSync (report.inventory.inode report.slot.description) else report.flushed)

def error (report : ObservedCheckpointRunSyncFailure attempt) : IO.Error :=
  IO.userError s!"sync failed for '{report.path}': {report.cause}"

abbrev perform (report : ObservedCheckpointRunSyncFailure attempt) : Step → EStateM IO.Error State Unit :=
  dispatch attempt report.writeRun report.writeStage report.rename report.openRead report.fsync

/-- The failed file barrier uses the live issuing description, and
the same cached run pair reports the wrapped error and reached image. -/
theorem failedPair (report : ObservedCheckpointRunSyncFailure attempt) :
    (∃ sync : FsyncObservation (fun (handle : Handle) => handle.2.description)
        (fun handle => handle.1.inode handle.2.description) (report.inventory, report.slot) report.flushed
        (fun inode image => image.completeFileSync inode) (report.fsync (report.inventory, report.slot) report.flushed),
      sync.issuer = report.slot.reference ∧ sync.effective = report.effective ∧
      report.flushedBindings report.path = some sync.effectInode ∧
      report.reachedView.visible report.path = some sync.effectInode) ∧
    ((report.perform (.writeRun report.index) >>= fun _ => report.perform (.syncRun report.index))
      (report.atRun report.index)) = .error report.error report.reached := by
  let captured := (report.inventory, report.slot)
  let persist := fun inode (image : WalInodeImage) => image.completeFileSync inode
  have effect : FsyncResult report.flushed (persist (report.inventory.inode report.slot.description) report.flushed)
      report.effective (report.fsync captured report.flushed) := by
    rw [show report.fsync captured report.flushed = _ from report.failed]
    cases report.effective <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> constructor
  let observation := FsyncObservation.ofInventory report.inventory report.drops
    (fun handle : Handle => handle.2.description) (fun handle => handle.1.inode handle.2.description)
    captured report.slot.reference report.issues rfl report.flushed persist effect
  refine ⟨⟨observation, rfl, rfl, report.bound, report.sameNames ▸ report.bound⟩, ?_⟩
  have staged : report.writeRun report.path report.run.run.bytes (report.atRun report.index) =
      .ok () ((report.atRun report.index).1.remember report.path captured, report.flushed) := by
    rw [report.projected]
    have written := report.writes.captures
    change writeCheckpointRunWith report.writes.lookup report.writes.openWrite report.writes.write report.writes.flush
      report.path report.run.run.bytes pure (report.atRun report.index).2 = .ok captured report.flushed at written
    simp only [stageFreshWithCache, written]
  have routed := performCheckpointRunPair_route directory (SegmentedCheckpointReport.generation before) attempt.table
    attempt.manifest report.selected (report.atRun report.index).1 captured report.writeRun report.writeStage report.rename
    report.openRead report.fsync staged
  rw [show report.fsync captured report.flushed = _ from report.failed] at routed
  exact routed

/-- The actual checkpoint worker returns at this run's own file barrier. -/
theorem returns (report : ObservedCheckpointRunSyncFailure attempt) :
    CheckpointPublication.run attempt.table.runs.length report.perform (report.atRun 0) = .error report.error report.reached :=
  report.toObservedCheckpointRunPrefix.returnsError report.failedPair.2

/-- Return the exact poisoned writer and its observed release. -/
theorem poisonsAndReleases (report : ObservedCheckpointRunSyncFailure attempt) {writer : Nat}
    (ownership : before.owners.Owns directory writer) (release : SegmentedFailureRelease writer) :
    let poisoned : Phase Installed × LockedFileState State := (.poisoned, ⟨report.reached, before.owners⟩)
    let released : LockedFileState State := ⟨report.reached, before.owners.set (directory.file .lock) none⟩
    runPreparedCheckpoint attempt.prepared report.perform (.ready before.installed, ⟨report.atRun 0, before.owners⟩) =
        .error report.error poisoned ∧
      release.Observed (directory := directory) poisoned released ∧
      TryLockObserves released.owners directory (.ok true) :=
  report.toObservedCheckpointRunPrefix.poisonsAndReleases report.returns ownership release

/-- The checked new-generation path and its complete link census exclude
every previously selected run inode. The successful prefix and the failed
pair retain those names and bytes on either reported file-sync timing. -/
theorem priorRuns (report : ObservedCheckpointRunSyncFailure attempt) {writer : Nat}
    (ready : before.RetainedReady directory writer)
    (entry : CheckpointRunPrefix.EntrySelection before (report.view 0)) :
    SelectedRunsAgree before.wal.directory.active.manifest (report.runs report.reached).guaranteed before.published.durable := by
  intro raw metadata binding decoded index within
  obtain ⟨_, _, stored, stable, separated⟩ :=
    report.toObservedCheckpointRunPrefix.priorStable ready entry binding decoded within
  have retained := report.frame.keepsStableOnSyncError (effective := report.effective) rfl report.links.privateBinding
    separated stable
  exact retained.guaranteed.trans stored.symm

end ObservedCheckpointRunSyncFailure

end Alvoki.Storage.DiskSession
