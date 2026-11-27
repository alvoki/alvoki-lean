import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointRunFileIssue

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair

/-- The run file sync returns an ordinary error. Its local finalizer
closes the same temporary description before the caller sees the error. -/
structure NativeCheckpointRunFileError {image : Type} (state : NativeReadyState)
    (cut : CheckpointPowerCut state.session.directory state.writer)
    extends NativeCheckpointRunFileEffect (image := image) state cut where
  cause : IO.Error
  failed : prior.primitives.fsync handle flushed = .error cause after
  afterClose : prior.descriptors after = handle.1.afterDrops [handle.2.1.closeEvent]

namespace NativeCheckpointRunFileError

variable {image : Type} {state : NativeReadyState} {cut : CheckpointPowerCut state.session.directory state.writer}

abbrev path (report : NativeCheckpointRunFileError (image := image) state cut) : FilePath :=
  report.toNativeCheckpointRunFileEffect.path

def error (report : NativeCheckpointRunFileError (image := image) state cut) : IO.Error :=
  IO.userError s!"sync failed for '{report.path}': {report.cause}"

def atIssue (report : NativeCheckpointRunFileError (image := image) state cut) : CensusDirectoryCache × image :=
  report.toNativeCheckpointRunFileEffect.toNativeCheckpointRunFileIssue.atIssue

theorem current (report : NativeCheckpointRunFileError (image := image) state cut) : cut.current = .syncRun report.index :=
  report.toNativeCheckpointRunFileEffect.toNativeCheckpointRunFileIssue.current

theorem reachedWrite (report : NativeCheckpointRunFileError (image := image) state cut) :
    report.prior.perform cut.checkpoint.prepared cut.checkpoint.manifest (.writeRun report.index)
      (state.cache, report.prior.atRun report.index) = .ok () report.atIssue :=
  report.toNativeCheckpointRunFileEffect.toNativeCheckpointRunFileIssue.reachedWrite

/-- The actual preflight reaches the issued file sync on the exact pending
handle installed by this run's write and flush. -/
theorem issues (report : NativeCheckpointRunFileError (image := image) state cut) (valid : state.Valid) :
    CheckpointIssue report.prior.perform state.session.phase report.prior.entry cut.checkpoint.prepared cut.checkpoint.manifest
      cut.completed (.syncRun report.index) report.atIssue :=
  report.toNativeCheckpointRunFileEffect.toNativeCheckpointRunFileIssue.issues valid

theorem callbackFails (report : NativeCheckpointRunFileError (image := image) state cut) :
    report.prior.perform cut.checkpoint.prepared cut.checkpoint.manifest (.syncRun report.index) report.atIssue =
      .error report.error (state.cache, report.after) := by
  let directory := state.session.directory.path
  let openRead := report.prior.primitives.openRead
  let fsync := report.prior.primitives.fsync
  change SyncPathGroup.run (sync directory openRead fsync) #[report.path]
    (state.cache.remember report.path report.handle, report.flushed) = _
  have separate : report.path ≠ directory := file_ne_directory _ _
  have consumed : state.cache.consume report.path = state.cache := by
    have empty := report.prior.pending
    cases known : state.cache with
    | mk directory active pending => simp_all [Cache.consume]
  rw [SyncPathGroup.run_single, syncRemembered separate report.handle openRead fsync report.flushed]
  simp only [fsync, report.failed, consumed]
  rfl

theorem returns (report : NativeCheckpointRunFileError (image := image) state cut) (valid : state.Valid) :
    runCheckpointWithEffects report.prior.perform (state.session.phase, report.prior.entry) =
      .error report.error (.poisoned, ⟨(state.cache, report.after), state.files.owners⟩) := by
  obtain ⟨_, _, continued⟩ := (report.issues valid).continuation
  rw [continued, List.forM_eq_forM, List.forM_cons]
  simp only [Bind.bind, EStateM.bind, report.callbackFails, NativeCheckpointRunObservations.entry]

/-- This handle is live at the issued fsync, and its observed release
restores the prior census without dropping either held database slot. -/
theorem custody (report : NativeCheckpointRunFileError (image := image) state cut) (valid : state.Valid) :
    report.handle.2.1 ∈ (report.prior.descriptors report.flushed).slots ∧
    report.prior.descriptors report.after = state.census ∧
    (report.prior.descriptors report.after).references report.handle.2.1.description = [] ∧
    state.directorySlot ∈ (report.prior.descriptors report.after).slots ∧
    state.owner ∈ (report.prior.descriptors report.after).slots ∧
    report.view.visible state.session.directory.path = some (report.prior.captured.inode state.directorySlot.description) ∧
    report.view.visible (state.session.directory.file .lock) = some (state.census.inode state.owner.description) := by
  have prior := report.prior.prefixCensus report.index (Nat.le_refl _)
  have census : report.prior.descriptors report.after = report.prior.descriptors (report.prior.atRun report.index) := by
    rw [report.afterClose, report.allocated, checkpointTemporaryClose]
  have restored := census.trans prior
  refine ⟨?_, restored, census.symm ▸ report.fresh,
    restored.symm ▸ valid.directoryLive, restored.symm ▸ valid.ownerLive, ?_, ?_⟩
  · rw [report.atFileSync, report.allocated]
    exact List.mem_cons_self
  · rw [report.sameNames, report.directoryAtIssue, report.prior.capturedInode]
  · rw [report.sameNames]
    exact report.lockAtIssue

/-- The run bytes are already visible, but their inode acquires the
new durable bytes only when the reported file sync takes effect. No
claim about durable publication of its new directory name is needed. -/
theorem runBytes (report : NativeCheckpointRunFileError (image := image) state cut) :
    let inode := report.handle.1.inode report.handle.2.1.description
    report.view.visible report.path = some inode ∧
    (report.prior.runs report.after).visible cut.checkpoint.prepared.generation report.index = some report.run.run.bytes ∧
    (report.prior.inodes report.after).crashBytes inode = (if cut.tookEffect then [report.run.run.bytes]
      else (report.prior.inodes report.flushed).crashBytes inode) :=
  report.toNativeCheckpointRunFileEffect.runBytes

theorem stableAfter (report : NativeCheckpointRunFileError (image := image) state cut) {path : FilePath}
    {inode : Nat} {bytes : ByteArray} (different : path ≠ report.path)
    (stable : (report.prior.views report.index).Stable path inode bytes) : report.view.Stable path inode bytes :=
  report.toNativeCheckpointRunFileEffect.stableAfter different stable

theorem priorRunBytes (report : NativeCheckpointRunFileError (image := image) state cut) (valid : state.Valid)
    {bytes payload : ByteArray} {metadata : Manifest.IntegrityCheckpoint} {index : Nat}
    (binding : state.writer.wal.directory.active.manifest = some bytes)
    (decoded : Manifest.IntegrityCheckpoint.decode bytes = .ok metadata) (within : index < metadata.header.runCount.toNat)
    (stored : state.writer.published.durable metadata.header.generation index = some payload) :
    ∃ inode, (report.prior.views 0).Stable (state.session.directory.file (.run metadata.header.generation index)) inode payload ∧
      report.view.Stable (state.session.directory.file (.run metadata.header.generation index)) inode payload :=
  report.toNativeCheckpointRunFileEffect.priorRunBytes valid binding decoded within stored

theorem filesAtReturn (report : NativeCheckpointRunFileError (image := image) state cut) :
    report.prior.files report.after = state.files.image :=
  report.toNativeCheckpointRunFileEffect.filesAtEffect

theorem manifestAtReturn (report : NativeCheckpointRunFileError (image := image) state cut) :
    match (report.prior.files report.after).directory.active.manifest with
    | none => report.view.visible (state.session.directory.file .manifest) = none
    | some bytes => ∃ inode, (report.prior.views 0).Stable (state.session.directory.file .manifest) inode bytes ∧
        report.view.Stable (state.session.directory.file .manifest) inode bytes :=
  report.toNativeCheckpointRunFileEffect.manifestAtEffect

theorem selectedCheckpoint (report : NativeCheckpointRunFileError (image := image) state cut) (valid : state.Valid) :
    SelectedIntegrityCheckpoint (report.prior.runs report.after).guaranteed
      (report.prior.files report.after).directory.active.manifest state.writer.checkpoint :=
  report.toNativeCheckpointRunFileEffect.selectedCheckpoint valid

end NativeCheckpointRunFileError
/-- A returned checkpoint run sync error reaches the poisoned phase
before any directory or manifest step, keeping the selected checkpoint
and the entire existing read replay. -/
structure NativeReturnedCheckpointRunFileError {image : Type} (current : NativeReadPosition history log)
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    (report : NativeCheckpointRunFileError (image := image) current.state cut) : Prop where
  issued : CheckpointIssue report.prior.perform current.state.session.phase report.prior.entry cut.checkpoint.prepared
    cut.checkpoint.manifest cut.completed (.syncRun report.index) report.atIssue
  returned : runCheckpointWithEffects report.prior.perform (current.state.session.phase, report.prior.entry) =
    .error report.error (.poisoned, ⟨(current.state.cache, report.after), current.state.files.owners⟩)
  held : current.state.files.owners.Owns current.state.session.directory current.state.session.descriptor
  openedCensus : report.prior.descriptors report.opened = report.handle.1
  syncCensus : report.prior.descriptors report.flushed = report.handle.1
  issuingSlot : report.handle.2.1 ∈ (report.prior.descriptors report.flushed).slots
  census : report.prior.descriptors report.after = current.state.census
  closed : (report.prior.descriptors report.after).references report.handle.2.1.description = []
  directoryLive : current.state.directorySlot ∈ (report.prior.descriptors report.after).slots
  lockLive : current.state.owner ∈ (report.prior.descriptors report.after).slots
  directoryObject : report.view.visible current.state.session.directory.path =
    some (report.prior.captured.inode current.state.directorySlot.description)
  lockObject : report.view.visible (current.state.session.directory.file .lock) =
    some (current.state.census.inode current.state.owner.description)
  files : report.prior.files report.after = current.state.files.image
  checkpoint : SelectedIntegrityCheckpoint (report.prior.runs report.after).guaranteed
    (report.prior.files report.after).directory.active.manifest current.state.writer.checkpoint
  replay : PendingClientReplay log current.reads history
  bounded : ∀ read ∈ current.reads, read.BoundedBy history.length

theorem NativeReadPosition.checkpointRunFileError {image : Type} (current : NativeReadPosition history log)
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    (report : NativeCheckpointRunFileError (image := image) current.state cut) :
    NativeReturnedCheckpointRunFileError current report := by
  obtain ⟨valid, _, replay⟩ := current.readPrefix.refines
  obtain ⟨slot, census, closed, directoryLive, lockLive, directory, lock⟩ := report.custody valid
  exact ⟨report.issues valid, report.returns valid, valid.retained.held, report.afterOpen, report.atFileSync,
    slot, census, closed, directoryLive,
    lockLive, directory, lock, report.filesAtReturn, report.selectedCheckpoint valid, replay, current.readPrefix.readsBounded⟩

end Alvoki.Storage.DiskSession
