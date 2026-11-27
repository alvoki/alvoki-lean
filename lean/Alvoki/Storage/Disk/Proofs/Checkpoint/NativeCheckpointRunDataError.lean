import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointRunDirectoryError
import Alvoki.Storage.Disk.Proofs.Checkpoint.CheckpointRunDataFailure

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair

/-- A reported error during the guarded run write or its flush. The
actual dispatcher drops the same file handle before returning the data
error. Its local effects and descriptor release are observed together. -/
structure NativeCheckpointRunDataError {image : Type} (state : NativeReadyState)
    (cut : CheckpointPowerCut state.session.directory state.writer) where
  index : Nat
  within : index < cut.checkpoint.table.runs.length
  prior : NativeCheckpointRunObservations (image := image) state cut index
  completed : cut.completed = runSteps index
  run : Compaction.CheckedRun
  selected : cut.checkpoint.table.runs.toArray[index]? = some run
  handle : CheckpointOpenHandle
  guard : AcceptedRunGuard prior.primitives.lookup (state.session.directory.file (.run cut.checkpoint.prepared.generation index))
    (prior.atRun index)
  opened : image
  openReturned : prior.primitives.openRun (state.session.directory.file (.run cut.checkpoint.prepared.generation index))
    (prior.atRun index) = .ok handle opened
  free : ∀ old ∈ (prior.descriptors (prior.atRun index)).slots, old.address ≠ handle.2.1.address
  fresh : (prior.descriptors (prior.atRun index)).references handle.2.1.description = []
  allocated : handle.1 = (prior.descriptors (prior.atRun index)).insert handle.2.1 free
  afterOpen : prior.descriptors opened = handle.1
  links : RunOpenLinkCensus
    (path := state.session.directory.file (.run cut.checkpoint.prepared.generation index))
    (before := prior.atRun index) prior.primitives.lookup (prior.views index).visible (handle.1.inode handle.2.1.description)
  openView : RunDirectoryInodeView state.session.directory (prior.inodes opened) (prior.runs opened)
  openedPath : openView.visible (state.session.directory.file (.run cut.checkpoint.prepared.generation index)) =
    some (handle.1.inode handle.2.1.description)
  emptyAtOpen : (prior.inodes opened).visible (handle.1.inode handle.2.1.description) = ByteArray.empty
  cause : IO.Error
  stopped : image
  failed : RunDataWriteFailure prior.primitives.write prior.primitives.flush handle run.run.bytes opened cause stopped
  beforeDrop : prior.descriptors stopped = handle.1
  after : image
  dropped : dataErrorDropState prior.primitives.drop handle stopped = after
  afterClose : prior.descriptors after = handle.1.afterDrops [handle.2.1.closeEvent]
  view : RunDirectoryInodeView state.session.directory (prior.inodes after) (prior.runs after)
  sameNames : view.visible = openView.visible
  directoryBound : view.visible state.session.directory.path = some (state.census.inode state.directorySlot.description)
  lockBound : view.visible (state.session.directory.file .lock) = some (state.census.inode state.owner.description)
  frame : RunWriteInodeFrame (state.session.directory.file (.run cut.checkpoint.prepared.generation index))
    (handle.1.inode handle.2.1.description) (prior.inodes after) (prior.views index) view
  walAndPair : prior.files after = prior.files (prior.atRun index)

namespace NativeCheckpointRunDataError

variable {image : Type} {state : NativeReadyState} {cut : CheckpointPowerCut state.session.directory state.writer}

abbrev path (report : NativeCheckpointRunDataError (image := image) state cut) : FilePath :=
  state.session.directory.file (.run cut.checkpoint.prepared.generation report.index)

def atIssue (report : NativeCheckpointRunDataError (image := image) state cut) : CensusDirectoryCache × image :=
  (state.cache, report.prior.atRun report.index)

theorem current (report : NativeCheckpointRunDataError (image := image) state cut) : cut.current = .writeRun report.index := by
  obtain ⟨_, paired⟩ := steps_atRunPair report.within
  have ordered := cut.schedule
  rw [report.completed, paired] at ordered
  simp only [List.append_assoc, List.cons_append, List.nil_append] at ordered
  exact (List.cons.inj (List.append_cancel_left ordered)).1.symm

/-- All earlier run pairs have returned before the actual preflight
dispatches this run write. -/
theorem issues (report : NativeCheckpointRunDataError (image := image) state cut) (valid : state.Valid) :
    CheckpointIssue report.prior.perform state.session.phase report.prior.entry cut.checkpoint.prepared cut.checkpoint.manifest
      cut.completed (.writeRun report.index) report.atIssue := by
  have scheduled := cut.schedule
  rw [report.current] at scheduled
  have completed := report.prior.runPrefix
  rw [← report.completed] at completed
  rw [valid.phase]
  exact cut.preflight.reachesIssue report.prior.perform report.prior.entry scheduled completed

/-- The current run write uses the selected run bytes and the exact opened
handle. Its original error skips the cache insertion and file sync. -/
theorem callbackFails (report : NativeCheckpointRunDataError (image := image) state cut) :
    report.prior.perform cut.checkpoint.prepared cut.checkpoint.manifest (.writeRun report.index) report.atIssue =
      .error report.cause (state.cache, report.after) := by
  have raw : report.prior.primitives.cached.writeRun report.path report.run.run.bytes (report.prior.atRun report.index) =
      .error report.cause report.after := by
    have failed := report.failed.returns report.guard report.openReturned report.prior.primitives.drop
    simpa only [CheckpointPrimitiveCalls.cached, dropHandleOnDataError, runDataDropImage, report.dropped] using failed
  have selected : cut.checkpoint.prepared.table.runs.toArray[report.index]? = some report.run := report.selected
  simp only [NativeCheckpointRunObservations.perform, CheckpointCacheCalls.perform, CheckpointFileCallbacks.perform,
    performCheckpointFileStep, selected, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, CheckpointCacheCalls.callbacks]
  exact stageFreshWithCache_error _ _ _ _ raw

theorem returns (report : NativeCheckpointRunDataError (image := image) state cut) (valid : state.Valid) :
    runCheckpointWithEffects report.prior.perform (state.session.phase, report.prior.entry) =
      .error report.cause (.poisoned, ⟨(state.cache, report.after), state.files.owners⟩) := by
  obtain ⟨_, _, continued⟩ := (report.issues valid).continuation
  rw [continued, List.forM_eq_forM, List.forM_cons]
  simp only [Bind.bind, EStateM.bind, report.callbackFails, NativeCheckpointRunObservations.entry]

/-- The returning finalizer has closed exactly the failed run's temporary
slot. The cached directory and held lock still point to their old objects. -/
theorem custody (report : NativeCheckpointRunDataError (image := image) state cut) (valid : state.Valid) :
    report.handle.2.1 ∈ (report.prior.descriptors report.stopped).slots ∧
    report.prior.descriptors report.after = state.census ∧
    (report.prior.descriptors report.after).references report.handle.2.1.description = [] ∧
    state.directorySlot ∈ (report.prior.descriptors report.after).slots ∧
    state.owner ∈ (report.prior.descriptors report.after).slots ∧
    report.view.visible state.session.directory.path = some (report.prior.captured.inode state.directorySlot.description) ∧
    report.view.visible (state.session.directory.file .lock) = some (state.census.inode state.owner.description) := by
  have before := report.prior.prefixCensus report.index (Nat.le_refl _)
  have census : report.prior.descriptors report.after = report.prior.descriptors (report.prior.atRun report.index) := by
    rw [report.afterClose, report.allocated, checkpointTemporaryClose]
  have restored := census.trans before
  refine ⟨?_, restored, census.symm ▸ report.fresh, restored.symm ▸ valid.directoryLive,
    restored.symm ▸ valid.ownerLive, ?_, report.lockBound⟩
  · rw [report.beforeDrop, report.allocated]
    exact List.mem_cons_self
  · rw [report.prior.capturedInode]
    exact report.directoryBound

/-- The freshly opened name retains its inode through the data error
and finalization. Its visible payload comes from the reached inode. -/
theorem scratchAtReturn (report : NativeCheckpointRunDataError (image := image) state cut) :
    let inode := report.handle.1.inode report.handle.2.1.description
    report.openView.visible report.path = some inode ∧
    (report.prior.inodes report.opened).visible inode = ByteArray.empty ∧
    report.view.visible report.path = some inode ∧
    (report.prior.runs report.after).visible cut.checkpoint.prepared.generation report.index =
      some ((report.prior.inodes report.after).visible inode) := by
  have bound : report.view.visible report.path = some (report.handle.1.inode report.handle.2.1.description) := by
    rw [report.sameNames]
    exact report.openedPath
  exact ⟨report.openedPath, report.emptyAtOpen, bound, report.view.visibleProjects _ _ _ bound⟩

theorem stableAfter (report : NativeCheckpointRunDataError (image := image) state cut) {path : FilePath}
    {inode : Nat} {bytes : ByteArray} (different : path ≠ report.path)
    (stable : (report.prior.views report.index).Stable path inode bytes) : report.view.Stable path inode bytes :=
  report.frame.keepsStableOnSyncError (effective := false) rfl (report.links.privateBinding report.guard) different stable

theorem priorRunBytes (report : NativeCheckpointRunDataError (image := image) state cut) (valid : state.Valid)
    {bytes payload : ByteArray} {metadata : Manifest.IntegrityCheckpoint} {index : Nat}
    (binding : state.writer.wal.directory.active.manifest = some bytes)
    (decoded : Manifest.IntegrityCheckpoint.decode bytes = .ok metadata) (within : index < metadata.header.runCount.toNat)
    (stored : state.writer.published.durable metadata.header.generation index = some payload) :
    ∃ inode, (report.prior.views 0).Stable (state.session.directory.file (.run metadata.header.generation index)) inode payload ∧
      report.view.Stable (state.session.directory.file (.run metadata.header.generation index)) inode payload :=
  report.prior.priorRunAfter valid report.stableAfter binding decoded within stored

theorem filesAtReturn (report : NativeCheckpointRunDataError (image := image) state cut) :
    report.prior.files report.after = state.files.image :=
  report.walAndPair.trans (report.prior.filesAtRun report.index (Nat.le_refl _))

theorem manifestAtReturn (report : NativeCheckpointRunDataError (image := image) state cut) :
    match (report.prior.files report.after).directory.active.manifest with
    | none => report.view.visible (state.session.directory.file .manifest) = none
    | some bytes => ∃ inode, (report.prior.views 0).Stable (state.session.directory.file .manifest) inode bytes ∧
        report.view.Stable (state.session.directory.file .manifest) inode bytes := by
  rw [report.filesAtReturn]
  exact report.prior.manifestAfter report.frame.visibleNames report.stableAfter

theorem selectedCheckpoint (report : NativeCheckpointRunDataError (image := image) state cut) (valid : state.Valid) :
    SelectedIntegrityCheckpoint (report.prior.runs report.after).guaranteed
      (report.prior.files report.after).directory.active.manifest state.writer.checkpoint :=
  report.prior.selectedAfter valid report.stableAfter report.filesAtReturn

end NativeCheckpointRunDataError

/-- A failed run write or flush ends the native checkpoint with a poisoned
session while retaining the same old checkpoint and earlier read replay. -/
structure NativeReturnedCheckpointRunDataError {image : Type} (current : NativeReadPosition history log)
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    (report : NativeCheckpointRunDataError (image := image) current.state cut) : Prop where
  issued : CheckpointIssue report.prior.perform current.state.session.phase report.prior.entry cut.checkpoint.prepared
    cut.checkpoint.manifest cut.completed (.writeRun report.index) report.atIssue
  returned : runCheckpointWithEffects report.prior.perform (current.state.session.phase, report.prior.entry) =
    .error report.cause (.poisoned, ⟨(current.state.cache, report.after), current.state.files.owners⟩)
  held : current.state.files.owners.Owns current.state.session.directory current.state.session.descriptor
  openedCensus : report.prior.descriptors report.opened = report.handle.1
  slotBeforeDrop : report.handle.2.1 ∈ (report.prior.descriptors report.stopped).slots
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

theorem NativeReadPosition.checkpointRunDataError {image : Type} (current : NativeReadPosition history log)
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    (report : NativeCheckpointRunDataError (image := image) current.state cut) :
    NativeReturnedCheckpointRunDataError current report := by
  obtain ⟨valid, _, replay⟩ := current.readPrefix.refines
  obtain ⟨slot, census, closed, directoryLive, lockLive, directory, lock⟩ := report.custody valid
  exact ⟨report.issues valid, report.returns valid, valid.retained.held, report.afterOpen,
    slot, census, closed, directoryLive, lockLive, directory, lock, report.filesAtReturn,
    report.selectedCheckpoint valid, replay, current.readPrefix.readsBounded⟩

end Alvoki.Storage.DiskSession
