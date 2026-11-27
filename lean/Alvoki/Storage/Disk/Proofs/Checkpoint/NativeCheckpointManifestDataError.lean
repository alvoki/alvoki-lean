import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointManifestSyncError
import Alvoki.Storage.Disk.Proofs.Checkpoint.CheckpointRunDataFailure

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair

namespace CheckpointPrimitiveCalls

private theorem stageDataError {handle image : Type} (calls : CheckpointPrimitiveCalls handle image)
    {path : FilePath} {bytes : ByteArray} {before opened stopped : image} {descriptor : handle} {cause : IO.Error}
    (opening : calls.StageOpened path before descriptor opened)
    (failed : RunDataWriteFailure calls.write calls.flush descriptor bytes opened cause stopped) :
    calls.cached.writeStaged path bytes before = .error cause (dataErrorDropState calls.drop descriptor stopped) := by
  have data : (do
      withDataErrorDrop calls.drop descriptor (calls.write descriptor bytes)
      withDataErrorDrop calls.drop descriptor (calls.flush descriptor)
      pure descriptor) opened = .error cause (dataErrorDropState calls.drop descriptor stopped) := by
    cases failed with
    | writeError failed => simp only [Bind.bind, EStateM.bind, withDataErrorDrop, failed]
    | flushError written failed => simp only [Bind.bind, EStateM.bind, withDataErrorDrop, written, failed]
  cases opening with
  | first opened =>
    simpa only [cached, writeFreshStagedWith, withFreshStaging, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, opened]
      using data
  | afterStale conflict cleaned opened =>
    simpa only [cached, writeFreshStagedWith, withFreshStaging, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
      conflict, cleaned, opened] using data

end CheckpointPrimitiveCalls

/-- The guarded exclusive stage opening succeeds after the run barriers.
The real write or flush uses that handle and returns its error after
local finalization. The reached file and slot effects are observed. -/
structure NativeCheckpointManifestDataError {image : Type} (state : NativeReadyState)
    (cut : CheckpointPowerCut state.session.directory state.writer) where
  settled : NativeCheckpointRunsSynced (image := image) state cut
  completed : cut.completed = runSteps cut.checkpoint.table.runs.length ++ [.syncRunsDirectory]
  handle : CheckpointOpenHandle
  opened : image
  opening : settled.runs.primitives.StageOpened (state.session.directory.file .stagedManifest) settled.after handle opened
  free : ∀ old ∈ (settled.runs.descriptors settled.after).slots, old.address ≠ handle.2.1.address
  fresh : (settled.runs.descriptors settled.after).references handle.2.1.description = []
  allocated : handle.1 = (settled.runs.descriptors settled.after).insert handle.2.1 free
  atOpen : settled.runs.descriptors opened = handle.1
  openView : RunDirectoryInodeView state.session.directory (settled.runs.inodes opened) (settled.runs.runs opened)
  openedPath : openView.visible (state.session.directory.file .stagedManifest) = some (handle.1.inode handle.2.1.description)
  emptyAtOpen : (settled.runs.inodes opened).visible (handle.1.inode handle.2.1.description) = ByteArray.empty
  cause : IO.Error
  beforeDrop : image
  failed : RunDataWriteFailure settled.runs.primitives.write settled.runs.primitives.flush handle cut.checkpoint.manifest
    opened cause beforeDrop
  atDrop : settled.runs.descriptors beforeDrop = handle.1
  after : image
  dropped : dataErrorDropState settled.runs.primitives.drop handle beforeDrop = after
  afterClose : settled.runs.descriptors after = handle.1.afterDrops [handle.2.1.closeEvent]
  view : RunDirectoryInodeView state.session.directory (settled.runs.inodes after) (settled.runs.runs after)
  sameNames : view.visible = openView.visible
  privateInode : ∀ other, settled.view.visible other = some (handle.1.inode handle.2.1.description) →
    other = state.session.directory.file .stagedManifest
  frame : RunWriteInodeFrame (state.session.directory.file .stagedManifest)
    (handle.1.inode handle.2.1.description) (settled.runs.inodes after) settled.view view
  bytesWritten : Nat
  bounded : bytesWritten ≤ cut.checkpoint.manifest.size
  scratchBytes : (settled.runs.inodes after).visible (handle.1.inode handle.2.1.description) =
    cut.checkpoint.manifest.extract 0 bytesWritten
  scratch : (settled.runs.files after).directory.staged .manifest =
    some ((settled.runs.inodes after).visible (handle.1.inode handle.2.1.description), false)
  pair : (settled.runs.files after).directory.active = (settled.runs.files settled.after).directory.active
  crashPair : (settled.runs.files after).directory.crashImages = (settled.runs.files settled.after).directory.crashImages
  wal : CheckpointWalView.ofFiles (settled.runs.files after) = CheckpointWalView.ofFiles (settled.runs.files settled.after)

namespace NativeCheckpointManifestDataError

variable {image : Type} {state : NativeReadyState} {cut : CheckpointPowerCut state.session.directory state.writer}

def atIssue (report : NativeCheckpointManifestDataError (image := image) state cut) : CensusDirectoryCache × image :=
  (state.cache, report.settled.after)

theorem current (report : NativeCheckpointManifestDataError (image := image) state cut) :
    cut.current = .manifest .writeStaged := by
  have ordered := cut.schedule
  rw [report.completed] at ordered
  simp only [CheckpointPublication.steps, Publication.steps, List.map_cons, List.map_nil, List.append_assoc,
    List.cons_append, List.nil_append] at ordered
  exact (List.cons.inj (List.cons.inj (List.append_cancel_left ordered)).2).1.symm

theorem issues (report : NativeCheckpointManifestDataError (image := image) state cut) (valid : state.Valid) :
    CheckpointIssue report.settled.runs.perform state.session.phase report.settled.runs.entry cut.checkpoint.prepared
      cut.checkpoint.manifest cut.completed (.manifest .writeStaged) report.atIssue := by
  have scheduled := cut.schedule
  rw [report.current] at scheduled
  have completed := report.settled.runPrefix
  rw [← report.completed] at completed
  rw [valid.phase]
  exact cut.preflight.reachesIssue report.settled.runs.perform report.settled.runs.entry scheduled completed

/-- The original error returns after the actual local drop, without
adding a pending handle for the failed staging operation. -/
theorem callbackFails (report : NativeCheckpointManifestDataError (image := image) state cut) :
    report.settled.runs.perform cut.checkpoint.prepared cut.checkpoint.manifest (.manifest .writeStaged) report.atIssue =
      .error report.cause (state.cache, report.after) := by
  have failed := report.settled.runs.primitives.stageDataError report.opening report.failed
  rw [report.dropped] at failed
  exact stageFreshWithCache_error _ _ _ _ failed

theorem returns (report : NativeCheckpointManifestDataError (image := image) state cut) (valid : state.Valid) :
    runCheckpointWithEffects report.settled.runs.perform (state.session.phase, report.settled.runs.entry) =
      .error report.cause (.poisoned, ⟨(state.cache, report.after), state.files.owners⟩) := by
  obtain ⟨_, _, continued⟩ := (report.issues valid).continuation
  rw [continued, List.forM_eq_forM, List.forM_cons]
  simp only [Bind.bind, EStateM.bind, report.callbackFails, NativeCheckpointRunObservations.entry]

theorem releasesStage (report : NativeCheckpointManifestDataError (image := image) state cut) :
    report.handle.2.1 ∈ (report.settled.runs.descriptors report.beforeDrop).slots ∧
    report.settled.runs.descriptors report.after = state.census ∧
    (report.settled.runs.descriptors report.after).references report.handle.2.1.description = [] := by
  have restored : report.settled.runs.descriptors report.after = report.settled.runs.descriptors report.settled.after := by
    rw [report.afterClose, report.allocated, checkpointTemporaryClose]
  refine ⟨?_, restored.trans report.settled.keepsCensus, restored.symm ▸ report.fresh⟩
  rw [report.atDrop, report.allocated]
  exact List.mem_cons_self

theorem scratchAtReturn (report : NativeCheckpointManifestDataError (image := image) state cut) :
    let inode := report.handle.1.inode report.handle.2.1.description
    report.openView.visible (state.session.directory.file .stagedManifest) = some inode ∧
    (report.settled.runs.inodes report.opened).visible inode = ByteArray.empty ∧
    report.view.visible (state.session.directory.file .stagedManifest) = some inode ∧
    (report.settled.runs.inodes report.after).visible inode = cut.checkpoint.manifest.extract 0 report.bytesWritten ∧
    (report.settled.runs.files report.after).directory.staged .manifest =
      some (cut.checkpoint.manifest.extract 0 report.bytesWritten, false) ∧ report.bytesWritten ≤ cut.checkpoint.manifest.size := by
  exact ⟨report.openedPath, report.emptyAtOpen, report.sameNames.symm ▸ report.openedPath, report.scratchBytes,
    report.scratch.trans (congrArg (fun bytes => some (bytes, false)) report.scratchBytes), report.bounded⟩

/-- The same local effect proof protects any path apart from the stage
name, including the existing manifest and already synced runs. -/
theorem keepsOther (report : NativeCheckpointManifestDataError (image := image) state cut)
    {path : FilePath} {inode : Nat} {bytes : ByteArray} (different : path ≠ state.session.directory.file .stagedManifest)
    (stable : report.settled.view.Stable path inode bytes) : report.view.Stable path inode bytes :=
  report.frame.keepsStableOnSyncError (effective := false) rfl report.privateInode different stable

private theorem fixedNameNeStage (directory : DiskDirectory) {file : DiskFile}
    (fixed : file = .lock ∨ file = .manifest) : directory.file file ≠ directory.file .stagedManifest := by
  intro equal
  rcases fixed with rfl | rfl <;>
    have names := (String.append_right_inj (directory.path.toString ++ "/")).mp (congrArg FilePath.toString equal)
    <;> contradiction

theorem rootAndLock (report : NativeCheckpointManifestDataError (image := image) state cut) (valid : state.Valid) :
    report.view.visible state.session.directory.path = some (report.settled.runs.captured.inode state.directorySlot.description) ∧
    report.view.visible (state.session.directory.file .lock) = some (state.census.inode state.owner.description) := by
  constructor
  · rw [report.frame.visibleNames _ (file_ne_directory _ .stagedManifest).symm, report.settled.sameDirectory]
    exact (report.settled.directoryCustody valid).2.2.1
  · rw [report.frame.visibleNames _ (fixedNameNeStage _ (.inl rfl)), report.settled.sameNames .lock]
    exact report.settled.lockAtIssue

theorem selectedPair (report : NativeCheckpointManifestDataError (image := image) state cut) (valid : state.Valid) :
    (report.settled.runs.files report.after).directory.active = state.writer.target.pair ∧
    (report.settled.runs.files report.after).directory.crashImages = [state.writer.target.pair] ∧
    CheckpointWalView.ofFiles (report.settled.runs.files report.after) = CheckpointWalView.ofFiles state.files.image := by
  obtain ⟨pair, survives, wal⟩ := report.settled.selectedPair valid
  exact ⟨report.pair.trans pair, report.crashPair.trans survives, report.wal.trans wal⟩

theorem manifestAtReturn (report : NativeCheckpointManifestDataError (image := image) state cut) (valid : state.Valid) :
    match (report.settled.runs.files report.after).directory.active.manifest with
    | none => report.view.visible (state.session.directory.file .manifest) = none
    | some bytes => ∃ inode, (report.settled.runs.views 0).Stable (state.session.directory.file .manifest) inode bytes ∧
        report.view.Stable (state.session.directory.file .manifest) inode bytes := by
  have before : state.files.image.directory.active = state.writer.target.pair := valid.retained.resumed.ready.selected
  rw [(report.selectedPair valid).1, ← before]
  have manifest := report.settled.runs.manifestAtEnd
  cases known : state.files.image.directory.active.manifest with
  | none =>
    rw [known] at manifest
    rw [report.frame.visibleNames _ (fixedNameNeStage _ (.inr rfl)), report.settled.sameNames .manifest]
    exact manifest
  | some payload =>
    rw [known] at manifest
    obtain ⟨inode, initial, stable⟩ := manifest
    exact ⟨inode, initial, report.keepsOther (fixedNameNeStage _ (.inr rfl))
      (report.settled.stableAfter stable.visibleBinding stable.visibleBytes stable.crashBytes)⟩

theorem priorRunBytes (report : NativeCheckpointManifestDataError (image := image) state cut) (valid : state.Valid)
    {bytes payload : ByteArray} {metadata : Manifest.IntegrityCheckpoint} {index : Nat}
    (binding : state.writer.wal.directory.active.manifest = some bytes)
    (decoded : Manifest.IntegrityCheckpoint.decode bytes = .ok metadata)
    (within : index < metadata.header.runCount.toNat)
    (stored : state.writer.published.durable metadata.header.generation index = some payload) :
    ∃ inode, (report.settled.runs.views 0).Stable (state.session.directory.file (.run metadata.header.generation index)) inode payload ∧
      report.view.Stable (state.session.directory.file (.run metadata.header.generation index)) inode payload := by
  obtain ⟨inode, initial, stable⟩ := report.settled.runs.priorRunAtEnd valid binding decoded within stored
  exact ⟨inode, initial, report.keepsOther (runFile_ne_stagedManifest _ _ _)
    (report.settled.stableAfter stable.visibleBinding stable.visibleBytes stable.crashBytes)⟩

theorem freshRunBytes (report : NativeCheckpointManifestDataError (image := image) state cut)
    {index : Nat} (within : index < cut.checkpoint.table.runs.length) :
    ∃ run inode, cut.checkpoint.table.runs.toArray[index]? = some run ∧
      report.view.Stable (state.session.directory.file (.run cut.checkpoint.prepared.generation index)) inode run.run.bytes := by
  obtain ⟨run, inode, selected, binding, visible, durable⟩ := report.settled.runs.freshRunAtEnd within
  exact ⟨run, inode, selected, report.keepsOther (runFile_ne_stagedManifest _ _ _) (report.settled.stableAfter binding visible durable)⟩

theorem selectedCheckpoint (report : NativeCheckpointManifestDataError (image := image) state cut) (valid : state.Valid) :
    SelectedIntegrityCheckpoint (report.settled.runs.runs report.after).guaranteed
      (report.settled.runs.files report.after).directory.active.manifest state.writer.checkpoint := by
  let ready := valid.retained
  have agrees : SelectedRunsAgree state.writer.wal.directory.active.manifest
      (report.settled.runs.runs report.after).guaranteed state.writer.published.durable := by
    intro bytes metadata binding decoded index within
    have selected := ready.resumed.selected
    rw [← ready.walPair] at selected
    obtain ⟨payload, stored⟩ := selected.runExists binding decoded within
    obtain ⟨_, _, exactRun⟩ := report.priorRunBytes valid binding decoded within stored
    exact exactRun.guaranteed.trans stored.symm
  rw [(report.selectedPair valid).1, ← ready.walPair]
  exact SelectedIntegrityCheckpoint.withRunMap (ready.walPair.symm ▸ ready.resumed.selected) agrees.symm

end NativeCheckpointManifestDataError

structure NativeReturnedCheckpointManifestDataError {image : Type} (current : NativeReadPosition history log)
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    (report : NativeCheckpointManifestDataError (image := image) current.state cut) : Prop where
  issued : CheckpointIssue report.settled.runs.perform current.state.session.phase report.settled.runs.entry
    cut.checkpoint.prepared cut.checkpoint.manifest cut.completed (.manifest .writeStaged) report.atIssue
  returned : runCheckpointWithEffects report.settled.runs.perform (current.state.session.phase, report.settled.runs.entry) =
    .error report.cause (.poisoned, ⟨(current.state.cache, report.after), current.state.files.owners⟩)
  held : current.state.files.owners.Owns current.state.session.directory current.state.session.descriptor
  openedCensus : report.settled.runs.descriptors report.opened = report.handle.1
  temporary : report.handle.2.1 ∈ (report.settled.runs.descriptors report.beforeDrop).slots
  census : report.settled.runs.descriptors report.after = current.state.census
  closed : (report.settled.runs.descriptors report.after).references report.handle.2.1.description = []
  directoryLive : current.state.directorySlot ∈ (report.settled.runs.descriptors report.after).slots
  lockLive : current.state.owner ∈ (report.settled.runs.descriptors report.after).slots
  directoryObject : report.view.visible current.state.session.directory.path =
    some (report.settled.runs.captured.inode current.state.directorySlot.description)
  lockObject : report.view.visible (current.state.session.directory.file .lock) =
    some (current.state.census.inode current.state.owner.description)
  pair : (report.settled.runs.files report.after).directory.active = current.state.writer.target.pair
  survives : (report.settled.runs.files report.after).directory.crashImages = [current.state.writer.target.pair]
  wal : CheckpointWalView.ofFiles (report.settled.runs.files report.after) = CheckpointWalView.ofFiles current.state.files.image
  checkpoint : SelectedIntegrityCheckpoint (report.settled.runs.runs report.after).guaranteed
    (report.settled.runs.files report.after).directory.active.manifest current.state.writer.checkpoint
  replay : PendingClientReplay log current.reads history
  bounded : ∀ read ∈ current.reads, read.BoundedBy history.length

theorem NativeReadPosition.checkpointManifestDataError {image : Type} (current : NativeReadPosition history log)
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    (report : NativeCheckpointManifestDataError (image := image) current.state cut) :
    NativeReturnedCheckpointManifestDataError current report := by
  obtain ⟨valid, _, replay⟩ := current.readPrefix.refines
  obtain ⟨slot, census, closed⟩ := report.releasesStage
  obtain ⟨directory, lock⟩ := report.rootAndLock valid
  obtain ⟨pair, survives, wal⟩ := report.selectedPair valid
  exact ⟨report.issues valid, report.returns valid, valid.retained.held, report.atOpen, slot, census, closed,
    census.symm ▸ valid.directoryLive, census.symm ▸ valid.ownerLive, directory, lock, pair, survives, wal,
    report.selectedCheckpoint valid, replay, current.readPrefix.readsBounded⟩

end Alvoki.Storage.DiskSession
