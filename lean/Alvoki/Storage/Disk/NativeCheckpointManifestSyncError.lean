import Alvoki.Storage.Disk.NativeCheckpointRunDirectoryError
import Alvoki.Storage.Disk.CheckpointRunFileSyncFailure

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

/-- The actual first directory sync returned on the cached directory
description after the ordered run pairs. Its reached view settles the
names and preserves their file bytes and the live descriptors. -/
structure NativeCheckpointRunsSynced {image : Type} (state : NativeReadyState)
    (cut : CheckpointPowerCut state.session.directory state.writer) where
  runs : NativeCheckpointRunObservations (image := image) state cut cut.checkpoint.table.runs.length
  after : image
  returned : runs.primitives.fsync (runs.captured, state.directorySlot, 0) (runs.atRun cut.checkpoint.table.runs.length) =
    .ok () after
  census : runs.descriptors after = runs.descriptors (runs.atRun cut.checkpoint.table.runs.length)
  directoryAtIssue : (runs.views cut.checkpoint.table.runs.length).visible state.session.directory.path =
    some (state.census.inode state.directorySlot.description)
  lockAtIssue : (runs.views cut.checkpoint.table.runs.length).visible (state.session.directory.file .lock) =
    some (state.census.inode state.owner.description)
  view : RunDirectoryInodeView state.session.directory (runs.inodes after) (runs.runs after)
  sameDirectory : view.visible state.session.directory.path =
    (runs.views cut.checkpoint.table.runs.length).visible state.session.directory.path
  sameNames : ∀ file : DiskFile, view.visible (state.session.directory.file file) =
    (runs.views cut.checkpoint.table.runs.length).visible (state.session.directory.file file)
  settledNames : ∀ file : DiskFile, ∀ surviving ∈ view.crashBindings,
    surviving (state.session.directory.file file) = view.visible (state.session.directory.file file)
  keepsDurableBytes : ∀ (file : DiskFile) inode bytes,
    (runs.views cut.checkpoint.table.runs.length).visible (state.session.directory.file file) = some inode →
    (runs.inodes (runs.atRun cut.checkpoint.table.runs.length)).visible inode = bytes →
    (runs.inodes (runs.atRun cut.checkpoint.table.runs.length)).crashBytes inode = [bytes] →
    (runs.inodes after).visible inode = bytes ∧ (runs.inodes after).crashBytes inode = [bytes]
  directoryEffect : (runs.files after).directory = (runs.files (runs.atRun cut.checkpoint.table.runs.length)).directory.syncDirectory
  walFrame : CheckpointWalView.ofFiles (runs.files after) =
    CheckpointWalView.ofFiles (runs.files (runs.atRun cut.checkpoint.table.runs.length))

namespace NativeCheckpointRunsSynced

variable {image : Type} {state : NativeReadyState} {cut : CheckpointPowerCut state.session.directory state.writer}

theorem syncReturns (seen : NativeCheckpointRunsSynced (image := image) state cut) :
    seen.runs.perform cut.checkpoint.prepared cut.checkpoint.manifest .syncRunsDirectory
      (state.cache, seen.runs.atRun cut.checkpoint.table.runs.length) = .ok () (state.cache, seen.after) := by
  change SyncPathGroup.run (sync state.session.directory.path seen.runs.primitives.openRead seen.runs.primitives.fsync)
    #[state.session.directory.path] (state.cache, seen.runs.atRun cut.checkpoint.table.runs.length) = _
  rw [SyncPathGroup.run_single]
  simp only [sync, Cache.resolve, beq_self_eq_true, ↓reduceIte, seen.runs.directoryCached, seen.returned, withCache]

theorem runPrefix (seen : NativeCheckpointRunsSynced (image := image) state cut) :
    ((runSteps cut.checkpoint.table.runs.length ++ [Step.syncRunsDirectory]).forM
      (seen.runs.perform cut.checkpoint.prepared cut.checkpoint.manifest)) seen.runs.entry.image =
      .ok () (state.cache, seen.after) := by
  rw [List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM]
  simp only [Bind.bind, EStateM.bind, seen.runs.runPrefix, List.forM_eq_forM, List.forM_cons,
    seen.syncReturns, List.forM_nil, Pure.pure, EStateM.pure]

theorem keepsCensus (seen : NativeCheckpointRunsSynced (image := image) state cut) :
    seen.runs.descriptors seen.after = state.census :=
  seen.census.trans (seen.runs.prefixCensus _ (Nat.le_refl _))

theorem directoryCustody (seen : NativeCheckpointRunsSynced (image := image) state cut) (valid : state.Valid) :
    state.directorySlot ∈ (seen.runs.descriptors (seen.runs.atRun cut.checkpoint.table.runs.length)).slots ∧
    state.owner ∈ (seen.runs.descriptors (seen.runs.atRun cut.checkpoint.table.runs.length)).slots ∧
    (seen.runs.views cut.checkpoint.table.runs.length).visible state.session.directory.path =
      some (seen.runs.captured.inode state.directorySlot.description) ∧
    (seen.runs.views cut.checkpoint.table.runs.length).visible (state.session.directory.file .lock) =
      some (state.census.inode state.owner.description) := by
  have census := seen.runs.prefixCensus _ (Nat.le_refl _)
  exact ⟨census.symm ▸ valid.directoryLive, census.symm ▸ valid.ownerLive,
    by rw [seen.runs.capturedInode]; exact seen.directoryAtIssue, seen.lockAtIssue⟩

/-- The successful directory barrier keeps already durable bytes and
settles the binding of each managed file in the reached directory. -/
theorem stableAfter (seen : NativeCheckpointRunsSynced (image := image) state cut)
    {file : DiskFile} {inode : Nat} {bytes : ByteArray}
    (binding : (seen.runs.views cut.checkpoint.table.runs.length).visible (state.session.directory.file file) = some inode)
    (visible : (seen.runs.inodes (seen.runs.atRun cut.checkpoint.table.runs.length)).visible inode = bytes)
    (durable : (seen.runs.inodes (seen.runs.atRun cut.checkpoint.table.runs.length)).crashBytes inode = [bytes]) :
    seen.view.Stable (state.session.directory.file file) inode bytes := by
  have named := (seen.sameNames file).trans binding
  obtain ⟨visibleAfter, durableAfter⟩ := seen.keepsDurableBytes file inode bytes binding visible durable
  exact ⟨named, fun surviving member => (seen.settledNames file surviving member).trans named, visibleAfter, durableAfter⟩

theorem selectedPair (seen : NativeCheckpointRunsSynced (image := image) state cut) (valid : state.Valid) :
    (seen.runs.files seen.after).directory.active = state.writer.target.pair ∧
    (seen.runs.files seen.after).directory.crashImages = [state.writer.target.pair] ∧
    CheckpointWalView.ofFiles (seen.runs.files seen.after) = CheckpointWalView.ofFiles state.files.image := by
  have pair : state.files.image.directory.active = state.writer.target.pair := valid.retained.resumed.ready.selected
  have entry := seen.runs.filesAtRun _ (Nat.le_refl _)
  refine ⟨?_, ?_, seen.walFrame.trans (congrArg CheckpointWalView.ofFiles entry)⟩
  all_goals rw [seen.directoryEffect, entry]
  all_goals simp only [DirectoryPublication.Image.syncDirectory, pair]

end NativeCheckpointRunsSynced

/-- Through staging and the returned file barrier, the same opened
temporary description is used. Files outside the stage path obey the
reported private-inode frame. -/
structure NativeCheckpointManifestSyncError {image : Type} (state : NativeReadyState)
    (cut : CheckpointPowerCut state.session.directory state.writer) where
  settled : NativeCheckpointRunsSynced (image := image) state cut
  completed : cut.completed = runSteps cut.checkpoint.table.runs.length ++ [.syncRunsDirectory, .manifest .writeStaged]
  handle : CheckpointOpenHandle
  opened : image
  buffered : image
  flushed : image
  opening : settled.runs.primitives.StageOpened (state.session.directory.file .stagedManifest) settled.after handle opened
  wrote : settled.runs.primitives.write handle cut.checkpoint.manifest opened = .ok () buffered
  flushedBytes : settled.runs.primitives.flush handle buffered = .ok () flushed
  free : ∀ old ∈ (settled.runs.descriptors settled.after).slots, old.address ≠ handle.2.1.address
  fresh : (settled.runs.descriptors settled.after).references handle.2.1.description = []
  allocated : handle.1 = (settled.runs.descriptors settled.after).insert handle.2.1 free
  atOpen : settled.runs.descriptors opened = handle.1
  atSync : settled.runs.descriptors flushed = handle.1
  issuingNames : FilePath → Option Nat
  staged : issuingNames (state.session.directory.file .stagedManifest) = some (handle.1.inode handle.2.1.description)
  written : (settled.runs.inodes flushed).visible (handle.1.inode handle.2.1.description) = cut.checkpoint.manifest
  privateInode : ∀ other, settled.view.visible other = some (handle.1.inode handle.2.1.description) →
    other = state.session.directory.file .stagedManifest
  cause : IO.Error
  after : image
  failed : settled.runs.primitives.fsync handle flushed = .error cause after
  afterClose : settled.runs.descriptors after = handle.1.afterDrops [handle.2.1.closeEvent]
  fileEffect : settled.runs.inodes after = if cut.tookEffect then
    (settled.runs.inodes flushed).completeFileSync (handle.1.inode handle.2.1.description) else settled.runs.inodes flushed
  view : RunDirectoryInodeView state.session.directory (settled.runs.inodes after) (settled.runs.runs after)
  sameNames : view.visible = issuingNames
  frame : RunWriteInodeFrame (state.session.directory.file .stagedManifest)
    (handle.1.inode handle.2.1.description) (settled.runs.inodes flushed) settled.view view
  pair : (settled.runs.files after).directory.active = (settled.runs.files settled.after).directory.active
  crashPair : (settled.runs.files after).directory.crashImages = (settled.runs.files settled.after).directory.crashImages
  wal : CheckpointWalView.ofFiles (settled.runs.files after) = CheckpointWalView.ofFiles (settled.runs.files settled.after)

namespace NativeCheckpointManifestSyncError

variable {image : Type} {state : NativeReadyState} {cut : CheckpointPowerCut state.session.directory state.writer}

def error (report : NativeCheckpointManifestSyncError (image := image) state cut) : IO.Error :=
  IO.userError s!"sync failed for '{state.session.directory.file .stagedManifest}': {report.cause}"

def atIssue (report : NativeCheckpointManifestSyncError (image := image) state cut) : CensusDirectoryCache × image :=
  (state.cache.remember (state.session.directory.file .stagedManifest) report.handle, report.flushed)

theorem current (report : NativeCheckpointManifestSyncError (image := image) state cut) :
    cut.current = .manifest .syncStaged := by
  have ordered := cut.schedule
  rw [report.completed] at ordered
  simp only [CheckpointPublication.steps, Publication.steps, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
    List.nil_append] at ordered
  exact (List.cons.inj (List.cons.inj (List.cons.inj (List.append_cancel_left ordered)).2).2).1.symm

theorem writeReturns (report : NativeCheckpointManifestSyncError (image := image) state cut) :
    report.settled.runs.perform cut.checkpoint.prepared cut.checkpoint.manifest (.manifest .writeStaged)
      (state.cache, report.settled.after) = .ok () report.atIssue :=
  report.settled.runs.primitives.remembersManifest state.session.directory cut.checkpoint.prepared cut.checkpoint.manifest
    state.cache report.opening report.wrote report.flushedBytes

theorem issues (report : NativeCheckpointManifestSyncError (image := image) state cut) (valid : state.Valid) :
    CheckpointIssue report.settled.runs.perform state.session.phase report.settled.runs.entry cut.checkpoint.prepared
      cut.checkpoint.manifest cut.completed (.manifest .syncStaged) report.atIssue := by
  have scheduled := cut.schedule
  rw [report.current] at scheduled
  have completed : (cut.completed.forM (report.settled.runs.perform cut.checkpoint.prepared cut.checkpoint.manifest))
      report.settled.runs.entry.image = .ok () report.atIssue := by
    have order : cut.completed =
        (runSteps cut.checkpoint.table.runs.length ++ [.syncRunsDirectory]) ++ [.manifest .writeStaged] := by
      rw [report.completed, List.append_assoc]
      rfl
    rw [order, List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM]
    simp only [Bind.bind, EStateM.bind, report.settled.runPrefix, List.forM_eq_forM, List.forM_cons,
      report.writeReturns, List.forM_nil, Pure.pure, EStateM.pure]
  rw [valid.phase]
  exact cut.preflight.reachesIssue report.settled.runs.perform report.settled.runs.entry scheduled completed

theorem callbackFails (report : NativeCheckpointManifestSyncError (image := image) state cut) :
    report.settled.runs.perform cut.checkpoint.prepared cut.checkpoint.manifest (.manifest .syncStaged) report.atIssue =
      .error report.error (state.cache, report.after) := by
  let path := state.session.directory.file .stagedManifest
  let openRead := report.settled.runs.primitives.openRead
  let fsync := report.settled.runs.primitives.fsync
  change SyncPathGroup.run (sync state.session.directory.path openRead fsync) #[path]
    (state.cache.remember path report.handle, report.flushed) = _
  have consumed : state.cache.consume (state.session.directory.file .stagedManifest) = state.cache := by
    have pending := report.settled.runs.pending
    cases known : state.cache with
    | mk directory active entries => simp_all [Cache.consume]
  rw [SyncPathGroup.run_single, syncRemembered (file_ne_directory _ .stagedManifest) report.handle openRead fsync report.flushed]
  simp only [fsync, report.failed, consumed]
  rfl

theorem returns (report : NativeCheckpointManifestSyncError (image := image) state cut) (valid : state.Valid) :
    runCheckpointWithEffects report.settled.runs.perform (state.session.phase, report.settled.runs.entry) =
      .error report.error (.poisoned, ⟨(state.cache, report.after), state.files.owners⟩) := by
  obtain ⟨_, _, continued⟩ := (report.issues valid).continuation
  rw [continued, List.forM_eq_forM, List.forM_cons]
  simp only [Bind.bind, EStateM.bind, report.callbackFails, NativeCheckpointRunObservations.entry]

private theorem lockNeStage (directory : DiskDirectory) :
    directory.file .lock ≠ directory.file .stagedManifest := by
  intro equal
  have names := (String.append_right_inj (directory.path.toString ++ "/")).mp (congrArg FilePath.toString equal)
  contradiction

/-- The temporary descriptor is live when the sync is issued. Its
reported release restores exactly the held writer's original census. -/
theorem custody (report : NativeCheckpointManifestSyncError (image := image) state cut) (valid : state.Valid) :
    report.handle.2.1 ∈ (report.settled.runs.descriptors report.flushed).slots ∧
    report.settled.runs.descriptors report.after = state.census ∧
    (report.settled.runs.descriptors report.after).references report.handle.2.1.description = [] ∧
    state.directorySlot ∈ (report.settled.runs.descriptors report.after).slots ∧
    state.owner ∈ (report.settled.runs.descriptors report.after).slots ∧
    report.view.visible state.session.directory.path = some (report.settled.runs.captured.inode state.directorySlot.description) ∧
    report.view.visible (state.session.directory.file .lock) = some (state.census.inode state.owner.description) := by
  have census : report.settled.runs.descriptors report.after = report.settled.runs.descriptors report.settled.after := by
    rw [report.afterClose, report.allocated, checkpointTemporaryClose]
  have restored := census.trans report.settled.keepsCensus
  refine ⟨?_, restored, census.symm ▸ report.fresh, restored.symm ▸ valid.directoryLive, restored.symm ▸ valid.ownerLive, ?_, ?_⟩
  · rw [report.atSync, report.allocated]
    exact List.mem_cons_self
  · rw [report.frame.visibleNames _ (file_ne_directory _ .stagedManifest).symm, report.settled.sameDirectory]
    exact (report.settled.directoryCustody valid).2.2.1
  · rw [report.frame.visibleNames _ (lockNeStage _), report.settled.sameNames .lock]
    exact report.settled.lockAtIssue

/-- The staged inode still contains the exact encoded checkpoint. Its
durable bytes depend on the reported file sync effect. -/
theorem stagedBytes (report : NativeCheckpointManifestSyncError (image := image) state cut) :
    let inode := report.handle.1.inode report.handle.2.1.description
    report.view.visible (state.session.directory.file .stagedManifest) = some inode ∧
    (report.settled.runs.inodes report.after).visible inode = cut.checkpoint.manifest ∧
    (report.settled.runs.inodes report.after).crashBytes inode = (if cut.tookEffect then [cut.checkpoint.manifest]
      else (report.settled.runs.inodes report.flushed).crashBytes inode) := by
  intro inode
  have named := (congrFun report.sameNames _).trans report.staged
  refine ⟨named, ?_, ?_⟩
  · rw [report.fileEffect]
    cases cut.tookEffect <;> exact report.written
  · rw [report.fileEffect]
    cases cut.tookEffect <;> simp [WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, inode, report.written]

private theorem manifestNeStage (directory : DiskDirectory) :
    directory.file .manifest ≠ directory.file .stagedManifest := by
  intro equal
  have names := (String.append_right_inj (directory.path.toString ++ "/")).mp (congrArg FilePath.toString equal)
  contradiction

theorem stableAfter (report : NativeCheckpointManifestSyncError (image := image) state cut)
    {path : FilePath} {inode : Nat} {bytes : ByteArray}
    (other : path ≠ state.session.directory.file .stagedManifest) (prior : report.settled.view.Stable path inode bytes) :
    report.view.Stable path inode bytes :=
  report.frame.keepsStableOnSyncError report.fileEffect report.privateInode other prior

theorem priorRunBytes (report : NativeCheckpointManifestSyncError (image := image) state cut) (valid : state.Valid)
    {bytes payload : ByteArray} {metadata : Manifest.IntegrityCheckpoint} {index : Nat}
    (binding : state.writer.wal.directory.active.manifest = some bytes)
    (decoded : Manifest.IntegrityCheckpoint.decode bytes = .ok metadata)
    (within : index < metadata.header.runCount.toNat)
    (stored : state.writer.published.durable metadata.header.generation index = some payload) :
    ∃ inode, (report.settled.runs.views 0).Stable (state.session.directory.file (.run metadata.header.generation index)) inode payload ∧
      report.view.Stable (state.session.directory.file (.run metadata.header.generation index)) inode payload := by
  obtain ⟨inode, original, stable⟩ := report.settled.runs.priorRunAtEnd valid binding decoded within stored
  exact ⟨inode, original, report.stableAfter (runFile_ne_stagedManifest _ _ _)
    (report.settled.stableAfter stable.visibleBinding stable.visibleBytes stable.crashBytes)⟩

theorem freshRunBytes (report : NativeCheckpointManifestSyncError (image := image) state cut)
    {index : Nat} (within : index < cut.checkpoint.table.runs.length) :
    ∃ run inode, cut.checkpoint.table.runs.toArray[index]? = some run ∧
      report.view.Stable (state.session.directory.file (.run cut.checkpoint.prepared.generation index)) inode run.run.bytes := by
  obtain ⟨run, inode, selected, binding, visible, durable⟩ := report.settled.runs.freshRunAtEnd within
  exact ⟨run, inode, selected, report.stableAfter (runFile_ne_stagedManifest _ _ _) (report.settled.stableAfter binding visible durable)⟩

theorem selectedPair (report : NativeCheckpointManifestSyncError (image := image) state cut) (valid : state.Valid) :
    (report.settled.runs.files report.after).directory.active = state.writer.target.pair ∧
    (report.settled.runs.files report.after).directory.crashImages = [state.writer.target.pair] ∧
    CheckpointWalView.ofFiles (report.settled.runs.files report.after) = CheckpointWalView.ofFiles state.files.image := by
  obtain ⟨pair, crashes, wal⟩ := report.settled.selectedPair valid
  exact ⟨report.pair.trans pair, report.crashPair.trans crashes, report.wal.trans wal⟩

theorem manifestAtReturn (report : NativeCheckpointManifestSyncError (image := image) state cut) (valid : state.Valid) :
    match (report.settled.runs.files report.after).directory.active.manifest with
    | none => report.view.visible (state.session.directory.file .manifest) = none
    | some bytes => ∃ inode, (report.settled.runs.views 0).Stable (state.session.directory.file .manifest) inode bytes ∧
        report.view.Stable (state.session.directory.file .manifest) inode bytes := by
  have beforePair : state.files.image.directory.active = state.writer.target.pair := valid.retained.resumed.ready.selected
  rw [(report.selectedPair valid).1, ← beforePair]
  have manifest := report.settled.runs.manifestAtEnd
  cases known : state.files.image.directory.active.manifest with
  | none =>
    rw [known] at manifest
    rw [report.frame.visibleNames _ (manifestNeStage _), report.settled.sameNames .manifest]
    exact manifest
  | some bytes =>
    rw [known] at manifest
    obtain ⟨inode, entry, prior⟩ := manifest
    exact ⟨inode, entry, report.stableAfter (manifestNeStage _)
      (report.settled.stableAfter prior.visibleBinding prior.visibleBytes prior.crashBytes)⟩

theorem selectedCheckpoint (report : NativeCheckpointManifestSyncError (image := image) state cut) (valid : state.Valid) :
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

end NativeCheckpointManifestSyncError

/-- The native checkpoint returns this staged-file diagnostic before
rename, with the exact earlier checkpoint and WAL read replay. -/
structure NativeReturnedCheckpointManifestSyncError {image : Type} (current : NativeReadPosition history log)
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    (report : NativeCheckpointManifestSyncError (image := image) current.state cut) : Prop where
  issued : CheckpointIssue report.settled.runs.perform current.state.session.phase report.settled.runs.entry
    cut.checkpoint.prepared cut.checkpoint.manifest cut.completed (.manifest .syncStaged) report.atIssue
  returned : runCheckpointWithEffects report.settled.runs.perform (current.state.session.phase, report.settled.runs.entry) =
    .error report.error (.poisoned, ⟨(current.state.cache, report.after), current.state.files.owners⟩)
  held : current.state.files.owners.Owns current.state.session.directory current.state.session.descriptor
  openedCensus : report.settled.runs.descriptors report.opened = report.handle.1
  syncCensus : report.settled.runs.descriptors report.flushed = report.handle.1
  issuingSlot : report.handle.2.1 ∈ (report.settled.runs.descriptors report.flushed).slots
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

theorem NativeReadPosition.checkpointManifestSyncError {image : Type} (current : NativeReadPosition history log)
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    (report : NativeCheckpointManifestSyncError (image := image) current.state cut) :
    NativeReturnedCheckpointManifestSyncError current report := by
  obtain ⟨valid, _, replay⟩ := current.readPrefix.refines
  obtain ⟨slot, census, closed, directoryLive, lockLive, directory, lock⟩ := report.custody valid
  obtain ⟨pair, survives, wal⟩ := report.selectedPair valid
  exact ⟨report.issues valid, report.returns valid, valid.retained.held, report.atOpen, report.atSync,
    slot, census, closed, directoryLive, lockLive, directory, lock, pair, survives, wal,
    report.selectedCheckpoint valid, replay, current.readPrefix.readsBounded⟩

end Alvoki.Storage.DiskSession
