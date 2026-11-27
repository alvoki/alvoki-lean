import Alvoki.Storage.Disk.Proofs.Native.Checkpoint.NativeReadyCheckpoint
import Alvoki.Storage.Disk.Proofs.Read.NativeReadRecoveryTrace
import Alvoki.Storage.Disk.Proofs.Checkpoint.CheckpointRunDirectoryCut
import Alvoki.Storage.Disk.Proofs.Checkpoint.SelectedRuns

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

/-- The reported successful run pairs before the chosen checkpoint
operation. Their physical frames and temporary lifetimes concern the same
callbacks used by checkpoint publication. -/
structure NativeCheckpointRunObservations {image : Type} (state : NativeReadyState)
    (cut : CheckpointPowerCut state.session.directory state.writer) (count : Nat) where
  primitives : CheckpointPrimitiveCalls CheckpointOpenHandle image
  descriptors : image → DescriptorInventory
  atRun : Nat → image
  initialCensus : descriptors (atRun 0) = state.census
  pending : state.cache.pending = []
  captured : DescriptorInventory
  directoryCached : state.cache.directory = some (captured, state.directorySlot, 0)
  capturedInode : captured.inode state.directorySlot.description = state.census.inode state.directorySlot.description
  inodes : image → WalInodeImage
  runs : image → RunUnlinkImage
  views : ∀ index, RunDirectoryInodeView state.session.directory (inodes (atRun index)) (runs (atRun index))
  selectedEntry : CheckpointRunPrefix.EntrySelection state.writer (views 0)
  runReports : ∀ index < count,
    ∃ run : Compaction.CheckedRun, cut.checkpoint.table.runs.toArray[index]? = some run ∧
      ∃ observed : CompletedCheckpointTemporaryFile descriptors primitives.cached primitives.cached.writeRun
        (state.session.directory.file (.run cut.checkpoint.prepared.generation index)) run.run.bytes
        (atRun index) (atRun (index + 1)),
      let path := state.session.directory.file (.run cut.checkpoint.prepared.generation index)
      let inode := observed.handle.1.inode observed.handle.2.1.description
      inodes (atRun (index + 1)) = (inodes observed.flushed).completeFileSync inode ∧
      (views (index + 1)).visible path = some inode ∧
      (inodes observed.flushed).visible inode = run.run.bytes ∧
      (∀ other, (views index).visible other = some inode → other = path) ∧
      RunWriteInodeFrame path inode (inodes observed.flushed) (views index) (views (index + 1))
  files : image → FileImage
  manifestAtEntry :
    match state.files.image.directory.active.manifest with
    | none => (views 0).visible (state.session.directory.file .manifest) = none
    | some bytes => ∃ inode, (views 0).Stable (state.session.directory.file .manifest) inode bytes
  initialFiles : files (atRun 0) = state.files.image
  runFileFrame : ∀ index < count, files (atRun (index + 1)) = files (atRun index)

/-- The first checkpoint directory barrier follows the completed run
pairs, without requiring any successful manifest operation. Each raw
run's inode frame concerns the same handle as its write, sync and close. -/
structure NativeCheckpointRunDirectoryError {image : Type} (state : NativeReadyState)
    (cut : CheckpointPowerCut state.session.directory state.writer)
    extends NativeCheckpointRunObservations (image := image) state cut cut.checkpoint.table.runs.length where
  completed : cut.completed = runSteps cut.checkpoint.table.runs.length
  directoryBound : (views cut.checkpoint.table.runs.length).visible state.session.directory.path =
    some (state.census.inode state.directorySlot.description)
  lockBound : (views cut.checkpoint.table.runs.length).visible (state.session.directory.file .lock) =
    some (state.census.inode state.owner.description)
  cause : IO.Error
  after : image
  failed : primitives.fsync (captured, state.directorySlot, 0) (atRun cut.checkpoint.table.runs.length) = .error cause after
  census : descriptors after = descriptors (atRun cut.checkpoint.table.runs.length)
  bindingsAfter : FilePath → Option Nat
  visibleNames : bindingsAfter = (views cut.checkpoint.table.runs.length).visible
  inodeBytes : inodes after = inodes (atRun cut.checkpoint.table.runs.length)
  runsAfter : runs after = if cut.tookEffect then (runs (atRun cut.checkpoint.table.runs.length)).syncDirectory
    else runs (atRun cut.checkpoint.table.runs.length)
  directoryEffect : (files after).directory = if cut.tookEffect then
    (files (atRun cut.checkpoint.table.runs.length)).directory.syncDirectory else (files (atRun cut.checkpoint.table.runs.length)).directory
  walFrame : CheckpointWalView.ofFiles (files after) = CheckpointWalView.ofFiles (files (atRun cut.checkpoint.table.runs.length))

namespace NativeCheckpointRunObservations

variable {image : Type} {state : NativeReadyState} {cut : CheckpointPowerCut state.session.directory state.writer} {count : Nat}

def entry (report : NativeCheckpointRunObservations (image := image) state cut count) :
    LockedFileState (CensusDirectoryCache × image) :=
  ⟨(state.cache, report.atRun 0), state.files.owners⟩

noncomputable def perform (report : NativeCheckpointRunObservations (image := image) state cut count) :=
  report.primitives.cached.perform state.session.directory

theorem runPrefix (report : NativeCheckpointRunObservations (image := image) state cut count) :
    ((runSteps count).forM (report.perform cut.checkpoint.prepared cut.checkpoint.manifest)) report.entry.image =
      .ok () (state.cache, report.atRun count) := by
  exact runSteps_returned _ _ (fun index => (state.cache, report.atRun index)) (fun index within => by
    obtain ⟨run, found, observed, _⟩ := report.runReports index within
    exact observed.runReturns report.primitives state.session.directory cut.checkpoint.prepared cut.checkpoint.manifest found
      state.cache report.pending)

theorem prefixCensus (report : NativeCheckpointRunObservations (image := image) state cut count)
    (index : Nat) (within : index ≤ count) :
    report.descriptors (report.atRun index) = state.census := by
  induction index with
  | zero => exact report.initialCensus
  | succ index prior =>
    obtain ⟨_, _, observed, _⟩ := report.runReports index within
    exact observed.keepsCensus.1.trans (prior (Nat.le_of_lt within))

theorem stablePath (report : NativeCheckpointRunObservations (image := image) state cut count)
    {path : FilePath} {inode : Nat} {bytes : ByteArray} (entry : (report.views 0).Stable path inode bytes)
    (different : ∀ index < count,
      path ≠ state.session.directory.file (.run cut.checkpoint.prepared.generation index))
    (through : Nat) (bounded : through ≤ count) :
    (report.views through).Stable path inode bytes := by
  induction through with
  | zero => exact entry
  | succ prior earlier =>
    obtain ⟨_, _, _, synced, _, _, privateBinding, frame⟩ := report.runReports prior bounded
    exact frame.keepsStable synced privateBinding (different prior bounded) (earlier (Nat.le_of_lt bounded))

theorem manifestNeRun (generation : UInt64) (index : Nat) :
    state.session.directory.file .manifest ≠ state.session.directory.file (.run generation index) := by
  intro equal
  have names := congrArg FilePath.toString equal
  have raw : "MANIFEST" = renderRunFileName generation index :=
    (String.append_right_inj (state.session.directory.path.toString ++ "/")).mp names
  have differentPrefix := congrArg (fun name : String => name.toList.take 4) raw
  change "MANIFEST".toList.take 4 = ("run-" ++ generation.toNat.repr ++ "-" ++ index.repr ++ ".v3").toList.take 4 at differentPrefix
  simp [String.toList_append] at differentPrefix

/-- The run writes target a fresh generation. Every earlier selected
canonical inode and durable payload is stable at the end of the prefix. -/
theorem priorRunAtEnd (report : NativeCheckpointRunObservations (image := image) state cut count) (valid : state.Valid)
    {bytes payload : ByteArray} {metadata : Manifest.IntegrityCheckpoint} {index : Nat}
    (binding : state.writer.wal.directory.active.manifest = some bytes)
    (decoded : Manifest.IntegrityCheckpoint.decode bytes = .ok metadata)
    (within : index < metadata.header.runCount.toNat)
    (stored : state.writer.published.durable metadata.header.generation index = some payload) :
    ∃ inode, (report.views 0).Stable (state.session.directory.file (.run metadata.header.generation index)) inode payload ∧
      (report.views count).Stable (state.session.directory.file (.run metadata.header.generation index)) inode payload := by
  let path := state.session.directory.file (.run metadata.header.generation index)
  have different := (cut.priorSelectedGeneration valid.retained binding decoded).2
  obtain ⟨inode, entry⟩ := report.selectedEntry bytes metadata binding decoded index within payload stored
  have apart (other : Nat) (_ : other < count) :
      path ≠ state.session.directory.file (.run cut.checkpoint.prepared.generation other) :=
    runPath_ne state.session.directory (fun equal => different (congrArg Prod.fst equal))
  exact ⟨inode, entry, report.stablePath entry apart _ (Nat.le_refl _)⟩

/-- Each completed run remains on the inode that its successful file
barrier synced, through all later writes to distinct run paths. -/
theorem freshRunAtEnd (report : NativeCheckpointRunObservations (image := image) state cut count)
    {index : Nat} (within : index < count) :
    ∃ (run : Compaction.CheckedRun) (inode : Nat), cut.checkpoint.table.runs.toArray[index]? = some run ∧
      (report.views count).visible (state.session.directory.file (.run cut.checkpoint.prepared.generation index)) = some inode ∧
      (report.inodes (report.atRun count)).visible inode = run.run.bytes ∧
      (report.inodes (report.atRun count)).crashBytes inode = [run.run.bytes] := by
  let generation := cut.checkpoint.prepared.generation
  have reached (through : Nat) (bounded : through ≤ count) : ∀ index < through,
      ∃ (run : Compaction.CheckedRun) (inode : Nat), cut.checkpoint.table.runs.toArray[index]? = some run ∧
        (report.views through).visible (state.session.directory.file (.run generation index)) = some inode ∧
        (report.inodes (report.atRun through)).visible inode = run.run.bytes ∧
        (report.inodes (report.atRun through)).crashBytes inode = [run.run.bytes] := by
    induction through with
    | zero => intro index inside; omega
    | succ prior earlier =>
      intro index inside
      obtain ⟨run, selected, observed, synced, bound, bytes, privateBinding, frame⟩ := report.runReports prior bounded
      by_cases same : index = prior
      · subst index
        refine ⟨run, _, selected, bound, synced.symm ▸ bytes, ?_⟩
        rw [synced]
        simp [WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, bytes]
      · obtain ⟨earlierRun, inode, selected, bound, bytes, crash⟩ := earlier (Nat.le_of_lt bounded) index (by omega)
        have apart : state.session.directory.file (.run generation index) ≠ state.session.directory.file (.run generation prior) :=
          runPath_ne state.session.directory (fun equal => same (congrArg Prod.snd equal))
        obtain ⟨different, named, visible⟩ := frame.keepsVisible synced privateBinding apart bound bytes
        refine ⟨earlierRun, inode, selected, named, visible, ?_⟩
        rw [synced]
        simp [WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, different, frame.crashBytes _ different, crash]
  exact reached _ (Nat.le_refl _) index within

theorem filesAtRun (report : NativeCheckpointRunObservations (image := image) state cut count) (index : Nat)
    (within : index ≤ count) : report.files (report.atRun index) = state.files.image := by
  induction index with
  | zero => exact report.initialFiles
  | succ index prior => exact (report.runFileFrame index within).trans (prior (Nat.le_of_lt within))

theorem manifestAtEnd (report : NativeCheckpointRunObservations (image := image) state cut count) :
    match state.files.image.directory.active.manifest with
    | none => (report.views count).visible (state.session.directory.file .manifest) = none
    | some bytes => ∃ inode, (report.views 0).Stable (state.session.directory.file .manifest) inode bytes ∧
        (report.views count).Stable (state.session.directory.file .manifest) inode bytes := by
  have entry := report.manifestAtEntry
  cases manifest : state.files.image.directory.active.manifest with
  | none =>
    rw [manifest] at entry
    have absent (through : Nat) (bounded : through ≤ count) :
        (report.views through).visible (state.session.directory.file .manifest) = none := by
      induction through with
      | zero => exact entry
      | succ prior earlier =>
        obtain ⟨_, _, _, _, _, _, _, frame⟩ := report.runReports prior bounded
        exact (frame.visibleNames _ (manifestNeRun cut.checkpoint.prepared.generation prior)).trans
          (earlier (Nat.le_of_lt bounded))
    exact absent _ (Nat.le_refl _)
  | some bytes =>
    rw [manifest] at entry
    obtain ⟨inode, stable⟩ := entry
    exact ⟨inode, stable, report.stablePath stable
      (fun index _ => manifestNeRun cut.checkpoint.prepared.generation index) _ (Nat.le_refl _)⟩

/-- Any effect local to the next run leaves the prior selected run
at the same inode, with its original visible and surviving bytes. -/
theorem priorRunAfter (report : NativeCheckpointRunObservations (image := image) state cut count)
    {after : image} {view : RunDirectoryInodeView state.session.directory (report.inodes after) (report.runs after)}
    (valid : state.Valid)
    (keep : ∀ {path inode bytes}, path ≠ state.session.directory.file (.run cut.checkpoint.prepared.generation count) →
      (report.views count).Stable path inode bytes → view.Stable path inode bytes)
    {bytes payload : ByteArray} {metadata : Manifest.IntegrityCheckpoint} {index : Nat}
    (binding : state.writer.wal.directory.active.manifest = some bytes)
    (decoded : Manifest.IntegrityCheckpoint.decode bytes = .ok metadata) (within : index < metadata.header.runCount.toNat)
    (stored : state.writer.published.durable metadata.header.generation index = some payload) :
    ∃ inode, (report.views 0).Stable (state.session.directory.file (.run metadata.header.generation index)) inode payload ∧
      view.Stable (state.session.directory.file (.run metadata.header.generation index)) inode payload := by
  obtain ⟨inode, entry, stable⟩ := report.priorRunAtEnd valid binding decoded within stored
  have generation := (cut.priorSelectedGeneration valid.retained binding decoded).2
  exact ⟨inode, entry, keep (runPath_ne _ (fun equal => generation (congrArg Prod.fst equal))) stable⟩

/-- Before any manifest staging, both absence and stable selected
contents of the canonical manifest are preserved by a local run effect. -/
theorem manifestAfter (report : NativeCheckpointRunObservations (image := image) state cut count)
    {after : image} {view : RunDirectoryInodeView state.session.directory (report.inodes after) (report.runs after)}
    (visible : ∀ path, path ≠ state.session.directory.file (.run cut.checkpoint.prepared.generation count) →
      view.visible path = (report.views count).visible path)
    (keep : ∀ {path inode bytes}, path ≠ state.session.directory.file (.run cut.checkpoint.prepared.generation count) →
      (report.views count).Stable path inode bytes → view.Stable path inode bytes) :
    match state.files.image.directory.active.manifest with
    | none => view.visible (state.session.directory.file .manifest) = none
    | some bytes => ∃ inode, (report.views 0).Stable (state.session.directory.file .manifest) inode bytes ∧
        view.Stable (state.session.directory.file .manifest) inode bytes := by
  have manifest := report.manifestAtEnd
  have separate := manifestNeRun (state := state) cut.checkpoint.prepared.generation count
  cases prior : state.files.image.directory.active.manifest with
  | none =>
    rw [prior] at manifest
    exact (visible _ separate).trans manifest
  | some bytes =>
    rw [prior] at manifest
    obtain ⟨inode, entry, stable⟩ := manifest
    exact ⟨inode, entry, keep separate stable⟩

/-- Select the same exact checkpoint from the guaranteed run map
at the reached file image, using only local inode frames. -/
theorem selectedAfter (report : NativeCheckpointRunObservations (image := image) state cut count)
    {after : image} {view : RunDirectoryInodeView state.session.directory (report.inodes after) (report.runs after)}
    (valid : state.Valid)
    (keep : ∀ {path inode bytes}, path ≠ state.session.directory.file (.run cut.checkpoint.prepared.generation count) →
      (report.views count).Stable path inode bytes → view.Stable path inode bytes)
    (files : report.files after = state.files.image) :
    SelectedIntegrityCheckpoint (report.runs after).guaranteed (report.files after).directory.active.manifest
      state.writer.checkpoint := by
  let ready := valid.retained
  have extra : SelectedRunsAgree state.writer.wal.directory.active.manifest (report.runs after).guaranteed
      state.writer.published.durable := by
    intro bytes metadata binding decoded index within
    have selected := ready.resumed.selected
    rw [← ready.walPair] at selected
    obtain ⟨payload, stored⟩ := selected.runExists binding decoded within
    obtain ⟨_, _, stable⟩ := report.priorRunAfter valid keep binding decoded within stored
    exact stable.guaranteed.trans stored.symm
  have pair : state.files.image.directory.active = state.writer.target.pair := ready.resumed.ready.selected
  rw [files, pair, ← ready.walPair]
  exact SelectedIntegrityCheckpoint.withRunMap (ready.walPair.symm ▸ ready.resumed.selected) extra.symm

end NativeCheckpointRunObservations

namespace NativeCheckpointRunDirectoryError

variable {image : Type} {state : NativeReadyState} {cut : CheckpointPowerCut state.session.directory state.writer}

abbrev atBarrier (report : NativeCheckpointRunDirectoryError (image := image) state cut) : image :=
  report.atRun cut.checkpoint.table.runs.length

def handle (report : NativeCheckpointRunDirectoryError (image := image) state cut) : CheckpointOpenHandle :=
  (report.captured, state.directorySlot, 0)

def error (report : NativeCheckpointRunDirectoryError (image := image) state cut) : IO.Error :=
  IO.userError s!"sync failed for '{state.session.directory.path}': {report.cause}"

theorem current (report : NativeCheckpointRunDirectoryError (image := image) state cut) : cut.current = .syncRunsDirectory := by
  have ordered := cut.schedule
  rw [report.completed, CheckpointPublication.steps, List.append_assoc] at ordered
  exact (List.cons.inj (List.append_cancel_left ordered)).1.symm

theorem runPrefix (report : NativeCheckpointRunDirectoryError (image := image) state cut) :
    (cut.completed.forM (report.perform cut.checkpoint.prepared cut.checkpoint.manifest)) report.entry.image =
      .ok () (state.cache, report.atBarrier) := by
  rw [report.completed]
  exact report.toNativeCheckpointRunObservations.runPrefix

/-- The real checkpoint preflight reaches this first directory barrier
with the original lock owner and the exact complete run prefix. -/
theorem issues (report : NativeCheckpointRunDirectoryError (image := image) state cut) (valid : state.Valid) :
    CheckpointIssue report.perform state.session.phase report.entry cut.checkpoint.prepared cut.checkpoint.manifest
      cut.completed .syncRunsDirectory (state.cache, report.atBarrier) := by
  have scheduled := cut.schedule
  rw [report.current] at scheduled
  rw [valid.phase]
  exact cut.preflight.reachesIssue report.perform report.entry scheduled report.runPrefix

theorem callbackFails (report : NativeCheckpointRunDirectoryError (image := image) state cut) :
    report.perform cut.checkpoint.prepared cut.checkpoint.manifest .syncRunsDirectory (state.cache, report.atBarrier) =
      .error report.error (state.cache, report.after) := by
  let directory := state.session.directory.path
  change SyncPathGroup.run (sync directory report.primitives.openRead report.primitives.fsync) #[directory]
    (state.cache, report.atBarrier) = _
  rw [SyncPathGroup.run_single]
  simp only [SyncHandleRouting.sync, Cache.resolve, beq_self_eq_true, ite_true, directory,
    report.directoryCached, report.failed, withCache, error]
  rfl

theorem returns (report : NativeCheckpointRunDirectoryError (image := image) state cut) (valid : state.Valid) :
    runCheckpointWithEffects report.perform (state.session.phase, report.entry) =
      .error report.error (.poisoned, ⟨(state.cache, report.after), state.files.owners⟩) := by
  obtain ⟨remaining, _, continued⟩ := (report.issues valid).continuation
  rw [continued, List.forM_eq_forM, List.forM_cons]
  simp only [Bind.bind, EStateM.bind, report.callbackFails, NativeCheckpointRunObservations.entry]

/-- The cached directory and lock still identify the original live
slots after the reported failure. The run-slot releases happened before
this first barrier, and the barrier did not change any visible binding. -/
theorem custody (report : NativeCheckpointRunDirectoryError (image := image) state cut) (valid : state.Valid) :
    report.descriptors report.after = state.census ∧
    state.directorySlot ∈ (report.descriptors report.after).slots ∧
    state.owner ∈ (report.descriptors report.after).slots ∧
    report.bindingsAfter state.session.directory.path = some (report.handle.1.inode state.directorySlot.description) ∧
    report.bindingsAfter (state.session.directory.file .lock) = some (state.census.inode state.owner.description) := by
  have census := report.census.trans (report.prefixCensus _ (Nat.le_refl _))
  rw [report.visibleNames]
  exact ⟨census, census.symm ▸ valid.directoryLive, census.symm ▸ valid.ownerLive,
    report.directoryBound.trans (congrArg some report.capturedInode.symm), report.lockBound⟩

theorem priorRunAtBarrier (report : NativeCheckpointRunDirectoryError (image := image) state cut) (valid : state.Valid)
    {bytes payload : ByteArray} {metadata : Manifest.IntegrityCheckpoint} {index : Nat}
    (binding : state.writer.wal.directory.active.manifest = some bytes)
    (decoded : Manifest.IntegrityCheckpoint.decode bytes = .ok metadata)
    (within : index < metadata.header.runCount.toNat)
    (stored : state.writer.published.durable metadata.header.generation index = some payload) :
    ∃ inode, (report.views cut.checkpoint.table.runs.length).Stable
      (state.session.directory.file (.run metadata.header.generation index)) inode payload :=
  (report.priorRunAtEnd valid binding decoded within stored).imp fun _ => And.right

/-- The same selected run is still bound to that inode and has the same
raw bytes at error return, regardless of the directory-sync effect. -/
theorem priorRunBytes (report : NativeCheckpointRunDirectoryError (image := image) state cut) (valid : state.Valid)
    {bytes payload : ByteArray} {metadata : Manifest.IntegrityCheckpoint} {index : Nat}
    (binding : state.writer.wal.directory.active.manifest = some bytes)
    (decoded : Manifest.IntegrityCheckpoint.decode bytes = .ok metadata)
    (within : index < metadata.header.runCount.toNat)
    (stored : state.writer.published.durable metadata.header.generation index = some payload) :
    ∃ inode, report.bindingsAfter (state.session.directory.file (.run metadata.header.generation index)) = some inode ∧
      (report.inodes report.after).visible inode = payload ∧ (report.inodes report.after).crashBytes inode = [payload] := by
  obtain ⟨inode, stable⟩ := report.priorRunAtBarrier valid binding decoded within stored
  exact ⟨inode, by rw [report.visibleNames]; exact stable.visibleBinding,
    report.inodeBytes.symm ▸ stable.visibleBytes, report.inodeBytes.symm ▸ stable.crashBytes⟩

/-- The exact run bytes remain visible on either returned error. They
become guaranteed as a group when the directory sync takes effect. -/
theorem freshRunBytes (report : NativeCheckpointRunDirectoryError (image := image) state cut)
    {index : Nat} (within : index < cut.checkpoint.table.runs.length) :
    (report.runs report.after).visible cut.checkpoint.prepared.generation index = cut.checkpoint.plan.files[index]? ∧
    (cut.tookEffect = true →
      (report.runs report.after).guaranteed cut.checkpoint.prepared.generation index = cut.checkpoint.plan.files[index]?) := by
  let generation := cut.checkpoint.prepared.generation
  obtain ⟨run, inode, selected, bound, bytes, _⟩ := report.freshRunAtEnd within
  have visible : (report.runs report.atBarrier).visible generation index = cut.checkpoint.plan.files[index]? := by
    rw [(report.views cut.checkpoint.table.runs.length).visibleProjects _ _ _ bound, bytes]
    change some run.run.bytes = (cut.checkpoint.table.runs.map (·.run.bytes))[index]?
    rw [List.getElem?_map, ← List.getElem?_toArray, selected]
    rfl
  rw [report.runsAfter]
  constructor
  · cases cut.tookEffect <;> exact visible
  · intro took
    simp only [took, ↓reduceIte]
    have settled : (report.runs report.atBarrier).syncDirectory.guaranteed = (report.runs report.atBarrier).visible :=
      congrArg Image.durable (RunUnlinkImage.project_settled (report.runs report.atBarrier).visible (.settled none))
    rw [settled]
    exact visible

theorem priorRuns (report : NativeCheckpointRunDirectoryError (image := image) state cut) (valid : state.Valid) :
    SelectedRunsAgree state.writer.wal.directory.active.manifest (report.runs report.after).guaranteed
      state.writer.published.durable := by
  intro bytes metadata binding decoded index within
  have selected := valid.retained.resumed.selected
  rw [← valid.retained.walPair] at selected
  obtain ⟨payload, stored⟩ := selected.runExists binding decoded within
  obtain ⟨inode, stable⟩ := report.priorRunAtBarrier valid binding decoded within stored
  rw [report.runsAfter]
  cases took : cut.tookEffect with
  | false => exact stable.guaranteed.trans stored.symm
  | true =>
    change (report.runs report.atBarrier).syncDirectory.guaranteed metadata.header.generation index = _
    have same : (report.runs report.atBarrier).syncDirectory.guaranteed = (report.runs report.atBarrier).visible :=
      congrArg Image.durable (RunUnlinkImage.project_settled (report.runs report.atBarrier).visible (.settled none))
    rw [same, (report.views cut.checkpoint.table.runs.length).visibleProjects _ _ _ stable.visibleBinding, stable.visibleBytes, stored]

theorem filesAtBarrier (report : NativeCheckpointRunDirectoryError (image := image) state cut) (index : Nat)
    (within : index ≤ cut.checkpoint.table.runs.length) :
    report.files (report.atRun index) = state.files.image :=
  report.filesAtRun index within

/-- No manifest write has run. Neither of the two reported sync effects
can change the only selected pair and its existing WAL. -/
theorem filesAtReturn (report : NativeCheckpointRunDirectoryError (image := image) state cut) (valid : state.Valid) :
    (report.files report.after).directory.active = state.writer.target.pair ∧
    (report.files report.after).directory.crashImages = [state.writer.target.pair] ∧
    CheckpointWalView.ofFiles (report.files report.after) = CheckpointWalView.ofFiles state.files.image := by
  have pair : state.files.image.directory.active = state.writer.target.pair := valid.retained.resumed.ready.selected
  have prior : state.files.image.directory.crashImages = [state.writer.target.pair] := valid.retained.resumed.ready.settled
  have atBarrier := report.filesAtRun _ (Nat.le_refl _)
  refine ⟨?_, ?_, report.walFrame.trans (congrArg CheckpointWalView.ofFiles atBarrier)⟩
  all_goals rw [report.directoryEffect, atBarrier]
  all_goals cases cut.tookEffect <;> simp only [Bool.false_eq_true, ite_false, ite_true, DirectoryPublication.Image.syncDirectory, pair, prior]

/-- The original canonical manifest inode and bytes remain at the same
path. In the no-checkpoint case the path stays absent. -/
theorem manifestAtReturn (report : NativeCheckpointRunDirectoryError (image := image) state cut) (valid : state.Valid) :
    match (report.files report.after).directory.active.manifest with
    | none => report.bindingsAfter (state.session.directory.file .manifest) = none
    | some bytes => ∃ inode, report.bindingsAfter (state.session.directory.file .manifest) = some inode ∧
        (report.inodes report.after).visible inode = bytes ∧ (report.inodes report.after).crashBytes inode = [bytes] := by
  have entry : state.files.image.directory.active = state.writer.target.pair := valid.retained.resumed.ready.selected
  rw [(report.filesAtReturn valid).1, ← entry]
  have existed := report.manifestAtEnd
  rw [report.visibleNames]
  cases manifest : state.files.image.directory.active.manifest with
  | none =>
    rw [manifest] at existed
    exact existed
  | some bytes =>
    rw [manifest] at existed
    obtain ⟨inode, _, same⟩ := existed
    exact ⟨inode, same.visibleBinding, report.inodeBytes.symm ▸ same.visibleBytes, report.inodeBytes.symm ▸ same.crashBytes⟩

theorem selectedCheckpoint (report : NativeCheckpointRunDirectoryError (image := image) state cut) (valid : state.Valid) :
    SelectedIntegrityCheckpoint (report.runs report.after).guaranteed (report.files report.after).directory.active.manifest
      state.writer.checkpoint := by
  have pair := (report.filesAtReturn valid).1
  rw [pair, ← valid.retained.walPair]
  exact SelectedIntegrityCheckpoint.withRunMap (valid.retained.walPair.symm ▸ valid.retained.resumed.selected)
    (report.priorRuns valid).symm

end NativeCheckpointRunDirectoryError
/-- A checkpoint can fail at its first directory sync without
replacing the selected manifest. The exact poisoned endpoint explains
all earlier recorded reads before any close or reopen is observed. -/
structure NativeReturnedCheckpointRunDirectoryError {image : Type} (current : NativeReadPosition history log)
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    (report : NativeCheckpointRunDirectoryError (image := image) current.state cut) : Prop where
  issued : CheckpointIssue report.perform current.state.session.phase report.entry cut.checkpoint.prepared
    cut.checkpoint.manifest cut.completed .syncRunsDirectory (current.state.cache, report.atBarrier)
  returned : runCheckpointWithEffects report.perform (current.state.session.phase, report.entry) =
    .error report.error (.poisoned, ⟨(current.state.cache, report.after), current.state.files.owners⟩)
  held : current.state.files.owners.Owns current.state.session.directory current.state.session.descriptor
  census : report.descriptors report.after = current.state.census
  directoryLive : current.state.directorySlot ∈ (report.descriptors report.after).slots
  lockLive : current.state.owner ∈ (report.descriptors report.after).slots
  directoryObject : report.bindingsAfter current.state.session.directory.path =
    some (report.handle.1.inode current.state.directorySlot.description)
  lockObject : report.bindingsAfter (current.state.session.directory.file .lock) =
    some (current.state.census.inode current.state.owner.description)
  visiblePair : (report.files report.after).directory.active = current.state.writer.target.pair
  crashPairs : (report.files report.after).directory.crashImages = [current.state.writer.target.pair]
  wal : CheckpointWalView.ofFiles (report.files report.after) = CheckpointWalView.ofFiles current.state.files.image
  checkpoint : SelectedIntegrityCheckpoint (report.runs report.after).guaranteed
    (report.files report.after).directory.active.manifest current.state.writer.checkpoint
  replay : PendingClientReplay log current.reads history
  bounded : ∀ read ∈ current.reads, read.BoundedBy history.length

theorem NativeReadPosition.checkpointRunDirectoryError {image : Type} (current : NativeReadPosition history log)
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    (report : NativeCheckpointRunDirectoryError (image := image) current.state cut) :
    NativeReturnedCheckpointRunDirectoryError current report := by
  obtain ⟨valid, _, replay⟩ := current.readPrefix.refines
  obtain ⟨census, directoryLive, lockLive, directory, lock⟩ := report.custody valid
  obtain ⟨visible, survives, wal⟩ := report.filesAtReturn valid
  exact ⟨report.issues valid, report.returns valid, valid.retained.held, census, directoryLive, lockLive,
    directory, lock, visible, survives, wal, report.selectedCheckpoint valid, replay, current.readPrefix.readsBounded⟩

end Alvoki.Storage.DiskSession
