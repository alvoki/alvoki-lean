import Alvoki.Storage.Disk.NativeCheckpointManifestSyncError
import Alvoki.Storage.Disk.CheckpointManifestRenameCut

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

private theorem fixedNameNeStage (directory : DiskDirectory) {file : DiskFile}
    (fixed : file = .lock ∨ file = .manifest) : directory.file file ≠ directory.file .stagedManifest := by
  intro equal
  rcases fixed with rfl | rfl <;>
    have names := (String.append_right_inj (directory.path.toString ++ "/")).mp (congrArg FilePath.toString equal)
    <;> contradiction

/-- The reported exclusive staging, file sync and exact release of its
temporary descriptor. It reaches the original cache at the rename. -/
structure NativeCheckpointManifestSynced {image : Type} (state : NativeReadyState)
    (cut : CheckpointPowerCut state.session.directory state.writer) where
  settled : NativeCheckpointRunsSynced (image := image) state cut
  handle : CheckpointOpenHandle
  opened : image
  buffered : image
  flushed : image
  after : image
  opening : settled.runs.primitives.StageOpened (state.session.directory.file .stagedManifest) settled.after handle opened
  wrote : settled.runs.primitives.write handle cut.checkpoint.manifest opened = .ok () buffered
  flushedBytes : settled.runs.primitives.flush handle buffered = .ok () flushed
  synced : settled.runs.primitives.fsync handle flushed = .ok () after
  free : ∀ old ∈ (settled.runs.descriptors settled.after).slots, old.address ≠ handle.2.1.address
  fresh : (settled.runs.descriptors settled.after).references handle.2.1.description = []
  allocated : handle.1 = (settled.runs.descriptors settled.after).insert handle.2.1 free
  atSync : settled.runs.descriptors flushed = handle.1
  afterClose : settled.runs.descriptors after = handle.1.afterDrops [handle.2.1.closeEvent]
  fileEffect : settled.runs.inodes after =
    (settled.runs.inodes flushed).completeFileSync (handle.1.inode handle.2.1.description)
  written : (settled.runs.inodes flushed).visible (handle.1.inode handle.2.1.description) = cut.checkpoint.manifest
  view : RunDirectoryInodeView state.session.directory (settled.runs.inodes after) (settled.runs.runs after)
  stageBinding : view.visible (state.session.directory.file .stagedManifest) = some (handle.1.inode handle.2.1.description)
  privateInode : ∀ other, settled.view.visible other = some (handle.1.inode handle.2.1.description) →
    other = state.session.directory.file .stagedManifest
  frame : RunWriteInodeFrame (state.session.directory.file .stagedManifest)
    (handle.1.inode handle.2.1.description) (settled.runs.inodes flushed) settled.view view
  wal : CheckpointWalView.ofFiles (settled.runs.files after) = CheckpointWalView.ofFiles (settled.runs.files settled.after)

namespace NativeCheckpointManifestSynced

variable {image : Type} {state : NativeReadyState} {cut : CheckpointPowerCut state.session.directory state.writer}

abbrev inode (seen : NativeCheckpointManifestSynced (image := image) state cut) : Nat :=
  seen.handle.1.inode seen.handle.2.1.description

abbrev prior (seen : NativeCheckpointManifestSynced (image := image) state cut) : Option Nat :=
  seen.view.visible (state.session.directory.file .manifest)

noncomputable def stagePair (seen : NativeCheckpointManifestSynced (image := image) state cut) :
    CompletedCheckpointTemporaryFile seen.settled.runs.descriptors seen.settled.runs.primitives.cached
      seen.settled.runs.primitives.cached.writeStaged (state.session.directory.file .stagedManifest)
      cut.checkpoint.manifest seen.settled.after seen.after where
  handle := seen.handle
  flushed := seen.flushed
  wrote := seen.settled.runs.primitives.wroteStage seen.opening seen.wrote seen.flushedBytes
  synced := seen.synced
  free := seen.free
  fresh := seen.fresh
  allocated := seen.allocated
  atFileSync := seen.atSync
  drop := seen.handle.2.1.closeEvent
  close := rfl
  afterClose := seen.atSync.symm ▸ seen.afterClose

theorem stageReturns (seen : NativeCheckpointManifestSynced (image := image) state cut) :
    ((seen.settled.runs.perform cut.checkpoint.prepared cut.checkpoint.manifest (.manifest .writeStaged) >>= fun _ =>
      seen.settled.runs.perform cut.checkpoint.prepared cut.checkpoint.manifest (.manifest .syncStaged))
      (state.cache, seen.settled.after)) = .ok () (state.cache, seen.after) :=
  seen.stagePair.returns state.session.directory (file_ne_directory _ .stagedManifest) state.cache seen.settled.runs.pending

theorem keepsCensus (seen : NativeCheckpointManifestSynced (image := image) state cut) :
    seen.settled.runs.descriptors seen.after = state.census ∧
    seen.handle.2.1 ∈ (seen.settled.runs.descriptors seen.flushed).slots ∧
    (seen.settled.runs.descriptors seen.after).references seen.handle.2.1.description = [] := by
  obtain ⟨census, live, closed⟩ := seen.stagePair.keepsCensus
  exact ⟨census.trans seen.settled.keepsCensus, live, closed⟩

theorem returns (seen : NativeCheckpointManifestSynced (image := image) state cut) :
    ((runSteps cut.checkpoint.table.runs.length ++ [CheckpointPublication.Step.syncRunsDirectory, .manifest .writeStaged, .manifest .syncStaged]).forM
      (seen.settled.runs.perform cut.checkpoint.prepared cut.checkpoint.manifest)) seen.settled.runs.entry.image =
      .ok () (state.cache, seen.after) := by
  have order : runSteps cut.checkpoint.table.runs.length ++ [CheckpointPublication.Step.syncRunsDirectory, .manifest .writeStaged, .manifest .syncStaged] =
      (runSteps cut.checkpoint.table.runs.length ++ [CheckpointPublication.Step.syncRunsDirectory]) ++ [.manifest .writeStaged, .manifest .syncStaged] := by
    rw [List.append_assoc]
    rfl
  rw [order, List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM]
  simp only [Bind.bind, EStateM.bind, seen.settled.runPrefix]
  have pair := seen.stageReturns
  simp only [Bind.bind, EStateM.bind] at pair
  simp only [List.forM_eq_forM, List.forM_cons, List.forM_nil, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  split <;> simp_all

theorem stagedBytes (seen : NativeCheckpointManifestSynced (image := image) state cut) :
    (seen.settled.runs.inodes seen.after).visible seen.inode = cut.checkpoint.manifest ∧
    (seen.settled.runs.inodes seen.after).crashBytes seen.inode = [cut.checkpoint.manifest] := by
  rw [seen.fileEffect]
  simp [inode, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, seen.written]

theorem retainsPath (seen : NativeCheckpointManifestSynced (image := image) state cut)
    {path : FilePath} {inode : Nat} {bytes : ByteArray} (other : path ≠ state.session.directory.file .stagedManifest)
    (known : seen.settled.view.Stable path inode bytes) : seen.view.Stable path inode bytes :=
  seen.frame.keepsStable seen.fileEffect seen.privateInode other known

theorem priorManifest (seen : NativeCheckpointManifestSynced (image := image) state cut) (valid : state.Valid) :
    seen.prior.map (seen.settled.runs.inodes seen.after).visible = state.writer.wal.directory.active.manifest ∧
    manifestCrashBytes (seen.settled.runs.inodes seen.after) seen.prior = [state.writer.wal.directory.active.manifest] ∧
    seen.prior ≠ some seen.inode := by
  have pair : state.files.image.directory.active = state.writer.wal.directory.active := valid.retained.directoryFiles ▸ rfl
  have selected := congrArg DirectoryPublication.Bindings.manifest pair
  rw [← selected]
  have manifest := seen.settled.runs.manifestAtEnd
  have other := fixedNameNeStage state.session.directory (.inr rfl)
  cases binding : state.files.image.directory.active.manifest with
  | none =>
    rw [binding] at manifest
    have absent : seen.prior = none :=
      (seen.frame.visibleNames _ other).trans ((seen.settled.sameNames .manifest).trans manifest)
    simp [absent, manifestCrashBytes]
  | some payload =>
    rw [binding] at manifest
    obtain ⟨inode, _, kept⟩ := manifest
    have directory := seen.settled.stableAfter kept.visibleBinding kept.visibleBytes kept.crashBytes
    have stable := seen.retainsPath other directory
    have different : inode ≠ seen.inode := by
      intro same
      apply other
      apply seen.privateInode
      change seen.settled.view.visible (state.session.directory.file .manifest) = some seen.inode
      rw [← same]
      exact directory.visibleBinding
    have named : seen.prior = some inode := stable.visibleBinding
    simp [named, manifestCrashBytes, stable.visibleBytes, stable.crashBytes, different]

end NativeCheckpointManifestSynced

/-- The actual rename returns its original cause from the closed-stage
prefix. The joint post-error report follows the inode of that stage
across the atomic name effect and preserves all selected run bytes. -/
structure NativeCheckpointManifestRenameError {image : Type} (state : NativeReadyState)
    (cut : CheckpointPowerCut state.session.directory state.writer) where
  synced : NativeCheckpointManifestSynced (image := image) state cut
  completed : cut.completed = runSteps cut.checkpoint.table.runs.length ++
    [CheckpointPublication.Step.syncRunsDirectory, .manifest .writeStaged, .manifest .syncStaged]
  cause : IO.Error
  after : image
  failed : synced.settled.runs.primitives.rename (state.session.directory.file .stagedManifest)
    (state.session.directory.file .manifest) synced.after = .error cause after
  descriptors : synced.settled.runs.descriptors after = synced.settled.runs.descriptors synced.after
  inodes : synced.settled.runs.inodes after = synced.settled.runs.inodes synced.after
  view : RunDirectoryInodeView state.session.directory (synced.settled.runs.inodes after) (synced.settled.runs.runs after)
  retained : ∀ path, path ≠ state.session.directory.file .stagedManifest → path ≠ state.session.directory.file .manifest →
    view.visible path = synced.view.visible path
  surviveOther : ∀ names ∈ view.crashBindings, ∃ previousNames ∈ synced.view.crashBindings, ∀ path,
    path ≠ state.session.directory.file .stagedManifest → path ≠ state.session.directory.file .manifest →
    names path = previousNames path
  live : view.visible (state.session.directory.file .manifest) = if cut.tookEffect then some synced.inode else synced.prior
  stage : view.visible (state.session.directory.file .stagedManifest) = if cut.tookEffect then none else some synced.inode
  survive : ∀ names ∈ view.crashBindings,
    names (state.session.directory.file .manifest) = synced.prior ∨
      (cut.tookEffect = true ∧ names (state.session.directory.file .manifest) = some synced.inode)
  liveFile : (synced.settled.runs.files after).directory.active.manifest =
    (view.visible (state.session.directory.file .manifest)).map (synced.settled.runs.inodes after).visible
  crashFiles : ∀ pair ∈ (synced.settled.runs.files after).directory.crashImages,
    ∃ names ∈ view.crashBindings, pair.manifest ∈
      manifestCrashBytes (synced.settled.runs.inodes after) (names (state.session.directory.file .manifest))
  crashMarker : ∀ pair ∈ (synced.settled.runs.files after).directory.crashImages,
    pair.walBoundary = state.writer.wal.directory.active.walBoundary
  wal : CheckpointWalView.ofFiles (synced.settled.runs.files after) =
    CheckpointWalView.ofFiles (synced.settled.runs.files synced.after)

namespace NativeCheckpointManifestRenameError

variable {image : Type} {state : NativeReadyState} {cut : CheckpointPowerCut state.session.directory state.writer}

def atIssue (report : NativeCheckpointManifestRenameError (image := image) state cut) : CensusDirectoryCache × image :=
  (state.cache, report.synced.after)

theorem current (report : NativeCheckpointManifestRenameError (image := image) state cut) :
    cut.current = .manifest .renameStaged := by
  have order := cut.schedule
  rw [report.completed] at order
  simp only [CheckpointPublication.steps, Publication.steps, List.map_cons, List.map_nil, List.append_assoc,
    List.cons_append, List.nil_append] at order
  have suffix := List.append_cancel_left order
  exact Option.some.inj (congrArg (fun remaining : List CheckpointPublication.Step => remaining[3]?) suffix).symm

theorem issues (report : NativeCheckpointManifestRenameError (image := image) state cut) (valid : state.Valid) :
    CheckpointIssue report.synced.settled.runs.perform state.session.phase report.synced.settled.runs.entry
      cut.checkpoint.prepared cut.checkpoint.manifest cut.completed (.manifest .renameStaged) report.atIssue := by
  have scheduled := cut.schedule
  rw [report.current] at scheduled
  have completed := report.synced.returns
  rw [← report.completed] at completed
  rw [valid.phase]
  exact cut.preflight.reachesIssue report.synced.settled.runs.perform report.synced.settled.runs.entry scheduled completed

theorem callbackFails (report : NativeCheckpointManifestRenameError (image := image) state cut) :
    report.synced.settled.runs.perform cut.checkpoint.prepared cut.checkpoint.manifest (.manifest .renameStaged) report.atIssue =
      .error report.cause (state.cache, report.after) := by
  change withCache state.cache
    (report.synced.settled.runs.primitives.rename (state.session.directory.file .stagedManifest)
      (state.session.directory.file .manifest) report.synced.after) = _
  rw [report.failed]
  rfl

theorem returns (report : NativeCheckpointManifestRenameError (image := image) state cut) (valid : state.Valid) :
    runCheckpointWithEffects report.synced.settled.runs.perform (state.session.phase, report.synced.settled.runs.entry) =
      .error report.cause (.poisoned, ⟨(state.cache, report.after), state.files.owners⟩) := by
  obtain ⟨_, _, continued⟩ := (report.issues valid).continuation
  rw [continued, List.forM_eq_forM, List.forM_cons]
  simp only [Bind.bind, EStateM.bind, report.callbackFails, NativeCheckpointRunObservations.entry]

theorem liveManifest (report : NativeCheckpointManifestRenameError (image := image) state cut) (valid : state.Valid) :
    (report.synced.settled.runs.files report.after).directory.active.manifest =
      (if cut.tookEffect then some cut.checkpoint.manifest else state.writer.wal.directory.active.manifest) := by
  rw [report.liveFile, report.live, report.inodes]
  cases took : cut.tookEffect
  · exact (report.synced.priorManifest valid).1
  · exact congrArg some report.synced.stagedBytes.1

theorem crashSelection (report : NativeCheckpointManifestRenameError (image := image) state cut) (valid : state.Valid)
    {pair : DirectoryPublication.Bindings}
    (surviving : pair ∈ (report.synced.settled.runs.files report.after).directory.crashImages) :
    pair.walBoundary = state.writer.wal.directory.active.walBoundary ∧
      (pair.manifest = state.writer.wal.directory.active.manifest ∨
        (cut.tookEffect = true ∧ pair.manifest = some cut.checkpoint.manifest)) := by
  obtain ⟨names, member, payload⟩ := report.crashFiles pair surviving
  rw [report.inodes] at payload
  refine ⟨report.crashMarker pair surviving, ?_⟩
  rcases report.survive names member with prior | ⟨effect, replacement⟩
  · rw [prior, (report.synced.priorManifest valid).2.1] at payload
    exact .inl (List.mem_singleton.mp payload)
  · rw [replacement, manifestCrashBytes, report.synced.stagedBytes.2] at payload
    exact .inr ⟨effect, List.mem_singleton.mp payload⟩

/-- The rename changes only its two names. Protected run inodes keep
their exact bindings and payloads in the same reached crash views. -/
theorem retainsPath (report : NativeCheckpointManifestRenameError (image := image) state cut)
    {path : FilePath} {inode : Nat} {bytes : ByteArray}
    (outsideStage : path ≠ state.session.directory.file .stagedManifest)
    (outsideManifest : path ≠ state.session.directory.file .manifest)
    (known : report.synced.view.Stable path inode bytes) : report.view.Stable path inode bytes := by
  refine ⟨(report.retained path outsideStage outsideManifest).trans known.visibleBinding, ?_,
    report.inodes.symm ▸ known.visibleBytes, report.inodes.symm ▸ known.crashBytes⟩
  intro names member
  obtain ⟨previous, allowed, frames⟩ := report.surviveOther names member
  exact (frames path outsideStage outsideManifest).trans (known.crashBinding previous allowed)

theorem freshRunAtReturn (report : NativeCheckpointManifestRenameError (image := image) state cut)
    {index : Nat} (within : index < cut.checkpoint.table.runs.length) :
    ∃ run inode, cut.checkpoint.table.runs.toArray[index]? = some run ∧
      report.view.Stable (state.session.directory.file (.run cut.checkpoint.prepared.generation index)) inode run.run.bytes := by
  obtain ⟨run, inode, found, binding, visible, durable⟩ := report.synced.settled.runs.freshRunAtEnd within
  have stable := report.synced.retainsPath (runFile_ne_stagedManifest _ _ _) (report.synced.settled.stableAfter binding visible durable)
  exact ⟨run, inode, found, report.retainsPath (runFile_ne_stagedManifest _ _ _) (runFile_ne_manifest _ _ _) stable⟩

theorem freshRunMap (report : NativeCheckpointManifestRenameError (image := image) state cut)
    {index : Nat} (within : index < cut.checkpoint.table.runs.length) :
    (report.synced.settled.runs.runs report.after).guaranteed cut.checkpoint.prepared.generation index =
      cut.checkpoint.plan.files[index]? := by
  obtain ⟨run, _, found, stable⟩ := report.freshRunAtReturn within
  rw [stable.guaranteed]
  change some run.run.bytes = (cut.checkpoint.table.runs.map (·.run.bytes))[index]?
  rw [List.getElem?_map, ← List.getElem?_toArray, found]
  rfl

theorem priorRunAtReturn (report : NativeCheckpointManifestRenameError (image := image) state cut) (valid : state.Valid)
    {bytes payload : ByteArray} {metadata : Manifest.IntegrityCheckpoint} {index : Nat}
    (binding : state.writer.wal.directory.active.manifest = some bytes)
    (decoded : Manifest.IntegrityCheckpoint.decode bytes = .ok metadata)
    (within : index < metadata.header.runCount.toNat)
    (stored : state.writer.published.durable metadata.header.generation index = some payload) :
    ∃ inode, (report.synced.settled.runs.views 0).Stable (state.session.directory.file (.run metadata.header.generation index)) inode payload ∧
      report.view.Stable (state.session.directory.file (.run metadata.header.generation index)) inode payload := by
  obtain ⟨inode, initial, kept⟩ := report.synced.settled.runs.priorRunAtEnd valid binding decoded within stored
  have stable := report.synced.retainsPath (runFile_ne_stagedManifest _ _ _)
    (report.synced.settled.stableAfter kept.visibleBinding kept.visibleBytes kept.crashBytes)
  exact ⟨inode, initial, report.retainsPath (runFile_ne_stagedManifest _ _ _) (runFile_ne_manifest _ _ _) stable⟩

theorem retainsRunMap (report : NativeCheckpointManifestRenameError (image := image) state cut) (valid : state.Valid) :
    SelectedRunsAgree state.writer.wal.directory.active.manifest
      (report.synced.settled.runs.runs report.after).guaranteed state.writer.published.durable := by
  intro bytes metadata present decoded index within
  have selected := valid.retained.resumed.selected
  rw [← valid.retained.walPair] at selected
  obtain ⟨payload, stored⟩ := selected.runExists present decoded within
  obtain ⟨_, _, stable⟩ := report.priorRunAtReturn valid present decoded within stored
  exact stable.guaranteed.trans stored.symm

private theorem lockNeManifest (directory : DiskDirectory) : directory.file .lock ≠ directory.file .manifest := by
  intro equal
  have names := (String.append_right_inj (directory.path.toString ++ "/")).mp (congrArg FilePath.toString equal)
  contradiction

theorem custody (report : NativeCheckpointManifestRenameError (image := image) state cut) (valid : state.Valid) :
    report.synced.settled.runs.descriptors report.after = state.census ∧
    (report.synced.settled.runs.descriptors report.after).references report.synced.handle.2.1.description = [] ∧
    state.directorySlot ∈ (report.synced.settled.runs.descriptors report.after).slots ∧
    state.owner ∈ (report.synced.settled.runs.descriptors report.after).slots ∧
    report.view.visible state.session.directory.path =
      some (report.synced.settled.runs.captured.inode state.directorySlot.description) ∧
    report.view.visible (state.session.directory.file .lock) = some (state.census.inode state.owner.description) := by
  obtain ⟨restored, _, closed⟩ := report.synced.keepsCensus
  have census := report.descriptors.trans restored
  refine ⟨census, report.descriptors.symm ▸ closed, census.symm ▸ valid.directoryLive, census.symm ▸ valid.ownerLive, ?_, ?_⟩
  · have different := (file_ne_directory state.session.directory .stagedManifest).symm
    rw [report.retained _ different (file_ne_directory _ .manifest).symm, report.synced.frame.visibleNames _ different,
      report.synced.settled.sameDirectory]
    exact (report.synced.settled.directoryCustody valid).2.2.1
  · have different := fixedNameNeStage state.session.directory (.inl rfl)
    rw [report.retained _ different (lockNeManifest _), report.synced.frame.visibleNames _ different,
      report.synced.settled.sameNames .lock]
    exact report.synced.settled.lockAtIssue

theorem walAtReturn (report : NativeCheckpointManifestRenameError (image := image) state cut) (valid : state.Valid) :
    CheckpointWalView.ofFiles (report.synced.settled.runs.files report.after) = CheckpointWalView.ofFiles state.files.image :=
  report.wal.trans (report.synced.wal.trans (report.synced.settled.selectedPair valid).2.2)

theorem modeledPublication (report : NativeCheckpointManifestRenameError (image := image) state cut) (valid : state.Valid) :
    ∃ published, state.writer.published.executeVersioned cut.checkpoint.plan cut.checkpoint.cut = some published ∧
      published.manifest.crashImages = (if cut.tookEffect then
        [some cut.checkpoint.manifest, state.writer.wal.directory.active.manifest]
        else [state.writer.wal.directory.active.manifest]) ∧
      (∀ index, published.durable (SegmentedCheckpointReport.generation state.writer) index = cut.checkpoint.plan.files[index]?) ∧
      ∀ older, older ≠ SegmentedCheckpointReport.generation state.writer → ∀ index,
        published.durable older index = state.writer.published.durable older index := by
  let count := cut.checkpoint.table.runs.length
  have planCount : cut.checkpoint.plan.files.length = count := by
    simp [SegmentedCheckpointReport.plan, VersionedRunSet.integrity, count]
  have earlier : state.writer.published.manifest.crashImages = [state.writer.wal.directory.active.manifest] := by
    simp [valid.retained.manifestFiles, valid.retained.directoryFiles, DirectoryPublication.Image.project,
      DirectoryPublication.Bindings.get, valid.retained.walDirectorySettled]
  have reached : cut.checkpoint.cut = (runSteps count).length + 1 + (2 + if cut.tookEffect then 1 else 0) := by
    rw [cut.reachedCount.1, report.completed, List.length_append]
    simp [count] <;> omega
  obtain ⟨written, ran, same, durable, older⟩ := checkpoint_runs_complete state.writer.published cut.checkpoint.plan.runSet
  have executed := state.writer.published.executeVersioned_atManifestRename cut.checkpoint.plan written ran same planCount
    cut.plannedManifestBytes cut.tookEffect
  rw [← reached] at executed
  refine ⟨_, executed, ?_, durable, older⟩
  cases cut.tookEffect <;> simp [earlier]

/-- The selected exact run map and committed WAL explain the same
acknowledged history for every old or replacement manifest choice. -/
def Replays (report : NativeCheckpointManifestRenameError (image := image) state cut)
    (binding : Option ByteArray) (log : List DatabaseSubmissions) (reads : List RecordedSnapshotRead) : Prop :=
  ∃ checkpoint table model,
    SelectedIntegrityCheckpoint (report.synced.settled.runs.runs report.after).guaranteed binding checkpoint ∧
    (((checkpoint.getD (.empty, 0)).2 = state.writer.installed.generation ∧ binding = state.writer.wal.directory.active.manifest) ∨
      ((checkpoint.getD (.empty, 0)).2 = SegmentedCheckpointReport.generation state.writer ∧ binding = some cut.checkpoint.manifest)) ∧
    recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode state.writer.history) = .ok table ∧
    table.committed.toNat = state.writer.history.length ∧ table.Refines model ∧ RepresentsWalHistory state.writer.history model ∧
    PendingClientReplay log reads state.writer.history

theorem replaysChoice (report : NativeCheckpointManifestRenameError (image := image) state cut) (valid : state.Valid)
    (pending : PendingClientReplay log reads state.writer.history) {binding : Option ByteArray}
    (choice : binding = state.writer.wal.directory.active.manifest ∨
      (cut.tookEffect = true ∧ binding = some cut.checkpoint.manifest)) : report.Replays binding log reads := by
  obtain ⟨published, executed, choices, newRuns, oldRuns⟩ := report.modeledPublication valid
  obtain ⟨modeled, exactExecution, _, _, _, recovers⟩ := cut.selectsAcknowledgedHistory valid.retained
  have same := Option.some.inj (exactExecution.symm.trans executed)
  subst modeled
  let physical := (report.synced.settled.runs.runs report.after).guaranteed
  have old : SelectedRunsAgree state.writer.wal.directory.active.manifest physical published.durable := by
    intro bytes manifest present decoded index within
    have different := (cut.priorSelectedGeneration valid.retained present decoded).2
    exact (report.retainsRunMap valid bytes manifest present decoded index within).trans (oldRuns _ different _).symm
  have new : ∀ index < cut.checkpoint.table.runs.length,
      physical (SegmentedCheckpointReport.generation state.writer) index =
        published.durable (SegmentedCheckpointReport.generation state.writer) index := by
    intro index within
    exact (report.freshRunMap within).trans (newRuns index).symm
  have allowed : binding ∈ published.manifest.crashImages := by
    rw [choices]
    rcases choice with prior | ⟨effective, replacement⟩
    · cases cut.tookEffect <;> simp [prior]
    · simp [effective, replacement]
  let pair : DirectoryPublication.Bindings := ⟨binding, state.writer.wal.directory.active.walBoundary⟩
  have joint : pair ∈ (published.segmentedCheckpointView state.writer.wal).directory.crashImages :=
    List.mem_map.mpr ⟨binding, allowed, rfl⟩
  obtain ⟨_, _, _, _, _, _, _, checkpoint, table, model, chosen, generations, replay, bound, refines, represents⟩ := recovers joint
  have origin : binding = state.writer.wal.directory.active.manifest ∨ binding = some cut.checkpoint.manifest :=
    choice.imp id And.right
  have sameRuns := cut.selectedRunAgreement valid.retained published binding origin physical new old
  exact ⟨checkpoint, table, model, SelectedIntegrityCheckpoint.withRunMap chosen sameRuns.symm, generations,
    replay, bound, refines, represents, pending⟩

/-- The reached visible pair and all reported crash pairs have replay
witnesses even though the rename returned an error. -/
theorem replaysFiles (report : NativeCheckpointManifestRenameError (image := image) state cut) (valid : state.Valid)
    (pending : PendingClientReplay log reads state.writer.history) :
    let directory := (report.synced.settled.runs.files report.after).directory
    directory.active.walBoundary = state.writer.wal.directory.active.walBoundary ∧
    report.Replays directory.active.manifest log reads ∧
    ∀ pair ∈ directory.crashImages,
      pair.walBoundary = state.writer.wal.directory.active.walBoundary ∧ report.Replays pair.manifest log reads := by
  intro directory
  have marker := congrArg CheckpointWalView.marker (report.walAtReturn valid)
  have liveMarker : directory.active.walBoundary = state.writer.wal.directory.active.walBoundary :=
    marker.trans (congrArg DirectoryPublication.Bindings.walBoundary
      (congrArg DirectoryPublication.Image.active valid.retained.directoryFiles))
  refine ⟨liveMarker, report.replaysChoice valid pending ?_, ?_⟩
  · have visible := report.liveManifest valid
    cases took : cut.tookEffect
    · exact .inl (by simpa only [took, Bool.false_eq_true, ite_false] using visible)
    · exact .inr ⟨rfl, by simpa only [took, ite_true] using visible⟩
  · intro pair surviving
    obtain ⟨marker, choice⟩ := report.crashSelection valid surviving
    exact ⟨marker, report.replaysChoice valid pending choice⟩

end NativeCheckpointManifestRenameError

/-- The native rename error exposes the original response and reached
owner. Every exact visible or crash-selected pair retains client replay. -/
structure NativeReturnedCheckpointManifestRenameError {image : Type} (current : NativeReadPosition history log)
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    (report : NativeCheckpointManifestRenameError (image := image) current.state cut) : Prop where
  issued : CheckpointIssue report.synced.settled.runs.perform current.state.session.phase report.synced.settled.runs.entry
    cut.checkpoint.prepared cut.checkpoint.manifest cut.completed (.manifest .renameStaged) report.atIssue
  returned : runCheckpointWithEffects report.synced.settled.runs.perform
    (current.state.session.phase, report.synced.settled.runs.entry) =
      .error report.cause (.poisoned, ⟨(current.state.cache, report.after), current.state.files.owners⟩)
  held : current.state.files.owners.Owns current.state.session.directory current.state.session.descriptor
  census : report.synced.settled.runs.descriptors report.after = current.state.census
  closed : (report.synced.settled.runs.descriptors report.after).references report.synced.handle.2.1.description = []
  directoryLive : current.state.directorySlot ∈ (report.synced.settled.runs.descriptors report.after).slots
  lockLive : current.state.owner ∈ (report.synced.settled.runs.descriptors report.after).slots
  directoryObject : report.view.visible current.state.session.directory.path =
    some (report.synced.settled.runs.captured.inode current.state.directorySlot.description)
  lockObject : report.view.visible (current.state.session.directory.file .lock) =
    some (current.state.census.inode current.state.owner.description)
  wal : CheckpointWalView.ofFiles (report.synced.settled.runs.files report.after) = CheckpointWalView.ofFiles current.state.files.image
  live : report.Replays (report.synced.settled.runs.files report.after).directory.active.manifest log current.reads
  survivors : ∀ pair ∈ (report.synced.settled.runs.files report.after).directory.crashImages,
    pair.walBoundary = current.state.writer.wal.directory.active.walBoundary ∧ report.Replays pair.manifest log current.reads
  sameHistory : current.state.writer.history = history
  bounded : ∀ read ∈ current.reads, read.BoundedBy history.length

theorem NativeReadPosition.checkpointManifestRenameError {image : Type} (current : NativeReadPosition history log)
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    (report : NativeCheckpointManifestRenameError (image := image) current.state cut) :
    NativeReturnedCheckpointManifestRenameError current report := by
  obtain ⟨valid, sameHistory, replay⟩ := current.readPrefix.refines
  obtain ⟨census, closed, directoryLive, lockLive, root, lock⟩ := report.custody valid
  have pending : PendingClientReplay log current.reads current.state.writer.history := sameHistory.symm ▸ replay
  obtain ⟨_, live, survivors⟩ := report.replaysFiles valid pending
  exact ⟨report.issues valid, report.returns valid, valid.retained.held, census, closed, directoryLive,
    lockLive, root, lock, report.walAtReturn valid, live, survivors, sameHistory, current.readPrefix.readsBounded⟩

end Alvoki.Storage.DiskSession
