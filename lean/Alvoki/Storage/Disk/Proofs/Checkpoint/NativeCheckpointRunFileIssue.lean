import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointRunDirectoryError
import Alvoki.Storage.Disk.Proofs.Checkpoint.CheckpointRunFileSyncFailure

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair

/-- The guarded and flushed run is pending on its exact open slot.
This prefix is shared by an ordinary sync return and an outer stop. -/
structure NativeCheckpointRunFileIssue {image : Type} (state : NativeReadyState)
    (cut : CheckpointPowerCut state.session.directory state.writer) where
  index : Nat
  within : index < cut.checkpoint.table.runs.length
  prior : NativeCheckpointRunObservations (image := image) state cut index
  completed : cut.completed = runSteps index ++ [.writeRun index]
  run : Compaction.CheckedRun
  selected : cut.checkpoint.table.runs.toArray[index]? = some run
  handle : CheckpointOpenHandle
  guard : AcceptedRunGuard prior.primitives.lookup (state.session.directory.file (.run cut.checkpoint.prepared.generation index))
    (prior.atRun index)
  opened : image
  buffered : image
  flushed : image
  openReturned : prior.primitives.openRun (state.session.directory.file (.run cut.checkpoint.prepared.generation index))
    (prior.atRun index) = .ok handle opened
  writeReturned : prior.primitives.write handle run.run.bytes opened = .ok () buffered
  flushReturned : prior.primitives.flush handle buffered = .ok () flushed
  free : ∀ old ∈ (prior.descriptors (prior.atRun index)).slots, old.address ≠ handle.2.1.address
  fresh : (prior.descriptors (prior.atRun index)).references handle.2.1.description = []
  allocated : handle.1 = (prior.descriptors (prior.atRun index)).insert handle.2.1 free
  afterOpen : prior.descriptors opened = handle.1
  atFileSync : prior.descriptors flushed = handle.1
  links : RunOpenLinkCensus
    (path := state.session.directory.file (.run cut.checkpoint.prepared.generation index))
    (before := prior.atRun index) prior.primitives.lookup (prior.views index).visible (handle.1.inode handle.2.1.description)
  issueBindings : FilePath → Option Nat
  issuingFile : issueBindings (state.session.directory.file (.run cut.checkpoint.prepared.generation index)) =
    some (handle.1.inode handle.2.1.description)
  directoryAtIssue : issueBindings state.session.directory.path = some (state.census.inode state.directorySlot.description)
  lockAtIssue : issueBindings (state.session.directory.file .lock) = some (state.census.inode state.owner.description)
  written : (prior.inodes flushed).visible (handle.1.inode handle.2.1.description) = run.run.bytes

/-- The reached file effect preserves the private run's identity and
frames other selected files. The caller reports descriptor behavior
separately for a returned result or for a stopped operation. -/
structure NativeCheckpointRunFileEffect {image : Type} (state : NativeReadyState)
    (cut : CheckpointPowerCut state.session.directory state.writer)
    extends NativeCheckpointRunFileIssue (image := image) state cut where
  after : image
  fileEffect : prior.inodes after = if cut.tookEffect then
    (prior.inodes flushed).completeFileSync (handle.1.inode handle.2.1.description) else prior.inodes flushed
  view : RunDirectoryInodeView state.session.directory (prior.inodes after) (prior.runs after)
  sameNames : view.visible = issueBindings
  frame : RunWriteInodeFrame (state.session.directory.file (.run cut.checkpoint.prepared.generation index))
    (handle.1.inode handle.2.1.description) (prior.inodes flushed) (prior.views index) view
  walAndPair : prior.files after = prior.files (prior.atRun index)

namespace NativeCheckpointRunFileIssue

variable {image : Type} {state : NativeReadyState} {cut : CheckpointPowerCut state.session.directory state.writer}

abbrev path (report : NativeCheckpointRunFileIssue (image := image) state cut) : FilePath :=
  state.session.directory.file (.run cut.checkpoint.prepared.generation report.index)

def atIssue (report : NativeCheckpointRunFileIssue (image := image) state cut) : CensusDirectoryCache × image :=
  (state.cache.remember report.path report.handle, report.flushed)

theorem current (report : NativeCheckpointRunFileIssue (image := image) state cut) : cut.current = .syncRun report.index := by
  obtain ⟨_, paired⟩ := steps_atRunPair report.within
  have ordered := cut.schedule
  rw [report.completed, paired] at ordered
  simp only [List.append_assoc, List.cons_append, List.nil_append] at ordered
  exact (List.cons.inj (List.cons.inj (List.append_cancel_left ordered)).2).1.symm

theorem reachedWrite (report : NativeCheckpointRunFileIssue (image := image) state cut) :
    report.prior.perform cut.checkpoint.prepared cut.checkpoint.manifest (.writeRun report.index)
      (state.cache, report.prior.atRun report.index) = .ok () report.atIssue :=
  report.prior.primitives.remembersRun state.session.directory cut.checkpoint.prepared cut.checkpoint.manifest report.selected
    state.cache report.guard report.openReturned report.writeReturned report.flushReturned

theorem runPrefix (report : NativeCheckpointRunFileIssue (image := image) state cut) :
    (cut.completed.forM (report.prior.perform cut.checkpoint.prepared cut.checkpoint.manifest)) report.prior.entry.image =
      .ok () report.atIssue := by
  rw [report.completed, List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM]
  simp only [Bind.bind, EStateM.bind, report.prior.runPrefix, List.forM_eq_forM, List.forM_cons,
    report.reachedWrite, List.forM_nil, Pure.pure, EStateM.pure]

/-- The exact pending handle installed by the flushed run is at the
next scheduled operation after preflight and the returned run prefix. -/
theorem issues (report : NativeCheckpointRunFileIssue (image := image) state cut) (valid : state.Valid) :
    CheckpointIssue report.prior.perform state.session.phase report.prior.entry cut.checkpoint.prepared cut.checkpoint.manifest
      cut.completed (.syncRun report.index) report.atIssue := by
  have scheduled := cut.schedule
  rw [report.current] at scheduled
  rw [valid.phase]
  exact cut.preflight.reachesIssue report.prior.perform report.prior.entry scheduled report.runPrefix

end NativeCheckpointRunFileIssue

namespace NativeCheckpointRunFileEffect

variable {image : Type} {state : NativeReadyState} {cut : CheckpointPowerCut state.session.directory state.writer}

abbrev path (report : NativeCheckpointRunFileEffect (image := image) state cut) : FilePath :=
  report.toNativeCheckpointRunFileIssue.path

/-- The run bytes are already visible, but their inode acquires the
new durable bytes only when the reported file sync takes effect. No
claim about durable publication of its new directory name is needed. -/
theorem runBytes (report : NativeCheckpointRunFileEffect (image := image) state cut) :
    let inode := report.handle.1.inode report.handle.2.1.description
    report.view.visible report.path = some inode ∧
    (report.prior.runs report.after).visible cut.checkpoint.prepared.generation report.index = some report.run.run.bytes ∧
    (report.prior.inodes report.after).crashBytes inode = (if cut.tookEffect then [report.run.run.bytes]
      else (report.prior.inodes report.flushed).crashBytes inode) := by
  intro inode
  have bound : report.view.visible report.path = some inode := by rw [report.sameNames]; exact report.issuingFile
  refine ⟨bound, ?_, ?_⟩
  · rw [report.view.visibleProjects _ _ _ bound, report.fileEffect]
    cases cut.tookEffect <;> exact congrArg some report.written
  · rw [report.fileEffect]
    cases cut.tookEffect <;> simp [WAL.Boundary.WalInodeImage.completeFileSync, WAL.Boundary.WalInodeImage.reportFileSync,
      inode, report.written]

theorem stableAfter (report : NativeCheckpointRunFileEffect (image := image) state cut) {path : FilePath}
    {inode : Nat} {bytes : ByteArray} (different : path ≠ report.path)
    (stable : (report.prior.views report.index).Stable path inode bytes) : report.view.Stable path inode bytes :=
  report.frame.keepsStableOnSyncError report.fileEffect (report.links.privateBinding report.guard) different stable

theorem priorRunBytes (report : NativeCheckpointRunFileEffect (image := image) state cut) (valid : state.Valid)
    {bytes payload : ByteArray} {metadata : Manifest.IntegrityCheckpoint} {index : Nat}
    (binding : state.writer.wal.directory.active.manifest = some bytes)
    (decoded : Manifest.IntegrityCheckpoint.decode bytes = .ok metadata) (within : index < metadata.header.runCount.toNat)
    (stored : state.writer.published.durable metadata.header.generation index = some payload) :
    ∃ inode, (report.prior.views 0).Stable (state.session.directory.file (.run metadata.header.generation index)) inode payload ∧
      report.view.Stable (state.session.directory.file (.run metadata.header.generation index)) inode payload :=
  report.prior.priorRunAfter valid report.stableAfter binding decoded within stored

theorem filesAtEffect (report : NativeCheckpointRunFileEffect (image := image) state cut) :
    report.prior.files report.after = state.files.image :=
  report.walAndPair.trans (report.prior.filesAtRun report.index (Nat.le_refl _))

theorem manifestAtEffect (report : NativeCheckpointRunFileEffect (image := image) state cut) :
    match (report.prior.files report.after).directory.active.manifest with
    | none => report.view.visible (state.session.directory.file .manifest) = none
    | some bytes => ∃ inode, (report.prior.views 0).Stable (state.session.directory.file .manifest) inode bytes ∧
        report.view.Stable (state.session.directory.file .manifest) inode bytes := by
  rw [report.filesAtEffect]
  exact report.prior.manifestAfter report.frame.visibleNames report.stableAfter

theorem selectedCheckpoint (report : NativeCheckpointRunFileEffect (image := image) state cut) (valid : state.Valid) :
    SelectedIntegrityCheckpoint (report.prior.runs report.after).guaranteed
      (report.prior.files report.after).directory.active.manifest state.writer.checkpoint :=
  report.prior.selectedAfter valid report.stableAfter report.filesAtEffect

end NativeCheckpointRunFileEffect

end Alvoki.Storage.DiskSession
