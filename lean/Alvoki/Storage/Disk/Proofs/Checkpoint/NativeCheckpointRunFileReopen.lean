import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointRunFileError
import Alvoki.Storage.Disk.Proofs.Native.Execution.NativeExecutionClose

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

def NativeCheckpointRunFileError.closeState {image : Type} {state : NativeReadyState}
    {cut : CheckpointPowerCut state.session.directory state.writer}
    (report : NativeCheckpointRunFileError (image := image) state cut) :
    CachedCloseState CheckpointOpenHandle image :=
  ⟨.poisoned, ⟨(state.cache, report.after), state.files.owners⟩, report.prior.descriptors report.after⟩

/-- Close starts from the returned run sync error. The reread contract uses
the raw bindings and inode contents at that error, before any manifest
operation could publish the attempted checkpoint. -/
structure NativeCheckpointRunFileReopenObservation (state : NativeReadyState) (input : FilePath) where
  image : Type
  cut : CheckpointPowerCut state.session.directory state.writer
  error : NativeCheckpointRunFileError (image := image) state cut
  close : CachedCloseReports state.session.directory state.session.descriptor error.closeState
  owner : close.slot = state.owner
  unlocked : close.result = .ok ()
  closeBindings : close.bindings = error.view.visible
  files : NativeCloseFiles state
  reachedNames : files.names = error.view.visible
  reachedBytes : ∀ inode payload, files.bytes inode = some payload → (error.prior.inodes error.after).visible inode = payload
  observe : ∀ plan : ClosedReadyReopenLayout state.writer state.releasedFiles,
    ∀ selected : SelectedIntegrityCheckpoint state.writer.published.durable
      state.releasedFiles.image.directory.active.manifest state.writer.checkpoint,
      Nonempty (NativeCloseAlignedReads files input close.finished.descriptors plan.layout selected)

structure NativeCheckpointRunFileReopened (current : NativeReadPosition history log) {input : FilePath}
    (seen : NativeCheckpointRunFileReopenObservation current.state input)
    (next : NativeReadPosition history log) : Prop where
  failed : NativeReturnedCheckpointRunFileError current seen.error
  closed : seen.close.run = .ok () seen.close.finished ∧ seen.close.finished.phase = .closed ∧
    seen.close.finished.files = ⟨(⟨none, none, []⟩, seen.error.after), current.state.releasedFiles.owners⟩ ∧
    seen.close.finished.descriptors = current.state.census.afterDrops
      (seen.close.drops .active ++ seen.close.drops .pending ++ seen.close.drops .directory) ∧
    seen.close.bindings (current.state.session.directory.file .lock) =
      some (current.state.census.inode current.state.owner.description)
  released : (⟨seen.error.prior.files seen.close.finished.files.image.2, seen.close.finished.files.owners⟩ :
    LockedFileState FileImage) = current.state.releasedFiles
  reads : next.reads = current.reads
  frame : NativeReadRecoveryFrame current.state next.state
  sessionFresh : next.state.session.sessionRef ≠ current.state.session.sessionRef
  phaseFresh : next.state.session.phaseRef ≠ current.state.session.phaseRef
  exactOpen : ∃ (plan : ClosedReadyReopenLayout current.state.writer current.state.releasedFiles)
    (selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
      current.state.releasedFiles.image.directory.active.manifest current.state.writer.checkpoint)
    (observed : NativeCloseAlignedReads seen.files input seen.close.finished.descriptors plan.layout selected),
    next.opened = observed.run ∧ next.opened = .ok next.state.session (next.state.census, next.state.files) ∧
    next.initial = next.state ∧ next.state.owner = observed.opening.admission.owner ∧
    next.state.directorySlot = observed.opening.admission.cached ∧ next.state.cache = observed.opening.admission.cache ∧
    next.state.census = observed.opening.finish.census ∧ NativeCloseSelectedReads observed ∧
    (current.state.writer.target.pair.manifest = none →
      seen.error.view.visible (current.state.session.directory.file .manifest) = none) ∧
    ∀ path payload, observed.ReadsOriginal path payload →
      ∃ read : observed.opening.reads.reads.ObservesFile path payload,
        seen.error.view.visible path = some read.object ∧
          (seen.error.prior.inodes seen.error.after).visible read.object = payload
  replay : InstalledClientReplay log current.reads history next.state.writer.installed next.state.session

/-- The next admission uses the reached close, rereads the old manifest
and each file it selected, and installs the same committed replay. -/
theorem NativeReadPosition.recoversCheckpointRunFileError (current : NativeReadPosition history log) {input : FilePath}
    (seen : NativeCheckpointRunFileReopenObservation current.state input) :
    ∃ next, NativeCheckpointRunFileReopened current seen next := by
  have failed := current.checkpointRunFileError seen.error
  have closed := seen.close.outcome rfl
  rw [seen.unlocked] at closed
  have cleared := seen.close.finishedFiles failed.held
  have census := seen.close.finishedDescriptors
  change seen.close.finished.descriptors = (seen.error.prior.descriptors seen.error.after).afterDrops _ at census
  rw [failed.census] at census
  have lock := (congrFun seen.closeBindings (current.state.session.directory.file .lock)).trans failed.lockObject
  have released : (⟨seen.error.prior.files seen.close.finished.files.image.2, seen.close.finished.files.owners⟩ :
      LockedFileState FileImage) = current.state.releasedFiles := by
    rw [cleared]
    change (⟨seen.error.prior.files seen.error.after, _⟩ : LockedFileState FileImage) = _
    rw [failed.files]
    rfl
  obtain ⟨plan, selected, observed, state, seed, directory, owner, directorySlot, cache, finalCensus, sessionFresh,
    phaseFresh, lockObject, directoryObject, _, _, target, checkpoint, durable, missing, manifest, runs, marker, wal, replay⟩ :=
    current.readPrefix.reopensReleasedAligned seen.files seen.observe
  let next : NativeReadPosition history log := ⟨observed.run, state, state, current.reads, seed⟩
  refine ⟨next, failed, ⟨closed, rfl, cleared, census, lock⟩, released, rfl,
    ⟨directory, directoryObject, lockObject, target, checkpoint, durable⟩, sessionFresh, phaseFresh,
    ⟨plan, selected, observed, rfl, seed.frames.1, rfl, owner, directorySlot, cache, finalCensus,
      ⟨missing, manifest, runs, marker, wal⟩, ?_, ?_⟩, replay⟩
  · intro absent
    exact (congrFun seen.reachedNames _).symm.trans (missing absent).1
  · intro path payload selectedRead
    obtain ⟨read, bound, bytes⟩ := selectedRead
    exact ⟨read, (congrFun seen.reachedNames path).symm.trans bound, seen.reachedBytes _ _ bytes⟩

end Alvoki.Storage.DiskSession
