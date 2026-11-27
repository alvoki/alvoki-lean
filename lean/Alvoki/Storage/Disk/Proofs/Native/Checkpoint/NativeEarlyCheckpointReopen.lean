import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointRunDirectoryError
import Alvoki.Storage.Disk.Proofs.Native.Execution.NativeCloseAlignedReopen

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

namespace NativeCheckpointRunDirectoryError

variable {image : Type} {state : NativeReadyState} {cut : CheckpointPowerCut state.session.directory state.writer}

private theorem sameImage {before after : FileImage} (directory : after.directory = before.directory)
    (wal : CheckpointWalView.ofFiles after = CheckpointWalView.ofFiles before) : after = before := by
  cases before
  cases after
  simp only [CheckpointWalView.ofFiles, CheckpointWalView.mk.injEq, FileImage.mk.injEq] at *
  exact ⟨directory, wal.1, wal.2.1, wal.2.2.1⟩

private theorem settledDirectory (image : DirectoryPublication.Image)
    (settled : image.crashImages = [image.active]) : image.syncDirectory = image := by
  cases image
  simp only [DirectoryPublication.Image.syncDirectory, DirectoryPublication.Image.mk.injEq, true_and, and_true]
  exact settled.symm

/-- The first checkpoint directory sync can settle newly written run
names. It leaves the selected manifest/marker and WAL projection intact. -/
theorem sameFiles (report : NativeCheckpointRunDirectoryError (image := image) state cut) (valid : state.Valid) :
    report.files report.after = state.files.image := by
  have projected := report.filesAtReturn valid
  apply sameImage _ projected.2.2
  rw [report.directoryEffect, report.filesAtBarrier _ (Nat.le_refl _)]
  cases cut.tookEffect
  · rfl
  · have pair : state.files.image.directory.active = state.writer.target.pair := valid.retained.resumed.ready.selected
    have prior : state.files.image.directory.crashImages = [state.writer.target.pair] := valid.retained.resumed.ready.settled
    exact settledDirectory _ (prior.trans (congrArg (fun selected => [selected]) pair.symm))

def closeState (report : NativeCheckpointRunDirectoryError (image := image) state cut) :
    CachedCloseState CheckpointOpenHandle image :=
  ⟨.poisoned, ⟨(state.cache, report.after), state.files.owners⟩, report.descriptors report.after⟩

end NativeCheckpointRunDirectoryError

/-- An actual close starts at the first directory error's reported
poisoned return. The observations for the next aligned open use that
same reached namespace and the bytes of the selected files. -/
structure NativeEarlyCheckpointReopenObservation (state : NativeReadyState) (input : FilePath) where
  image : Type
  cut : CheckpointPowerCut state.session.directory state.writer
  error : NativeCheckpointRunDirectoryError (image := image) state cut
  close : CachedCloseReports state.session.directory state.session.descriptor error.closeState
  owner : close.slot = state.owner
  unlocked : close.result = .ok ()
  closeBindings : close.bindings = error.bindingsAfter
  files : NativeCloseFiles state
  reachedNames : files.names = error.bindingsAfter
  reachedBytes : ∀ inode payload, files.bytes inode = some payload → (error.inodes error.after).visible inode = payload
  observe : ∀ plan : ClosedReadyReopenLayout state.writer state.releasedFiles,
    ∀ selected : SelectedIntegrityCheckpoint state.writer.published.durable
      state.releasedFiles.image.directory.active.manifest state.writer.checkpoint,
      Nonempty (NativeCloseAlignedReads files input close.finished.descriptors plan.layout selected)

/-- A failed early checkpoint has no new selected manifest. Its actual
close and reopen keep the old manifest, the runs it names and the
previously acknowledged history. The reached raw runs can include newer
unselected names, according to the reported directory effect. -/
structure NativeEarlyCheckpointReopen (current : NativeReadPosition history log) {input : FilePath}
    (seen : NativeEarlyCheckpointReopenObservation current.state input)
    (next : NativeReadPosition history log) : Prop where
  failed : NativeReturnedCheckpointRunDirectoryError current seen.error
  closed : seen.close.run = .ok () seen.close.finished ∧ seen.close.finished.phase = .closed ∧
    seen.close.finished.files = ⟨(⟨none, none, []⟩, seen.error.after), current.state.releasedFiles.owners⟩ ∧
    seen.close.finished.descriptors = current.state.census.afterDrops
      (seen.close.drops .active ++ seen.close.drops .pending ++ seen.close.drops .directory) ∧
    seen.close.bindings (current.state.session.directory.file .lock) =
      some (current.state.census.inode current.state.owner.description)
  released : (⟨seen.error.files seen.close.finished.files.image.2, seen.close.finished.files.owners⟩ :
    LockedFileState FileImage) = current.state.releasedFiles
  reads : next.reads = current.reads
  phaseFresh : next.state.session.phaseRef ≠ current.state.session.phaseRef
  sessionFresh : next.state.session.sessionRef ≠ current.state.session.sessionRef
  lock : next.state.census.inode next.state.owner.description = current.state.census.inode current.state.owner.description
  directory : next.state.census.inode next.state.directorySlot.description =
    current.state.census.inode current.state.directorySlot.description
  checkpoint : next.state.writer.checkpoint = current.state.writer.checkpoint
  durable : next.state.writer.published.durable = current.state.writer.published.durable
  target : next.state.writer.target = current.state.writer.target
  exactOpen :
    ∃ (plan : ClosedReadyReopenLayout current.state.writer current.state.releasedFiles)
      (selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
        current.state.releasedFiles.image.directory.active.manifest current.state.writer.checkpoint)
      (observed : NativeCloseAlignedReads seen.files input seen.close.finished.descriptors plan.layout selected),
      next.opened = observed.run ∧ next.opened = .ok next.state.session (next.state.census, next.state.files) ∧
      next.initial = next.state ∧ next.state.session.directory = current.state.session.directory ∧
      next.state.owner = observed.opening.admission.owner ∧ next.state.directorySlot = observed.opening.admission.cached ∧
      next.state.cache = observed.opening.admission.cache ∧ next.state.census = observed.opening.finish.census ∧
      (current.state.writer.target.pair.manifest = none → seen.error.bindingsAfter (current.state.session.directory.file .manifest) = none) ∧
      (∀ bytes, current.state.writer.target.pair.manifest = some bytes →
        observed.ReadsOriginal (current.state.session.directory.file .manifest) bytes) ∧
      (∀ bytes manifest, current.state.writer.target.pair.manifest = some bytes →
        Manifest.IntegrityCheckpoint.decode bytes = .ok manifest → ∀ index < manifest.header.runCount.toNat,
        ∀ payload, current.state.writer.published.durable manifest.header.generation index = some payload →
        observed.ReadsOriginal (current.state.session.directory.file (.run manifest.header.generation index)) payload) ∧
      observed.ReadsOriginal (current.state.session.directory.file .walBoundary)
        (WAL.Boundary.encode (WAL.encode current.state.writer.history).size.toUInt64) ∧
      (∀ segment ∈ plan.layout.sealed ++ [plan.layout.keeper],
        observed.ReadsOriginal (current.state.session.directory.file (.walSegment segment.first)) segment.bytes) ∧
      ∀ path payload, observed.ReadsOriginal path payload →
        ∃ read : observed.opening.reads.reads.ObservesFile path payload,
          seen.error.bindingsAfter path = some read.object ∧ (seen.error.inodes seen.error.after).visible read.object = payload
  replay : InstalledClientReplay log current.reads history next.state.writer.installed next.state.session

theorem NativeReadPosition.recoversEarlyCheckpointError (current : NativeReadPosition history log) {input : FilePath}
    (seen : NativeEarlyCheckpointReopenObservation current.state input) :
    ∃ next, NativeEarlyCheckpointReopen current seen next := by
  let valid := current.readPrefix.refines.1
  have failed := current.checkpointRunDirectoryError seen.error
  have closed := seen.close.outcome rfl
  rw [seen.unlocked] at closed
  have cleared := seen.close.finishedFiles valid.retained.held
  have closeLock := (congrFun seen.closeBindings (current.state.session.directory.file .lock)).trans failed.lockObject
  have closeCensus := seen.close.finishedDescriptors
  change seen.close.finished.descriptors = (seen.error.descriptors seen.error.after).afterDrops _ at closeCensus
  rw [failed.census] at closeCensus
  have projected : (⟨seen.error.files seen.close.finished.files.image.2, seen.close.finished.files.owners⟩ :
      LockedFileState FileImage) = current.state.releasedFiles := by
    rw [cleared]
    change (⟨seen.error.files seen.error.after, _⟩ : LockedFileState FileImage) = _
    rw [seen.error.sameFiles valid]
    rfl
  obtain ⟨plan, selected, observed, reached, seed, directory, owner, directorySlot, cache, census, sessionFresh, phaseFresh,
    lockInode, directoryInode, _, _, target, checkpoint, durable, absent, manifest, runs, marker, wal, replay⟩ :=
    current.readPrefix.reopensReleasedAligned seen.files seen.observe
  let next : NativeReadPosition history log := ⟨observed.run, reached, reached, current.reads, seed⟩
  refine ⟨next, failed, ⟨closed, rfl, cleared, closeCensus, closeLock⟩, projected, rfl, phaseFresh, sessionFresh,
    lockInode, directoryInode, checkpoint, durable, target, ⟨plan, selected, observed, rfl, seed.frames.1, rfl,
      directory, owner, directorySlot, cache, census, ?_, manifest, runs, marker, wal, ?_⟩, replay⟩
  · intro missing
    exact (congrFun seen.reachedNames (current.state.session.directory.file .manifest)).symm.trans (absent missing).1
  · intro path payload selectedRead
    obtain ⟨read, name, bytes⟩ := selectedRead
    exact ⟨read, (congrFun seen.reachedNames path).symm.trans name, seen.reachedBytes _ _ bytes⟩

end Alvoki.Storage.DiskSession
