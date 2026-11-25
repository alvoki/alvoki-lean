import Alvoki.Storage.Disk.NativeCheckpointManifestSyncError
import Alvoki.Storage.Disk.NativeExecutionClose
import Alvoki.Storage.Disk.Checkpoint.Reopen.HeldInstallation

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair

namespace NativeCheckpointManifestSyncError

variable {image : Type} {state : NativeReadyState} {cut : CheckpointPowerCut state.session.directory state.writer}

def closeState (report : NativeCheckpointManifestSyncError (image := image) state cut) :
    CachedCloseState CheckpointOpenHandle image :=
  ⟨.poisoned, ⟨(state.cache, report.after), state.files.owners⟩, report.settled.runs.descriptors report.after⟩

/-- The close hands off the reached file projection, including the
manifest scratch and the new run names. The old writer supplies the
earlier history and selected checkpoint for the aligned reopen. -/
def retrySource (report : NativeCheckpointManifestSyncError (image := image) state cut) : NativeReadyState :=
  let files := report.settled.runs.files report.after
  let durable := (report.settled.runs.runs report.after).guaranteed
  { state with writer := { state.writer with
      files
      wal := { state.writer.wal with directory := files.directory }
      published := ⟨files.directory.project .manifest, durable⟩ } }

theorem priorRunsAgree (report : NativeCheckpointManifestSyncError (image := image) state cut) (valid : state.Valid) :
    SelectedRunsAgree state.writer.target.pair.manifest report.retrySource.writer.published.durable state.writer.published.durable := by
  let ready := valid.retained
  intro bytes metadata binding decoded index within
  obtain ⟨payload, stored⟩ := ready.resumed.selected.runExists binding decoded within
  have physical := (congrArg DirectoryPublication.Bindings.manifest ready.walPair).trans binding
  obtain ⟨_, _, stable⟩ := report.priorRunBytes valid physical decoded within stored
  exact stable.guaranteed.trans stored.symm

theorem retryRetained (report : NativeCheckpointManifestSyncError (image := image) state cut) (valid : state.Valid) :
    report.retrySource.writer.RetainedReady state.session.directory state.session.descriptor := by
  let ready := valid.retained
  obtain ⟨pair, survives, frame⟩ := report.selectedPair valid
  have keeps := congrArg CheckpointWalView.kept frame
  have keeper := congrArg CheckpointWalView.keeper frame
  have later : (report.settled.runs.files report.after).later = state.files.image.later :=
    congrArg CheckpointWalView.later frame
  have previous := report.priorRunsAgree valid
  have selected := SelectedIntegrityCheckpoint.withRunMap ready.resumed.selected previous.symm
  have accepted := previous.acceptsVersioned state.writer.target.decoded ready.resumed.accepted
  refine ⟨{ ready.resumed with
    ready := ⟨pair, survives, ?_, ?_, ?_⟩, selected, accepted },
    ⟨ready.layout.ordered, ready.layout.forward, ready.layout.activeEnd, ready.layout.activeBytes⟩,
    ?_, ready.spans, rfl, keeps.trans ready.sealedFiles, ready.active, rfl, ready.held⟩
  · exact (congrArg Publication.Image.active keeper).trans ready.resumed.ready.keeper
  · exact (congrArg Publication.Image.crashImages keeper).trans ready.resumed.ready.keeperDurable
  · change (report.settled.runs.files report.after).later.DurablyEmpty
    rw [later]
    exact ready.resumed.ready.pruned
  · intro binding chosen
    apply ready.valid binding
    change binding ∈ (report.settled.runs.files report.after).directory.active ::
      (report.settled.runs.files report.after).directory.crashImages at chosen
    simpa only [WalSegmentImage.Selects, ready.walPair, ready.walDirectorySettled, pair, survives] using chosen

/-- Physical observations of the unchanged WAL objects at the exact
returned checkpoint error, before the failed writer releases its lock. -/
structure WalObjects (report : NativeCheckpointManifestSyncError (image := image) state cut) : Prop where
  marker : ∀ payload, state.writer.target.pair.walBoundary = some payload → ∃ inode,
    report.view.visible (state.session.directory.file .walBoundary) = some inode ∧
    (report.settled.runs.inodes report.after).visible inode = payload
  segments : ∀ segment ∈ state.writer.wal.sealed ++ [state.writer.wal.active], ∃ inode,
    report.view.visible (state.session.directory.file (.walSegment segment.first)) = some inode ∧
    (report.settled.runs.inodes report.after).visible inode = segment.bytes

theorem liveManifest (report : NativeCheckpointManifestSyncError (image := image) state cut) (valid : state.Valid) :
    match state.writer.target.pair.manifest with
    | none => report.view.visible (state.session.directory.file .manifest) = none
    | some bytes => ∃ inode, report.view.Stable (state.session.directory.file .manifest) inode bytes := by
  have manifest := report.manifestAtReturn valid
  rw [(report.selectedPair valid).1] at manifest
  cases present : state.writer.target.pair.manifest with
  | none => simpa only [present] using manifest
  | some payload =>
    rw [present] at manifest
    exact manifest.imp fun _ => And.right

/-- The post-error manifest and runs are derived from the exact already
reached view. Only the original WAL object observations are supplied by
the consumer of this close/reopen theorem. -/
def closeFiles (report : NativeCheckpointManifestSyncError (image := image) state cut) (valid : state.Valid)
    (wal : report.WalObjects) : NativeCloseFiles report.retrySource where
  names := report.view.visible
  bytes := fun inode => some ((report.settled.runs.inodes report.after).visible inode)
  directory := (report.custody valid).2.2.2.2.2.1.trans (congrArg some report.settled.runs.capturedInode)
  lock := (report.custody valid).2.2.2.2.2.2
  manifestAbsent missing := by
    change state.writer.target.pair.manifest = none at missing
    change report.view.visible (state.session.directory.file .manifest) = none
    simpa only [missing] using report.liveManifest valid
  manifest payload present := by
    have observed := report.liveManifest valid
    change state.writer.target.pair.manifest = some payload at present
    rw [present] at observed
    obtain ⟨inode, stable⟩ := observed
    exact ⟨inode, stable.visibleBinding, congrArg some stable.visibleBytes⟩
  marker payload present := by
    obtain ⟨inode, named, bytes⟩ := wal.marker payload present
    exact ⟨inode, named, congrArg some bytes⟩
  wal segment member := by
    obtain ⟨inode, named, bytes⟩ := wal.segments segment member
    exact ⟨inode, named, congrArg some bytes⟩
  runs raw metadata present decoded index within payload stored := by
    have agrees := report.priorRunsAgree valid raw metadata present decoded index within
    have original := agrees.symm.trans stored
    have selected := (congrArg DirectoryPublication.Bindings.manifest valid.retained.walPair).trans present
    obtain ⟨inode, _, stable⟩ := report.priorRunBytes valid selected decoded within original
    exact ⟨inode, stable.visibleBinding, congrArg some stable.visibleBytes⟩

end NativeCheckpointManifestSyncError

/-- A close starts from the actual staged-manifest file sync error.
The next read report uses the exact released scratch, retained runs and
census after that close. -/
structure NativeCheckpointManifestSyncReopenObservation (state : NativeReadyState) (input : FilePath) where
  image : Type
  cut : CheckpointPowerCut state.session.directory state.writer
  error : NativeCheckpointManifestSyncError (image := image) state cut
  close : CachedCloseReports state.session.directory state.session.descriptor error.closeState
  owner : close.slot = state.owner
  unlocked : close.result = .ok ()
  closeBindings : close.bindings = error.view.visible
  scratch : (error.settled.runs.files error.after).directory.staged .manifest =
    some ((error.settled.runs.inodes error.after).visible (error.handle.1.inode error.handle.2.1.description), cut.tookEffect)
  wal : error.WalObjects
  observe : ∀ (valid : state.Valid)
    (plan : ClosedReadyReopenLayout error.retrySource.writer error.retrySource.releasedFiles)
    (selected : SelectedIntegrityCheckpoint error.retrySource.writer.published.durable
      error.retrySource.releasedFiles.image.directory.active.manifest error.retrySource.writer.checkpoint),
    Nonempty (NativeCloseAlignedReads (error.closeFiles valid wal) input close.finished.descriptors plan.layout selected)

structure NativeCheckpointManifestSyncReopened (current : NativeReadPosition history log) {input : FilePath}
    (seen : NativeCheckpointManifestSyncReopenObservation current.state input)
    (next : NativeReadPosition history log) : Prop where
  failed : NativeReturnedCheckpointManifestSyncError current seen.error
  closed : seen.close.run = .ok () seen.close.finished ∧ seen.close.finished.phase = .closed ∧
    seen.close.finished.files = ⟨(⟨none, none, []⟩, seen.error.after), current.state.releasedFiles.owners⟩ ∧
    seen.close.finished.descriptors = current.state.census.afterDrops
      (seen.close.drops .active ++ seen.close.drops .pending ++ seen.close.drops .directory) ∧
    seen.close.bindings (current.state.session.directory.file .lock) =
      some (current.state.census.inode current.state.owner.description)
  released : (⟨seen.error.settled.runs.files seen.close.finished.files.image.2, seen.close.finished.files.owners⟩ :
    LockedFileState FileImage) = seen.error.retrySource.releasedFiles
  scratch : seen.error.retrySource.releasedFiles.image.directory.staged .manifest =
    some (seen.cut.checkpoint.manifest, seen.cut.tookEffect)
  reads : next.reads = current.reads
  directory : next.state.session.directory = current.state.session.directory
  root : next.state.census.inode next.state.directorySlot.description =
    current.state.census.inode current.state.directorySlot.description
  lock : next.state.census.inode next.state.owner.description = current.state.census.inode current.state.owner.description
  sessionFresh : next.state.session.sessionRef ≠ current.state.session.sessionRef
  phaseFresh : next.state.session.phaseRef ≠ current.state.session.phaseRef
  checkpoint : next.state.writer.checkpoint = current.state.writer.checkpoint
  durable : next.state.writer.published.durable = (seen.error.settled.runs.runs seen.error.after).guaranteed
  target : next.state.writer.target = current.state.writer.target
  exactOpen : ∃ (valid : current.state.Valid)
      (plan : ClosedReadyReopenLayout seen.error.retrySource.writer seen.error.retrySource.releasedFiles)
      (selected : SelectedIntegrityCheckpoint seen.error.retrySource.writer.published.durable
        seen.error.retrySource.releasedFiles.image.directory.active.manifest seen.error.retrySource.writer.checkpoint)
      (observed : NativeCloseAlignedReads (seen.error.closeFiles valid seen.wal) input seen.close.finished.descriptors
        plan.layout selected),
    next.opened = observed.run ∧ next.opened = .ok next.state.session (next.state.census, next.state.files) ∧
    next.initial = next.state ∧ next.state.owner = observed.opening.admission.owner ∧
    next.state.directorySlot = observed.opening.admission.cached ∧ next.state.cache = observed.opening.admission.cache ∧
    next.state.census = observed.opening.finish.census ∧ NativeCloseSelectedReads observed ∧
    ∀ path payload, observed.ReadsOriginal path payload →
      ∃ read : observed.opening.reads.reads.ObservesFile path payload,
        seen.error.view.visible path = some read.object ∧
          (seen.error.settled.runs.inodes seen.error.after).visible read.object = payload
  replay : InstalledClientReplay log current.reads history next.state.writer.installed next.state.session

/-- The captured aligned opener selects the previous checkpoint from
the exact post-close scratch image, carrying the earlier read replay. -/
theorem NativeReadPosition.recoversCheckpointManifestSyncError (current : NativeReadPosition history log) {input : FilePath}
    (seen : NativeCheckpointManifestSyncReopenObservation current.state input) :
    ∃ next, NativeCheckpointManifestSyncReopened current seen next := by
  obtain ⟨valid, sameHistory, pending⟩ := current.readPrefix.refines
  have failed := current.checkpointManifestSyncError seen.error
  have returned := seen.close.outcome rfl
  rw [seen.unlocked] at returned
  have cleared := seen.close.finishedFiles failed.held
  have census := seen.close.finishedDescriptors
  change seen.close.finished.descriptors = (seen.error.settled.runs.descriptors seen.error.after).afterDrops _ at census
  rw [failed.census] at census
  have lock := (congrFun seen.closeBindings (current.state.session.directory.file .lock)).trans failed.lockObject
  have released : (⟨seen.error.settled.runs.files seen.close.finished.files.image.2, seen.close.finished.files.owners⟩ :
    LockedFileState FileImage) = seen.error.retrySource.releasedFiles := by
    rw [cleared]
    rfl
  have reopened := (seen.error.closeFiles valid seen.wal).reopensReleasedAligned (seen.error.retryRetained valid)
    sameHistory pending current.readPrefix.readsBounded (seen.observe valid)
  obtain ⟨plan, selected, observed, reached, seed, directory, owner, cached, cache, final,
    sessionFresh, phaseFresh, sameLock, sameRoot, _, _, target, checkpoint, durable, absent, manifest, runs, marker, wal, replay⟩ := reopened
  let next : NativeReadPosition history log := ⟨observed.run, reached, reached, current.reads, seed⟩
  have scratch : seen.error.retrySource.releasedFiles.image.directory.staged .manifest =
      some (seen.cut.checkpoint.manifest, seen.cut.tookEffect) := by
    change (seen.error.settled.runs.files seen.error.after).directory.staged .manifest = _
    rw [seen.scratch, seen.error.stagedBytes.2.1]
  refine ⟨next, failed, ⟨returned, rfl, cleared, census, lock⟩, released, scratch, rfl, directory, sameRoot, sameLock,
    sessionFresh, phaseFresh, checkpoint, durable, target, ⟨valid, plan, selected, observed, rfl, seed.frames.1, rfl,
      owner, cached, cache, final, ⟨absent, manifest, runs, marker, wal⟩, ?_⟩, replay⟩
  intro path payload read
  obtain ⟨observedFile, name, bytes⟩ := read
  exact ⟨observedFile, name, Option.some.inj bytes⟩

end Alvoki.Storage.DiskSession
