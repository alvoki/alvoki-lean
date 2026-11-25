import Alvoki.Storage.Disk.NativeCheckpointRunFileIssue
import Alvoki.Storage.Disk.NativePendingCheckpointOpenPhase

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair

/-- The pending run has been flushed and its fsync is issued. The outer
stop records the reached file effect with the run descriptor still live. -/
structure NativeCheckpointRunFileStop {image : Type} (state : NativeReadyState)
    (cut : CheckpointPowerCut state.session.directory state.writer) where
  effect : NativeCheckpointRunFileEffect (image := image) state cut
  fsync : CheckpointOpenHandle → EStateM FilePath image (Except IO.Error Unit)
  stopped : fsync effect.handle effect.flushed = .error effect.path effect.after
  census : effect.prior.descriptors effect.after = effect.prior.descriptors effect.flushed

namespace NativeCheckpointRunFileStop

variable {image heap : Type} {state : NativeReadyState} {cut : CheckpointPowerCut state.session.directory state.writer}
  (stop : NativeCheckpointRunFileStop (image := image) state cut)

abbrev issue : NativeCheckpointRunFileIssue (image := image) state cut :=
  stop.effect.toNativeCheckpointRunFileIssue

theorem selectsHandle : (state.cache.remember stop.effect.path stop.effect.handle).resolve
    state.session.directory.path stop.effect.path stop.effect.prior.primitives.openRead stop.effect.flushed =
    .ok stop.effect.handle (state.cache, stop.effect.flushed) := by
  have consumed : state.cache.consume stop.effect.path = state.cache := by
    have pending := stop.effect.prior.pending
    cases known : state.cache with
    | mk directory active pendingAtIssue => simp_all [Cache.consume]
  rw [Cache.resolveRemembered (file_ne_directory _ _) stop.effect.handle stop.effect.prior.primitives.openRead
    stop.effect.flushed, consumed]

def syncGroup : EStateM FilePath (CensusDirectoryCache × image) (Except IO.Error Unit) :=
  (SyncPathGroup.run (checkpointSyncUntilStop state.session.directory.path stop.effect.prior.primitives.openRead stop.fsync)
    #[stop.effect.path]).run

theorem stopsGroup :
    stop.syncGroup stop.issue.atIssue = .error stop.effect.path (state.cache, stop.effect.after) :=
  checkpointSyncGroupStops stop.selectsHandle stop.stopped

/-- Consuming the pending cache entry does not release the descriptor
before the primitive returns. The held root and lock slots remain live. -/
theorem custody (valid : state.Valid) :
    stop.effect.prior.descriptors stop.effect.after = stop.effect.handle.1 ∧
    stop.effect.handle.2.1 ∈ (stop.effect.prior.descriptors stop.effect.after).slots ∧
    state.directorySlot ∈ (stop.effect.prior.descriptors stop.effect.after).slots ∧
    state.owner ∈ (stop.effect.prior.descriptors stop.effect.after).slots ∧
    stop.effect.view.visible state.session.directory.path = some (stop.effect.prior.captured.inode state.directorySlot.description) ∧
    stop.effect.view.visible (state.session.directory.file .lock) = some (state.census.inode state.owner.description) := by
  have census := stop.census.trans stop.effect.atFileSync
  have prior := stop.effect.prior.prefixCensus stop.effect.index (Nat.le_refl _)
  refine ⟨census, ?_, ?_, ?_, ?_, ?_⟩
  · rw [census, stop.effect.allocated]
    exact List.mem_cons_self
  · rw [census, stop.effect.allocated]
    exact List.mem_cons_of_mem _ (prior.symm ▸ valid.directoryLive)
  · rw [census, stop.effect.allocated]
    exact List.mem_cons_of_mem _ (prior.symm ▸ valid.ownerLive)
  · rw [stop.effect.sameNames, stop.effect.directoryAtIssue, stop.effect.prior.capturedInode]
  · rw [stop.effect.sameNames]
    exact stop.effect.lockAtIssue

noncomputable def onOpenPhase (opened : NativeOpenedHandle heap) :
    EStateM FilePath (heap × (CensusDirectoryCache × image)) (Except IO.Error Unit) := fun entry =>
  match runCheckpointPrefixOnOpenPhase opened (fun _ => runSteps stop.effect.index ++ [.writeRun stop.effect.index])
      stop.effect.prior.perform entry with
  | .error cause reached => .ok (.error cause) reached
  | .ok () (phase, files) =>
    match stop.syncGroup files with
    | .ok result reached => .ok result (phase, reached)
    | .error path reached => .error path (phase, reached)

end NativeCheckpointRunFileStop

/-- The still-pending operation carries the old selected checkpoint,
committed history and previous reads independently of a later reopen. -/
structure NativePendingCheckpointRunFile (current : NativeReadPosition history log)
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    (stop : NativeCheckpointRunFileStop (image := image) current.state cut) : Prop where
  issued : CheckpointIssue stop.effect.prior.perform current.state.session.phase stop.effect.prior.entry
    cut.checkpoint.prepared cut.checkpoint.manifest cut.completed (.syncRun stop.effect.index) stop.issue.atIssue
  stopped : stop.syncGroup stop.issue.atIssue = .error stop.effect.path (current.state.cache, stop.effect.after)
  held : current.state.files.owners.Owns current.state.session.directory current.state.session.descriptor
  census : stop.effect.prior.descriptors stop.effect.after = stop.effect.handle.1
  runLive : stop.effect.handle.2.1 ∈ (stop.effect.prior.descriptors stop.effect.after).slots
  directoryLive : current.state.directorySlot ∈ (stop.effect.prior.descriptors stop.effect.after).slots
  lockLive : current.state.owner ∈ (stop.effect.prior.descriptors stop.effect.after).slots
  files : stop.effect.prior.files stop.effect.after = current.state.files.image
  selected : SelectedIntegrityCheckpoint (stop.effect.prior.runs stop.effect.after).guaranteed
    (stop.effect.prior.files stop.effect.after).directory.active.manifest current.state.writer.checkpoint
  replay : PendingClientReplay log current.reads history
  bounded : ∀ read ∈ current.reads, read.BoundedBy history.length

theorem NativeReadPosition.stopsAtCheckpointRunFile (current : NativeReadPosition history log)
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    (stop : NativeCheckpointRunFileStop (image := image) current.state cut) :
    NativePendingCheckpointRunFile current stop := by
  obtain ⟨valid, _, replay⟩ := current.readPrefix.refines
  obtain ⟨census, runLive, directoryLive, lockLive, _, _⟩ := stop.custody valid
  exact ⟨stop.issue.issues valid, stop.stopsGroup, valid.retained.held, census, runLive, directoryLive, lockLive,
    stop.effect.filesAtEffect, stop.effect.selectedCheckpoint valid, replay, current.readPrefix.readsBounded⟩

/-- The actual opened phase is poisoned before the original run prefix
and the issued fsync on the selected run. This cut never reaches the
later runs, the directory barrier or the ready phase setter. -/
theorem NativeOpenedPosition.stopsAtCheckpointRunFile {heap : Type} {opened : NativeOpenedHandle heap}
    (current : NativeOpenedPosition opened)
    {cut : CheckpointPowerCut current.current.ready.state.session.directory current.current.ready.state.writer}
    (stop : NativeCheckpointRunFileStop (image := image) current.current.ready.state cut) :
    let state := current.current.ready.state
    opened.table.UsesOpenCheckpointSchedule state.session.directory opened.files opened.phase ∧
    NativePendingCheckpointRunFile current.current.ready stop ∧
    ∃ poisoned, opened.contents poisoned opened.phase = some .poisoned ∧
      opened.get opened.phase current.reached = .ok state.session.phase current.reached ∧
      opened.set opened.phase .poisoned current.reached = .ok () poisoned ∧
      stop.onOpenPhase opened (current.reached, stop.effect.prior.entry.image) =
        .error stop.effect.path (poisoned, state.cache, stop.effect.after) := by
  intro state
  have valid := current.current.ready.readPrefix.refines.1
  have loaded := opened.phaseEffects.reads current.reached opened.phase state.session.phase current.stored
  obtain ⟨poisoned, written, stored⟩ := opened.phaseEffects.writes current.reached opened.phase state.session.phase
    .poisoned current.stored
  have available : CheckpointPreflight state.session.phase (.ok (cut.checkpoint.prepared, cut.checkpoint.manifest)) := by
    rw [valid.phase]
    exact cut.preflight
  have returned := stop.issue.runPrefix
  rw [stop.effect.completed] at returned
  have arrived : runCheckpointPrefixOnOpenPhase opened (fun _ => runSteps stop.effect.index ++ [.writeRun stop.effect.index])
      stop.effect.prior.perform (current.reached, stop.effect.prior.entry.image) = .ok () (poisoned, stop.issue.atIssue) :=
    available.reachesOpenPrefix opened loaded written returned
  refine ⟨current.uses.checkpoint, current.current.ready.stopsAtCheckpointRunFile stop, poisoned, stored, loaded, written, ?_⟩
  have stopped : stop.syncGroup stop.issue.atIssue = .error stop.effect.path (state.cache, stop.effect.after) := stop.stopsGroup
  simp only [NativeCheckpointRunFileStop.onOpenPhase, arrived, stopped]

end Alvoki.Storage.DiskSession
