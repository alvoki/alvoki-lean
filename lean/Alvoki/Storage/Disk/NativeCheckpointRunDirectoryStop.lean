import Alvoki.Storage.Disk.NativeCheckpointRunDirectoryError
import Alvoki.Storage.Disk.NativePendingCheckpointOpenPhase

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair

/-- The first directory barrier issues after all run writes, file
syncs and their temporary-file finalizers. Its outer stop carries the
path of the cached directory and has no ordinary checkpoint result. -/
structure NativeCheckpointRunDirectoryStop {image : Type} (state : NativeReadyState)
    (cut : CheckpointPowerCut state.session.directory state.writer) where
  runs : NativeCheckpointRunObservations (image := image) state cut cut.checkpoint.table.runs.length
  completed : cut.completed = runSteps cut.checkpoint.table.runs.length
  directoryBound : (runs.views cut.checkpoint.table.runs.length).visible state.session.directory.path =
    some (state.census.inode state.directorySlot.description)
  lockBound : (runs.views cut.checkpoint.table.runs.length).visible (state.session.directory.file .lock) =
    some (state.census.inode state.owner.description)
  fsync : CheckpointOpenHandle → EStateM FilePath image (Except IO.Error Unit)
  reached : image
  stopped : fsync (runs.captured, state.directorySlot, 0) (runs.atRun cut.checkpoint.table.runs.length) =
    .error state.session.directory.path reached
  census : runs.descriptors reached = runs.descriptors (runs.atRun cut.checkpoint.table.runs.length)
  inodeBytes : runs.inodes reached = runs.inodes (runs.atRun cut.checkpoint.table.runs.length)
  view : RunDirectoryInodeView state.session.directory (runs.inodes reached) (runs.runs reached)
  visibleNames : view.visible = (runs.views cut.checkpoint.table.runs.length).visible
  survivingNames : ∀ names ∈ view.crashBindings, if cut.tookEffect then names = view.visible
    else names ∈ (runs.views cut.checkpoint.table.runs.length).crashBindings
  directoryEffect : (runs.files reached).directory = if cut.tookEffect then
    (runs.files (runs.atRun cut.checkpoint.table.runs.length)).directory.syncDirectory
    else (runs.files (runs.atRun cut.checkpoint.table.runs.length)).directory
  walFrame : CheckpointWalView.ofFiles (runs.files reached) =
    CheckpointWalView.ofFiles (runs.files (runs.atRun cut.checkpoint.table.runs.length))

namespace NativeCheckpointRunDirectoryStop

variable {image heap : Type} {state : NativeReadyState} {cut : CheckpointPowerCut state.session.directory state.writer}
  (stop : NativeCheckpointRunDirectoryStop (image := image) state cut)

abbrev atIssue : image := stop.runs.atRun cut.checkpoint.table.runs.length

abbrev handle : CheckpointOpenHandle := (stop.runs.captured, state.directorySlot, 0)

include stop in
theorem current : cut.current = .syncRunsDirectory := by
  have ordered := cut.schedule
  rw [stop.completed, CheckpointPublication.steps, List.append_assoc] at ordered
  exact (List.cons.inj (List.append_cancel_left ordered)).1.symm

theorem issues (valid : state.Valid) :
    CheckpointIssue stop.runs.perform state.session.phase stop.runs.entry cut.checkpoint.prepared
      cut.checkpoint.manifest cut.completed .syncRunsDirectory (state.cache, stop.atIssue) := by
  have schedule := cut.schedule
  rw [stop.current] at schedule
  have returnedPrefix := stop.runs.runPrefix
  rw [← stop.completed] at returnedPrefix
  rw [valid.phase]
  exact cut.preflight.reachesIssue stop.runs.perform stop.runs.entry schedule returnedPrefix

def syncGroup : EStateM FilePath (CensusDirectoryCache × image) (Except IO.Error Unit) :=
  (SyncPathGroup.run (checkpointSyncUntilStop state.session.directory.path stop.runs.primitives.openRead stop.fsync)
    #[state.session.directory.path]).run

theorem stopsGroup : stop.syncGroup (state.cache, stop.atIssue) =
    .error state.session.directory.path (state.cache, stop.reached) :=
  checkpointCachedDirectorySyncStops stop.runs.directoryCached stop.stopped

/-- The issued and stopped states have the original lock and cached
directory. The run slots were finalized in the completed prefix. -/
theorem custody (valid : state.Valid) :
    stop.runs.descriptors stop.atIssue = state.census ∧ stop.runs.descriptors stop.reached = state.census ∧
    state.owner ∈ (stop.runs.descriptors stop.atIssue).slots ∧ state.directorySlot ∈ (stop.runs.descriptors stop.atIssue).slots ∧
    stop.view.visible state.session.directory.path = some (stop.handle.1.inode state.directorySlot.description) ∧
    stop.view.visible (state.session.directory.file .lock) = some (state.census.inode state.owner.description) := by
  have atIssue := stop.runs.prefixCensus _ (Nat.le_refl _)
  rw [stop.visibleNames]
  exact ⟨atIssue, stop.census.trans atIssue, atIssue.symm ▸ valid.ownerLive, atIssue.symm ▸ valid.directoryLive,
    stop.directoryBound.trans (congrArg some stop.runs.capturedInode.symm), stop.lockBound⟩

theorem preservesStable {path : FilePath} {inode : Nat} {bytes : ByteArray}
    (before : (stop.runs.views cut.checkpoint.table.runs.length).Stable path inode bytes) :
    stop.view.Stable path inode bytes := by
  have visible := (congrFun stop.visibleNames path).trans before.visibleBinding
  refine ⟨visible, ?_, stop.inodeBytes.symm ▸ before.visibleBytes, stop.inodeBytes.symm ▸ before.crashBytes⟩
  intro names survived
  have chosen := stop.survivingNames names survived
  cases effect : cut.tookEffect <;> simp only [effect, Bool.false_eq_true, ite_false, ite_true] at chosen
  · exact before.crashBinding names chosen
  · exact (congrFun chosen path).trans visible

/-- Neither observed sync effect changes which checkpoint and WAL are
selected. Stable old run bytes remain guaranteed in the reached map. -/
theorem selectsPrior (valid : state.Valid) :
    (stop.runs.files stop.reached).directory.active = state.writer.target.pair ∧
    (stop.runs.files stop.reached).directory.crashImages = [state.writer.target.pair] ∧
    CheckpointWalView.ofFiles (stop.runs.files stop.reached) = CheckpointWalView.ofFiles state.files.image ∧
    SelectedIntegrityCheckpoint (stop.runs.runs stop.reached).guaranteed
      (stop.runs.files stop.reached).directory.active.manifest state.writer.checkpoint := by
  let ready := valid.retained
  have atIssue := stop.runs.filesAtRun _ (Nat.le_refl _)
  have pair : state.files.image.directory.active = state.writer.target.pair := ready.resumed.ready.selected
  have choices : state.files.image.directory.crashImages = [state.writer.target.pair] := ready.resumed.ready.settled
  have active : (stop.runs.files stop.reached).directory.active = state.writer.target.pair := by
    rw [stop.directoryEffect, atIssue]
    cases cut.tookEffect <;> exact pair
  have crash : (stop.runs.files stop.reached).directory.crashImages = [state.writer.target.pair] := by
    rw [stop.directoryEffect, atIssue]
    cases cut.tookEffect
    · exact choices
    · exact congrArg (fun choice => [choice]) pair
  have selected := ready.walPair.symm ▸ ready.resumed.selected
  refine ⟨active, crash, stop.walFrame.trans (congrArg CheckpointWalView.ofFiles atIssue), ?_⟩
  rw [active, ← ready.walPair]
  apply SelectedIntegrityCheckpoint.withRunMap selected
  intro raw metadata bound decoded index within
  obtain ⟨payload, stored⟩ := selected.runExists bound decoded within
  obtain ⟨inode, _, prior⟩ := stop.runs.priorRunAtEnd valid bound decoded within stored
  exact stored.trans (stop.preservesStable prior).guaranteed.symm

theorem manifestStable :
    match state.files.image.directory.active.manifest with
    | none => stop.view.visible (state.session.directory.file .manifest) = none
    | some bytes => ∃ inode, (stop.runs.views 0).Stable (state.session.directory.file .manifest) inode bytes ∧
        stop.view.Stable (state.session.directory.file .manifest) inode bytes := by
  have before := stop.runs.manifestAtEnd
  cases selected : state.files.image.directory.active.manifest <;> rw [selected] at before
  · exact (congrFun stop.visibleNames _).trans before
  · obtain ⟨inode, entry, retained⟩ := before
    exact ⟨inode, entry, stop.preservesStable retained⟩

theorem priorRunStable (valid : state.Valid)
    {bytes payload : ByteArray} {metadata : Manifest.IntegrityCheckpoint} {index : Nat}
    (bound : state.writer.wal.directory.active.manifest = some bytes)
    (decoded : Manifest.IntegrityCheckpoint.decode bytes = .ok metadata)
    (within : index < metadata.header.runCount.toNat)
    (stored : state.writer.published.durable metadata.header.generation index = some payload) :
    ∃ inode, (stop.runs.views 0).Stable (state.session.directory.file (.run metadata.header.generation index)) inode payload ∧
      stop.view.Stable (state.session.directory.file (.run metadata.header.generation index)) inode payload := by
  obtain ⟨inode, entry, retained⟩ := stop.runs.priorRunAtEnd valid bound decoded within stored
  exact ⟨inode, entry, stop.preservesStable retained⟩

theorem freshRunSettled {index : Nat} (within : index < cut.checkpoint.table.runs.length)
    (effective : cut.tookEffect = true) :
    ∃ (run : Compaction.CheckedRun) (inode : Nat), cut.checkpoint.table.runs.toArray[index]? = some run ∧
      stop.view.Stable (state.session.directory.file (.run cut.checkpoint.prepared.generation index)) inode run.run.bytes := by
  obtain ⟨run, inode, selected, bound, bytes, durable⟩ := stop.runs.freshRunAtEnd within
  have bound := (congrFun stop.visibleNames _).trans bound
  refine ⟨run, inode, selected, bound, ?_, stop.inodeBytes.symm ▸ bytes, stop.inodeBytes.symm ▸ durable⟩
  intro names survived
  have settled := stop.survivingNames names survived
  rw [effective] at settled
  exact (congrFun settled _).trans bound

noncomputable def onOpenPhase (opened : NativeOpenedHandle heap) :
    EStateM FilePath (heap × (CensusDirectoryCache × image)) (Except IO.Error Unit) := fun entry =>
  match runCheckpointPrefixOnOpenPhase opened (fun next => runSteps next.table.runs.length) stop.runs.perform entry with
  | .error cause reached => .ok (.error cause) reached
  | .ok () (phase, files) =>
    match stop.syncGroup files with
    | .ok result reached => .ok result (phase, reached)
    | .error path reached => .error path (phase, reached)

/-- The original opened phase is read and poisoned before the actual
run callbacks and the cached directory issue. The unfinished checkpoint
keeps the earlier replay for the still-selected history. -/
theorem stopsOnOpenPhase {opened : NativeOpenedHandle heap} (current : NativeOpenedPosition opened)
    {cut : CheckpointPowerCut current.current.ready.state.session.directory current.current.ready.state.writer}
    (stop : NativeCheckpointRunDirectoryStop (image := image) current.current.ready.state cut) :
    let state := current.current.ready.state
    opened.table.UsesOpenCheckpointSchedule state.session.directory opened.files opened.phase ∧
    CheckpointIssue stop.runs.perform state.session.phase stop.runs.entry cut.checkpoint.prepared cut.checkpoint.manifest
      cut.completed .syncRunsDirectory (state.cache, stop.atIssue) ∧
    state.files.owners.Owns state.session.directory state.session.descriptor ∧
    PendingClientReplay current.current.submissions current.current.ready.reads current.current.history ∧
    (∀ read ∈ current.current.ready.reads, read.BoundedBy current.current.history.length) ∧
    ∃ poisoned, opened.contents poisoned opened.phase = some .poisoned ∧
      opened.get opened.phase current.reached = .ok state.session.phase current.reached ∧
      opened.set opened.phase .poisoned current.reached = .ok () poisoned ∧
      stop.onOpenPhase opened (current.reached, stop.runs.entry.image) =
        .error state.session.directory.path (poisoned, state.cache, stop.reached) := by
  intro state
  obtain ⟨valid, _, replay⟩ := current.current.ready.readPrefix.refines
  have loaded := opened.phaseEffects.reads current.reached opened.phase state.session.phase current.stored
  obtain ⟨poisoned, written, stored⟩ := opened.phaseEffects.writes current.reached opened.phase state.session.phase
    .poisoned current.stored
  have available : CheckpointPreflight state.session.phase (.ok (cut.checkpoint.prepared, cut.checkpoint.manifest)) := by
    rw [valid.phase]
    exact cut.preflight
  have arrived : runCheckpointPrefixOnOpenPhase opened (fun next => runSteps next.table.runs.length)
      stop.runs.perform (current.reached, stop.runs.entry.image) =
      .ok () (poisoned, state.cache, stop.atIssue) :=
    available.reachesOpenPrefix opened loaded written stop.runs.runPrefix
  refine ⟨current.uses.checkpoint, stop.issues valid, valid.retained.held, replay,
    current.current.ready.readPrefix.readsBounded, poisoned, stored, loaded, written, ?_⟩
  have stopped : stop.syncGroup (state.cache, stop.atIssue) =
      .error state.session.directory.path (state.cache, stop.reached) := stop.stopsGroup
  simp only [onOpenPhase, arrived, stopped]

end NativeCheckpointRunDirectoryStop
end Alvoki.Storage.DiskSession
