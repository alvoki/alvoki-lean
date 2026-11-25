import Alvoki.Storage.Disk.NativeCheckpointFsyncEffects
import Alvoki.Storage.Disk.NativeReadyPowerLoss

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting

/-- The selected files of a ready table before any survivor is chosen. -/
structure NativeReadyStorage (state : NativeReadyState) (storage : CheckpointStorageObservation) : Prop where
  directoryBound : storage.files.names state.session.directory.path = some (state.census.inode state.directorySlot.description)
  lockBound : storage.files.names (state.session.directory.file .lock) = some (state.census.inode state.owner.description)
  manifest : match state.writer.target.pair.manifest with
    | none => storage.files.names (state.session.directory.file .manifest) = none
    | some bytes => storage.files.Stored (state.session.directory.file .manifest) bytes
  marker : storage.files.Stored (state.session.directory.file .walBoundary)
    (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64)
  keeper : storage.files.Stored (state.session.directory.file (.walSegment state.writer.wal.active.first)) state.writer.wal.active.bytes
  sealedFiles : ∀ segment ∈ state.writer.wal.sealed,
    storage.files.Stored (state.session.directory.file (.walSegment segment.first)) segment.bytes
  runs : ∀ bytes metadata, state.writer.target.pair.manifest = some bytes →
    Manifest.IntegrityCheckpoint.decode bytes = .ok metadata → ∀ index < metadata.header.runCount.toNat,
    ∀ payload, state.writer.published.durable metadata.header.generation index = some payload →
    storage.files.Stored (state.session.directory.file (.run metadata.header.generation index)) payload
  settled : ∀ names ∈ storage.crashNames, ∀ path, state.crashPath path → names path = storage.files.names path

namespace NativeReadyStorage

variable {state : NativeReadyState} {first last : CheckpointStorageObservation}

/-- A private checkpoint prefix preserves the previously committed
footprint. Each surviving map is traced back jointly. -/
theorem frame (initial : NativeReadyStorage state first) (frame : first.Frames state.crashPath last) :
    NativeReadyStorage state last := by
  refine ⟨(frame.visible _ (.inl rfl)).1.trans initial.directoryBound,
    (frame.visible _ (.inr (.inl rfl))).1.trans initial.lockBound, ?_,
    frame.visible.stored (.inr (.inr (.inr (.inl (.inl rfl))))) initial.marker,
    frame.visible.stored (.inr (.inr (.inr (.inl (.inr (.inl rfl)))))) initial.keeper, ?_, ?_, ?_⟩
  · have manifest := initial.manifest
    cases selected : state.writer.target.pair.manifest with
    | none =>
      rw [selected] at manifest
      exact (frame.visible _ (.inr (.inr (.inl rfl)))).1.trans manifest
    | some bytes =>
      rw [selected] at manifest
      exact frame.visible.stored (.inr (.inr (.inl rfl))) manifest
  · intro segment member
    exact frame.visible.stored (.inr (.inr (.inr (.inl (.inr (.inr ⟨segment, member, rfl⟩))))))
      (initial.sealedFiles segment member)
  · intro bytes metadata manifest decoded index within payload bound
    exact frame.visible.stored (.inr (.inr (.inr (.inr ⟨bytes, metadata, index, manifest, decoded, within, rfl⟩))))
      (initial.runs bytes metadata manifest decoded index within payload bound)
  · intro names allowed path selected
    obtain ⟨prior, priorAllowed, frameNames⟩ := frame.survivors names allowed
    exact (frameNames path selected).trans
      ((initial.settled prior priorAllowed path selected).trans (frame.visible path selected).1.symm)

/-- Sample durable bytes at the bound inodes of one reached survivor. -/
def observeCrash (stable : NativeReadyStorage state first)
    (names : FilePath → Option Nat) (chosen : names ∈ first.crashNames)
    (contents : Nat → ByteArray)
    (durable : ∀ path, checkpointSurvivorPath state.session.directory state.writer state.writer.target.pair.manifest path →
      ∀ inode, names path = some inode → contents inode ∈ first.files.bytes inode)
    (rebootObjects : Nat → Nat) : NativeReadyQuietCrash state where
  live := first.files
  directoryBound := stable.directoryBound
  lockBound := stable.lockBound
  manifest := stable.manifest
  marker := stable.marker
  keeper := stable.keeper
  sealedFiles := stable.sealedFiles
  runs := stable.runs
  crashNames := first.crashNames
  settled := stable.settled
  names := names
  chosen := chosen
  contents := contents
  durable := durable
  rebootObjects := rebootObjects

end NativeReadyStorage

variable {heap : Type} {opened : NativeOpenedHandle heap} {current : NativeOpenedPosition opened}
  {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap} {fsync : CheckpointFsync heap}
  {step : Step} {reason : FilePath} {reached : CheckpointWorld heap}

/-- Keep the selected files through the phase update and the returned
source calls. The first directory barrier can use this settlement. -/
theorem NativeCheckpointSourceStop.storageAtIssue
    (stop : NativeCheckpointSourceStop current primitives fsync step reason reached)
    (observe : heap → CheckpointStorageObservation)
    (initial : NativeReadyStorage current.current.ready.state (observe current.reached))
    (phaseFrame : (observe current.reached).Frames current.current.ready.state.crashPath (observe stop.poisoned))
    (returnedKeeps : ∀ stage ∈ stop.completed, ∀ before after,
      (primitives.checkpointStepUntilStop current.current.ready.state.session.directory
        fsync stop.next stop.manifest stage).run before = .ok (.ok ()) after →
      (observe before.2).Frames current.current.ready.state.crashPath (observe after.2)) :
    NativeReadyStorage current.current.ready.state (observe stop.atIssue.2) := by
  have returned := successfulCheckpointStepsPreserve _ (fun world => observe world.2)
    (CheckpointStorageObservation.Frames current.current.ready.state.crashPath)
    (CheckpointStorageObservation.Frames.refl _) CheckpointStorageObservation.Frames.trans
    stop.completed returnedKeeps stop.returnedPrefix
  exact initial.frame (phaseFrame.trans returned)

/-- Carry the selected files through the last observed, non-returning
effect independently of any subsequent reboot. -/
theorem NativeCheckpointSourceStop.reachedStorage
    (stop : NativeCheckpointSourceStop current primitives fsync step reason reached)
    (observe : heap → CheckpointStorageObservation)
    (stable : NativeReadyStorage current.current.ready.state (observe stop.atIssue.2))
    (stoppedKeeps : (observe stop.atIssue.2).Frames current.current.ready.state.crashPath (observe reached.2)) :
    NativeReadyStorage current.current.ready.state (observe reached.2) :=
  stable.frame stoppedKeeps

end Alvoki.Storage.DiskSession
