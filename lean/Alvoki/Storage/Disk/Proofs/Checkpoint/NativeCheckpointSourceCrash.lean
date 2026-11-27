import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointFsyncEffects
import Alvoki.Storage.Disk.NativeReadyPowerLoss

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting

/-- Paths that a WAL append and marker publication must preserve.
The active keeper and commit marker are established by the write. -/
def NativeReadyState.writeFramePath (state : NativeReadyState) (path : FilePath) : Prop :=
  let directory := state.session.directory
  path = directory.path ∨ path = directory.file .lock ∨ path = directory.file .manifest ∨
  (∃ segment ∈ state.writer.wal.sealed, path = directory.file (.walSegment segment.first)) ∨
  ∃ bytes metadata index, state.writer.target.pair.manifest = some bytes ∧
    Manifest.IntegrityCheckpoint.decode bytes = .ok metadata ∧ index < metadata.header.runCount.toNat ∧
    path = directory.file (.run metadata.header.generation index)

theorem NativeReadyState.crashPath_iff_write {state : NativeReadyState} {path : FilePath} :
    state.crashPath path ↔ path = state.session.directory.file .walBoundary ∨
      path = state.session.directory.file (.walSegment state.writer.wal.active.first) ∨ state.writeFramePath path := by
  simp only [crashPath, checkpointSurvivorPath, checkpointWalPath, writeFramePath, or_left_comm, or_comm]

/-- The recovery bindings and bytes that an ordinary WAL write keeps. -/
structure NativeReadyProtectedStorage (state : NativeReadyState) (files : CheckpointSurvivingFiles) : Prop where
  directoryBound : files.names state.session.directory.path = some (state.census.inode state.directorySlot.description)
  lockBound : files.names (state.session.directory.file .lock) = some (state.census.inode state.owner.description)
  manifest : match state.writer.target.pair.manifest with
    | none => files.names (state.session.directory.file .manifest) = none
    | some bytes => files.Stored (state.session.directory.file .manifest) bytes
  sealedFiles : ∀ segment ∈ state.writer.wal.sealed,
    files.Stored (state.session.directory.file (.walSegment segment.first)) segment.bytes
  runs : ∀ bytes metadata, state.writer.target.pair.manifest = some bytes →
    Manifest.IntegrityCheckpoint.decode bytes = .ok metadata → ∀ index < metadata.header.runCount.toNat,
    ∀ payload, state.writer.published.durable metadata.header.generation index = some payload →
    files.Stored (state.session.directory.file (.run metadata.header.generation index)) payload

/-- The selected files of a ready table before any survivor is chosen. -/
structure NativeReadyStorage (state : NativeReadyState) (storage : CheckpointStorageObservation) : Prop
    extends NativeReadyProtectedStorage state storage.files where
  marker : storage.files.Stored (state.session.directory.file .walBoundary)
    (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64)
  keeper : storage.files.Stored (state.session.directory.file (.walSegment state.writer.wal.active.first)) state.writer.wal.active.bytes
  settled : ∀ names ∈ storage.crashNames, ∀ path, state.crashPath path → names path = storage.files.names path

/-- The two names used to acquire the directory and lock on the next open. -/
structure RebootDirectoryBindings (state : NativeReadyState) (names : FilePath → Option Nat) : Prop where
  directory : names state.session.directory.path = some (state.census.inode state.directorySlot.description)
  lock : names (state.session.directory.file .lock) = some (state.census.inode state.owner.description)

/-- Protected regular files need their names and byte choices preserved.
The held directory's own binding needs no byte observation. -/
theorem NativeReadyProtectedStorage.frameChildren
    {state : NativeReadyState} {first last : CheckpointSurvivingFiles}
    (initial : NativeReadyProtectedStorage state first)
    (directoryBound : last.names state.session.directory.path =
      some (state.census.inode state.directorySlot.description))
    (frame : first.Frames (fun path => state.writeFramePath path ∧
      ∃ file, path = state.session.directory.file file) last) :
    NativeReadyProtectedStorage state last := by
  refine ⟨directoryBound, (frame _ ⟨.inr (.inl rfl), .lock, rfl⟩).1.trans initial.lockBound, ?_, ?_, ?_⟩
  · have manifest := initial.manifest
    cases selected : state.writer.target.pair.manifest with
    | none =>
      rw [selected] at manifest
      exact (frame _ ⟨.inr (.inr (.inl rfl)), .manifest, rfl⟩).1.trans manifest
    | some bytes =>
      rw [selected] at manifest
      exact frame.stored ⟨.inr (.inr (.inl rfl)), .manifest, rfl⟩ manifest
  · intro segment member
    exact frame.stored ⟨.inr (.inr (.inr (.inl ⟨segment, member, rfl⟩))), .walSegment segment.first, rfl⟩
      (initial.sealedFiles segment member)
  · intro bytes metadata manifest decoded index within payload bound
    exact frame.stored ⟨.inr (.inr (.inr (.inr ⟨bytes, metadata, index, manifest, decoded, within, rfl⟩))),
      .run metadata.header.generation index, rfl⟩
      (initial.runs bytes metadata manifest decoded index within payload bound)

theorem NativeReadyProtectedStorage.frame {state : NativeReadyState} {first last : CheckpointSurvivingFiles}
    (initial : NativeReadyProtectedStorage state first) (frame : first.Frames state.writeFramePath last) :
    NativeReadyProtectedStorage state last :=
  initial.frameChildren ((frame _ (.inl rfl)).1.trans initial.directoryBound)
    (fun path kept => frame path kept.1)

/-- An inode kept in the chosen map supplies its singleton durable payload. -/
theorem CheckpointSurvivingFiles.Stored.samplesAtBinding {files : CheckpointSurvivingFiles}
    {path : FilePath} {payload : ByteArray} (stored : files.Stored path payload)
    (names : FilePath → Option Nat) (contents : Nat → ByteArray) (kept : names path = files.names path)
    (sampled : ∀ inode, names path = some inode → contents inode ∈ files.bytes inode) :
    ∃ inode, names path = some inode ∧ contents inode = payload := by
  obtain ⟨inode, bound, durable⟩ := stored
  have survived := kept.trans bound
  exact ⟨inode, survived, List.mem_singleton.mp (durable ▸ sampled inode survived)⟩

/-- Sample the immutable files through one namespace. The same scope
retains a missing manifest, the root and lock, and the files that the
selected manifest and sealed WAL reference. -/
theorem NativeReadyProtectedStorage.samplesRebootFiles {state : NativeReadyState} {files : CheckpointSurvivingFiles}
    (protectedFiles : NativeReadyProtectedStorage state files)
    (names : FilePath → Option Nat) (contents : Nat → ByteArray)
    (kept : ∀ path, state.writeFramePath path → names path = files.names path)
    (sampled : ∀ path, checkpointSurvivorPath state.session.directory state.writer
        state.writer.target.pair.manifest path →
      ∀ inode, names path = some inode → contents inode ∈ files.bytes inode) :
    NativeReadyProtectedStorage state ⟨names, fun inode => [contents inode]⟩ ∧
      (names (state.session.directory.file .manifest)).map contents = state.writer.target.pair.manifest := by
  let directory := state.session.directory
  let rebootFiles : CheckpointSurvivingFiles := ⟨names, fun inode => [contents inode]⟩
  have sample {path payload} (protectedPath : state.writeFramePath path)
      (sourcePath : checkpointSurvivorPath directory state.writer state.writer.target.pair.manifest path)
      (stored : files.Stored path payload) : rebootFiles.Stored path payload := by
    obtain ⟨inode, bound, bytes⟩ := stored.samplesAtBinding names contents (kept path protectedPath) (sampled path sourcePath)
    exact ⟨inode, bound, congrArg List.singleton bytes⟩
  have manifest : (match state.writer.target.pair.manifest with
        | none => names (directory.file .manifest) = none
        | some payload => rebootFiles.Stored (directory.file .manifest) payload) ∧
      (names (directory.file .manifest)).map contents = state.writer.target.pair.manifest := by
    have original := protectedFiles.manifest
    have binding := kept (directory.file .manifest) (.inr (.inr (.inl rfl)))
    cases selected : state.writer.target.pair.manifest with
    | none =>
      rw [selected] at original
      exact ⟨binding.trans original, by rw [binding, original]; rfl⟩
    | some payload =>
      rw [selected] at original
      obtain ⟨inode, survives, bytes⟩ := original.samplesAtBinding names contents binding (sampled _ (.inl rfl))
      exact ⟨⟨inode, survives, congrArg List.singleton bytes⟩, by rw [survives, Option.map_some, bytes]⟩
  refine ⟨⟨(kept _ (.inl rfl)).trans protectedFiles.directoryBound,
    (kept _ (.inr (.inl rfl))).trans protectedFiles.lockBound, manifest.1, ?_, ?_⟩, manifest.2⟩
  · intro segment member
    exact sample (.inr (.inr (.inr (.inl ⟨segment, member, rfl⟩))))
      (.inr (.inl (.inr (.inr ⟨segment, member, rfl⟩)))) (protectedFiles.sealedFiles segment member)
  · intro bytes metadata binding decoded index within payload stored
    exact sample (.inr (.inr (.inr (.inr ⟨bytes, metadata, index, binding, decoded, within, rfl⟩))))
      (.inr (.inr ⟨bytes, metadata, index, binding, decoded, within, rfl⟩))
      (protectedFiles.runs bytes metadata binding decoded index within payload stored)

namespace NativeReadyStorage

variable {state : NativeReadyState} {first last : CheckpointStorageObservation}

/-- A private checkpoint prefix preserves the previously committed
footprint. Each surviving map is traced back jointly. -/
theorem frame (initial : NativeReadyStorage state first) (frame : first.Frames state.crashPath last) :
    NativeReadyStorage state last := by
  have included : ∀ path, state.writeFramePath path → state.crashPath path :=
    fun _ kept => NativeReadyState.crashPath_iff_write.mpr (.inr (.inr kept))
  refine ⟨initial.toNativeReadyProtectedStorage.frame (frame.weaken included).visible,
    frame.visible.stored (NativeReadyState.crashPath_iff_write.mpr (.inl rfl)) initial.marker,
    frame.visible.stored (NativeReadyState.crashPath_iff_write.mpr (.inr (.inl rfl))) initial.keeper,
    frame.settledFrom initial.settled⟩

/-- One chosen map retains every previously settled path in the frame. -/
theorem chosenBinding (initial : NativeReadyStorage state first) {scope : FilePath → Prop}
    (frame : first.Frames scope last) (names : FilePath → Option Nat) (chosen : names ∈ last.crashNames)
    {path : FilePath} (kept : scope path) (settled : state.crashPath path) :
    names path = first.files.names path := by
  have retained := frame.weaken (scope := fun path => scope path ∧ state.crashPath path) (fun _ both => both.1)
  exact (retained.settledFrom (fun prior possible path both => initial.settled prior possible path both.2)
    names chosen path ⟨kept, settled⟩).trans (frame.visible path kept).1

/-- Sampling a retained regular file picks the same inode and its exact
settled payload. No assumption about other names or files is needed. -/
theorem sampleFile (initial : NativeReadyStorage state first) {scope : FilePath → Prop}
    (frame : first.Frames scope last) {path : FilePath} (kept : scope path) (settled : state.crashPath path)
    {payload : ByteArray} (stored : first.files.Stored path payload)
    (names : FilePath → Option Nat) (chosen : names ∈ last.crashNames) (contents : Nat → ByteArray)
    (sampled : ∀ inode, names path = some inode → contents inode ∈ last.files.bytes inode) :
    ∃ inode, first.files.names path = some inode ∧ names path = some inode ∧ contents inode = payload := by
  have binding := initial.chosenBinding frame names chosen kept settled
  have retained := frame.visible.stored kept stored
  obtain ⟨inode, survives, bytes⟩ := retained.samplesAtBinding names contents
    (binding.trans (frame.visible path kept).1.symm) sampled
  exact ⟨inode, binding.symm.trans survives, survives, bytes⟩

theorem rebootDirectoryBindings (initial : NativeReadyStorage state first) {scope : FilePath → Prop}
    (frame : first.Frames scope last) (names : FilePath → Option Nat) (chosen : names ∈ last.crashNames)
    (directory : scope state.session.directory.path) (lock : scope (state.session.directory.file .lock)) :
    RebootDirectoryBindings state names :=
  ⟨(initial.chosenBinding frame names chosen directory (.inl rfl)).trans initial.directoryBound,
    (initial.chosenBinding frame names chosen lock (.inr (.inl rfl))).trans initial.lockBound⟩

/-- The same chosen map supplies the marker, active keeper and each seal
even if the selected manifest has changed. -/
theorem samplesWal (initial : NativeReadyStorage state first) {scope : FilePath → Prop}
    (frame : first.Frames scope last)
    (kept : ∀ path, checkpointWalPath state.session.directory state.writer path → scope path)
    (names : FilePath → Option Nat) (chosen : names ∈ last.crashNames) (contents : Nat → ByteArray)
    (sampled : ∀ path, checkpointWalPath state.session.directory state.writer path →
      ∀ inode, names path = some inode → contents inode ∈ last.files.bytes inode) :
    let files : CheckpointSurvivingFiles := ⟨names, fun inode => [contents inode]⟩
    files.Stored (state.session.directory.file .walBoundary)
        (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64) ∧
    files.Stored (state.session.directory.file (.walSegment state.writer.wal.active.first))
        state.writer.wal.active.bytes ∧
    ∀ segment ∈ state.writer.wal.sealed,
      files.Stored (state.session.directory.file (.walSegment segment.first)) segment.bytes := by
  intro files
  have sample {path payload} (wal : checkpointWalPath state.session.directory state.writer path)
      (stored : first.files.Stored path payload) : files.Stored path payload := by
    obtain ⟨inode, _, named, bytes⟩ := initial.sampleFile frame (kept path wal) (.inr (.inr (.inr (.inl wal))))
      stored names chosen contents (sampled path wal)
    exact ⟨inode, named, congrArg (fun payload => [payload]) bytes⟩
  exact ⟨sample (.inl rfl) initial.marker, sample (.inr (.inl rfl)) initial.keeper,
    fun segment member => sample (.inr (.inr ⟨segment, member, rfl⟩)) (initial.sealedFiles segment member)⟩

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

end Alvoki.Storage.DiskSession
