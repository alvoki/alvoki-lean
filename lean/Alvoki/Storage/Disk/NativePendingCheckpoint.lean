import Alvoki.Storage.Disk.NativeCheckpointDirectoryError
import Alvoki.Storage.Disk.NativeReadRecoveryTrace

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting

variable {image : Type} {state : NativeReadyState}
  {cut : CheckpointPowerCut state.session.directory state.writer}

/-- Interpret one grouped sync path with the same handle resolver.
A reported interruption bypasses the ordinary sync error handler. -/
def checkpointSyncUntilStop (directory : FilePath)
    (openRead : FilePath → EStateM IO.Error image CheckpointOpenHandle)
    (fsync : CheckpointOpenHandle → EStateM FilePath image (Except IO.Error Unit))
    (path : FilePath) : ExceptT IO.Error (EStateM FilePath (CensusDirectoryCache × image)) Unit :=
  fun (cache, files) =>
    match cache.resolve directory path openRead files with
    | .error cause reached => .ok (.error cause) reached
    | .ok handle (cache, files) =>
      match fsync handle files with
      | .ok result reached => .ok result (cache, reached)
      | .error path reached => .error path (cache, reached)

theorem checkpointSyncGroupStops {directory path : FilePath} {cache selectedCache : CensusDirectoryCache}
    {openRead : FilePath → EStateM IO.Error image CheckpointOpenHandle}
    {fsync : CheckpointOpenHandle → EStateM FilePath image (Except IO.Error Unit)}
    {handle : CheckpointOpenHandle} {files reached : image}
    (resolved : cache.resolve directory path openRead files = .ok handle (selectedCache, files))
    (issued : fsync handle files = .error path reached) :
    (SyncPathGroup.run (checkpointSyncUntilStop directory openRead fsync) #[path]).run (cache, files) =
      .error path (selectedCache, reached) := by
  have stopped : checkpointSyncUntilStop directory openRead fsync path (cache, files) =
      .error path (selectedCache, reached) := by
    simp only [checkpointSyncUntilStop, resolved, issued]
  simp [SyncPathGroup.run, ← Array.forIn_toList, List.forIn_cons, List.forIn_nil, MonadExcept.tryCatch, MonadExceptOf.tryCatch,
    tryCatchThe, ExceptT.tryCatch, Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, EStateM.bind,
    StateT.pure, Pure.pure, ExceptT.pure, stopped]

theorem checkpointCachedDirectorySyncStops {directory : FilePath} {cache : CensusDirectoryCache}
    {openRead : FilePath → EStateM IO.Error image CheckpointOpenHandle}
    {fsync : CheckpointOpenHandle → EStateM FilePath image (Except IO.Error Unit)}
    {handle : CheckpointOpenHandle} {files reached : image}
    (cached : cache.directory = some handle) (issued : fsync handle files = .error directory reached) :
    (SyncPathGroup.run (checkpointSyncUntilStop directory openRead fsync) #[directory]).run (cache, files) =
      .error directory (cache, reached) :=
  checkpointSyncGroupStops (by simp only [Cache.resolve, beq_self_eq_true, ↓reduceIte, cached]) issued

/-- The issued final directory fsync stops without a native return.
The outer path identifies the interruption. Any ordinary return would
instead carry its result inside the callback. -/
structure NativeCheckpointDirectoryStop {image : Type} (state : NativeReadyState)
    (cut : CheckpointPowerCut state.session.directory state.writer) where
  barrier : NativeCheckpointFinalBarrier (image := image) state cut
  fsync : CheckpointOpenHandle → EStateM FilePath image (Except IO.Error Unit)
  reached : image
  stopped : fsync barrier.handle barrier.observed.renamed.2 = .error state.session.directory.path reached
  physical : barrier.Physical reached

namespace NativeCheckpointDirectoryStop

variable (stop : NativeCheckpointDirectoryStop (image := image) state cut)

def session (_stop : NativeCheckpointDirectoryStop (image := image) state cut) : SegmentedSession := { state.session with phase := .poisoned }

/-- Route the actual grouped sync up to its stopped primitive, keeping
a reported interruption separate from the public checkpoint error. -/
def syncPath (path : FilePath) :
    ExceptT IO.Error (EStateM FilePath (CensusDirectoryCache × image)) Unit :=
  checkpointSyncUntilStop state.session.directory.path stop.barrier.callbackPrefix.primitives.openRead stop.fsync path

theorem stopsGroup :
    (SyncPathGroup.run stop.syncPath #[state.session.directory.path]).run stop.barrier.observed.renamed =
      .error state.session.directory.path (state.cache, stop.reached) := by
  have atIssue : stop.barrier.observed.renamed = (state.cache, stop.barrier.observed.renamed.2) :=
    Prod.ext stop.barrier.callbackPrefix.beforeFinalDirectory.1 rfl
  have cached : state.cache.directory = some stop.barrier.handle := stop.barrier.callbackPrefix.directoryCached
  calc
    _ = (SyncPathGroup.run stop.syncPath #[state.session.directory.path]).run
        (state.cache, stop.barrier.observed.renamed.2) := congrArg _ atIssue
    _ = _ := checkpointCachedDirectorySyncStops cached stop.stopped

/-- The previous session remains poisoned at the issued callback.
Acquisition and reads through its original references see that phase. -/
theorem rejectsReads (sequence : UInt64) (sameSession : Bool) (read : PackedTable → Option α)
    (stop : NativeCheckpointDirectoryStop (image := image) state cut) :
    stop.session.sessionRef = state.session.sessionRef ∧ stop.session.phaseRef = state.session.phaseRef ∧
    stop.session.runAcquireAt sequence = .error (IO.userError "publication failed; reopen the database") stop.session ∧
    stop.session.runSnapshotRead sameSession read =
      .error (IO.userError "publication failed; reopen the database") stop.session :=
  ⟨rfl, rfl, rfl, SegmentedSession.runSnapshotRead_poisoned rfl sameSession read⟩

end NativeCheckpointDirectoryStop

/-- A native execution endpoint at an issued final checkpoint sync.
The proof retains the original lock and cache at issue, the reached
physical choice, and the client replay without completing the call. -/
structure NativePendingCheckpoint (current : NativeReadPosition history log)
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    (stop : NativeCheckpointDirectoryStop (image := image) current.state cut) : Prop where
  issued : CheckpointIssue stop.barrier.perform current.state.session.phase stop.barrier.entry
    cut.checkpoint.prepared cut.checkpoint.manifest cut.completed (.manifest .syncDirectory) stop.barrier.observed.renamed
  routing : let atDirectory : FilePath → EStateM IO.Error (CensusDirectoryCache × image) Unit :=
      fun _ (cache, files) => withCache cache (stop.barrier.callbackPrefix.primitives.fsync stop.barrier.handle files)
    stop.barrier.perform cut.checkpoint.prepared cut.checkpoint.manifest (.manifest .syncDirectory)
      stop.barrier.observed.renamed = SyncPathGroup.run atDirectory #[current.state.session.directory.path]
        stop.barrier.observed.renamed
  stopped : (SyncPathGroup.run stop.syncPath #[current.state.session.directory.path]).run stop.barrier.observed.renamed =
    .error current.state.session.directory.path (current.state.cache, stop.reached)
  phase : stop.session.phase = .poisoned
  cache : stop.barrier.observed.renamed.1 = current.state.cache
  census : stop.barrier.callbackPrefix.descriptors stop.barrier.observed.renamed.2 = current.state.census
  directoryLive : current.state.directorySlot ∈ (stop.barrier.callbackPrefix.descriptors stop.barrier.observed.renamed.2).slots
  lockLive : current.state.owner ∈ (stop.barrier.callbackPrefix.descriptors stop.barrier.observed.renamed.2).slots
  held : stop.barrier.entry.owners.Owns current.state.session.directory current.state.session.descriptor
  directoryObject : stop.barrier.bindings stop.barrier.observed.renamed.2 current.state.session.directory.path =
    some (stop.barrier.handle.1.inode current.state.directorySlot.description)
  lockObject : stop.barrier.bindings stop.barrier.observed.renamed.2 (current.state.session.directory.file .lock) =
    some (current.state.census.inode current.state.owner.description)
  wal : CheckpointWalView.ofFiles (stop.physical.files stop.reached) = CheckpointWalView.ofFiles current.state.files.image
  survivors : ∀ pair ∈ (stop.physical.files stop.reached).directory.crashImages,
    pair.walBoundary = current.state.writer.wal.directory.active.walBoundary ∧
      cut.PendingReplay (stop.physical.runs stop.reached) pair.manifest log current.reads
  reads : PendingClientReplay log current.reads history
  bounded : ∀ read ∈ current.reads, read.BoundedBy history.length

theorem NativeReadPosition.stopsDuringCheckpoint (current : NativeReadPosition history log)
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    (stop : NativeCheckpointDirectoryStop (image := image) current.state cut) :
    NativePendingCheckpoint current stop := by
  obtain ⟨valid, history, replay⟩ := current.readPrefix.refines
  obtain ⟨census, directoryLive, lockLive, directoryObject, lockObject⟩ :=
    (stop.barrier.custody valid).2 stop.barrier.observed.renamed.2 (by simp)
  exact ⟨stop.barrier.issues valid, stop.barrier.routes, stop.stopsGroup, rfl,
    stop.barrier.callbackPrefix.beforeFinalDirectory.1, census, directoryLive, lockLive, valid.retained.held,
    directoryObject, lockObject, stop.physical.wal,
    fun _ survived => stop.physical.replaysSurvivor valid (history.symm ▸ replay) survived, replay,
    current.readPrefix.readsBounded⟩

end Alvoki.Storage.DiskSession
