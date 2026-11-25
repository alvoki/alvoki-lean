import Alvoki.Storage.Disk.NativeUncertainWriteTableOpen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair CheckpointPublication

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- The prescribed write returns `commitUnknown` on the current table.
A reported power loss and its aligned reader determine the next table. -/
structure NativeOpenedUncertainWriteReport (current : NativeOpenedPosition opened) (request : WriteRequest)
    (input : FilePath) (view : OpenCloseHeapView heap FileImage) (names : heap → FilePath → Option Nat)
    (bytes : heap → Nat → ByteArray) where
  observed : NativeUncertainWriteCrashObservation current.current.ready.state input
  requestMatches : observed.write.request = request
  finish : CapturedAlignedFinish observed.effects.reader.opening.callbacks observed.effects.reader.opening.reads
    observed.effects.crash.vacant observed.effects.plan.selected
  aligned : observed.effects.reader.opening.finish = .aligned finish
  cause : IO.Error
  failed : heap
  failedFiles : OpenWriteFiles
  returned :
    let state := current.current.ready.state
    request.runOnOpenPhase state.session.directory observed.write.openCalls opened.phase opened.get opened.set
      (current.reached, (WriteRequest.readyCall state.writer state.cache).2.image) =
      .error (.commitUnknown cause) (failed, failedFiles)
  rebooted : heap
  calls : RawOpenAdmissionCallbacks heap
  init : OpenSyncCacheCallbacks heap
  stream : Type
  phaseIdentity : IO.Ref (Phase Installed) → Nat
  tokenIdentity : IO.Ref Unit → Nat
  allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))
  allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)
  physical : RawUncertainWriteReopenEffects observed finish aligned view calls init names bytes failed rebooted
    phaseIdentity tokenIdentity allocatePhase allocateToken stream
  samePhase : view.phase = opened.contents
  remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)
  write : FilePath → ByteArray → EStateM IO.Error heap Unit
  rename : FilePath → FilePath → EStateM IO.Error heap Unit
  bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened
  assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
    IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable
  constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files)

variable {current : NativeOpenedPosition opened} {request : WriteRequest} {input : FilePath}
  {view : OpenCloseHeapView heap FileImage} {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}

/-- The event records the original request and diagnostic, the uncertain
batch and the rows selected by the surviving marker. -/
def NativeOpenedUncertainWriteReport.event (seen : NativeOpenedUncertainWriteReport current request input view names bytes)
    (retained : List WAL.Write) : NativeExecutionEvent :=
  .uncertainWriteCrashRecovered request input seen.cause seen.observed.write.failure.batch retained

/-- The exact aligned return starts the next session at the new table.
Its history, submissions and reads come from the same reported write and open. -/
structure NativeOpenedUncertainWriteReport.Returned
    (seen : NativeOpenedUncertainWriteReport current request input view names bytes) (retained : List WAL.Write)
    {handle : NativeOpenedHandle heap} (start : NativeOpenedPosition handle) : Prop where
  sourceWrite : opened.table.UsesOpenWriteSchedules current.current.ready.state.session.directory opened.files opened.phase
  cause : seen.cause = seen.observed.write.failure.cause
  failedFiles : seen.failedFiles = (seen.observed.cache, seen.observed.write.failure.failed)
  poisoned : view.phase seen.failed opened.phase = some .poisoned
  failedProjection : (view.descriptors seen.failed, view.files seen.failed) =
    (seen.observed.effects.census.reached, ⟨seen.observed.write.failure.released.image, current.current.ready.state.writer.owners⟩)
  rebootProjection : (view.descriptors seen.rebooted, view.files seen.rebooted) =
    (seen.observed.effects.crash.reboot, seen.observed.effects.crash.retry)
  emptyCensus : (view.descriptors seen.rebooted).slots = []
  lockObject : names seen.rebooted (current.current.ready.state.session.directory.file .lock) =
    some ((view.handle seen.physical.raw.afterFlock seen.physical.raw.lock).1.inode
      (view.handle seen.physical.raw.afterFlock seen.physical.raw.lock).2.1.description)
  directoryObject : names seen.rebooted current.current.ready.state.session.directory.path =
    some ((view.handle seen.physical.seed.afterPending seen.physical.seed.handle).1.inode
      (view.handle seen.physical.seed.afterPending seen.physical.seed.handle).2.1.description)
  survivorBytes : ∀ path payload, checkpointSurvivorPath current.current.ready.state.session.directory
    current.current.ready.state.writer seen.observed.effects.crash.retry.image.directory.active.manifest path →
    seen.observed.effects.reader.ReadsSurvivor path payload →
    ∃ read : seen.observed.effects.reader.opening.reads.reads.ObservesFile path payload,
      names seen.rebooted path = some read.object ∧ bytes seen.rebooted read.object = payload
  recovery : ∃ next : NativeReadPosition (current.current.history ++ retained)
      (current.current.submissions ++ [.uncertainBatch seen.observed.write.failure.batch]),
    NativeUncertainWriteCrashContinuation current.current.ready seen.observed retained next ∧
    start.current = ⟨current.current.history ++ retained,
      current.current.submissions ++ [.uncertainBatch seen.observed.write.failure.batch], next⟩
  sourceOpen : ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles),
    let directory := current.current.ready.state.session.directory
    DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
    cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
      (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
      (fun value => liftM (IO.mkRef value)) makeCache ∧
    seen.physical.toRawAlignedCheckpointReopenEffects.openTable seen.remove seen.write seen.rename
      seen.bootstrap seen.assemble makeCache = .ok handle.table start.reached
  common : NativeExecutionStep current.current (seen.event retained) start.current
  lock : handle.lock = seen.physical.raw.lock
  cache : handle.files.UsesCacheReferences seen.physical.seed.activeRef seen.physical.seed.pendingRef
    seen.physical.seed.directoryRef
  cacheDirectory : handle.files.AtDirectory current.current.ready.state.session.directory.path
  contents : handle.contents = view.phase
  get : handle.get = opened.get
  set : handle.set = opened.set
  ptrEq : handle.ptrEq = opened.ptrEq
  token : seen.tokenIdentity handle.token = start.current.ready.state.session.sessionRef
  unpinned : start.pins = []
  files : view.files start.reached = start.current.ready.state.files
  census : view.descriptors start.reached = start.current.ready.state.census
  cached : view.cacheAt start.reached seen.physical.seed.directoryRef seen.physical.seed.activeRef
    seen.physical.seed.pendingRef = start.current.ready.state.cache

/-- Extend the trace with the returned write and its recovery as one common
step. The actual reopened table and selected rows are derived together. -/
theorem NativeOpenedUncertainWriteReport.reaches
    (seen : NativeOpenedUncertainWriteReport current request input view names bytes) :
    ∃ (retained : List WAL.Write) (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      seen.Returned retained start := by
  have returned :
      let state := current.current.ready.state
      seen.observed.write.request.runOnOpenPhase state.session.directory seen.observed.write.openCalls
        opened.phase opened.get opened.set
        (current.reached, (WriteRequest.readyCall state.writer state.cache).2.image) =
        .error (.commitUnknown seen.cause) (seen.failed, seen.failedFiles) := by
    simpa only [seen.requestMatches] using seen.returned
  obtain ⟨source, cause, failedFiles, poisoned, failedProjection, rebootProjection, emptyCensus, lockObject,
    directoryObject, surviving, retained, next, cacheOpen, makeCache, handle, start, cacheAction, cacheSource,
    recovered, common, rawOpen, reached, lock, cache, directory, contents, get, set, compare, token, pins, files,
    census, cached⟩ := current.opensAfterUncertainWrite seen.physical returned seen.samePhase seen.remove seen.write
      seen.rename seen.bootstrap seen.assemble seen.constructs
  refine ⟨retained, handle, start, source, cause, failedFiles, poisoned, failedProjection, rebootProjection,
    emptyCensus, lockObject, directoryObject, surviving, ⟨next, recovered, reached⟩,
    ⟨cacheOpen, makeCache, cacheAction, cacheSource, rawOpen⟩, ?_, lock, cache, directory, contents, get, set,
    compare, ?_, pins, ?_, ?_, ?_⟩
  · simpa only [NativeOpenedUncertainWriteReport.event, seen.requestMatches] using common
  · rw [reached]
    exact token
  · rw [reached]
    exact files
  · rw [reached]
    exact census
  · rw [reached]
    exact cached

end Alvoki.Storage.DiskSession
