import Alvoki.Storage.Disk.Proofs.Append.NativeStoppedFirstAppendTableOpen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair CheckpointPublication

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- The original raw append stops at one poisoned heap. The remaining
publication callbacks cannot affect that result. -/
theorem NativeFirstAppendStop.stopsBeforeSuffix (current : NativeOpenedPosition opened)
    {prepared : NativeReadyWritePreparation current.current.ready.state} (stop : NativeFirstAppendStop prepared)
    {view : OpenCloseHeapView heap FileImage} (samePhase : view.phase = opened.contents) :
    let state := current.current.ready.state
    stop.rawWrite stop.handle (WAL.encodeBatch prepared.batch) (stop.selectedCensus, prepared.initial) =
      .error stop.logical.appendCall stop.cutFiles ∧
    ∃ poisoned, opened.set opened.phase .poisoned current.reached = .ok () poisoned ∧
      view.phase poisoned opened.phase = some .poisoned ∧
      ∀ (flush : CheckpointOpenHandle → FirstAppendInterrupted Unit)
        (stage : FilePath → ByteArray → FirstAppendInterrupted Unit)
        (sync : Array FilePath → FirstAppendInterrupted Unit) (rename : FilePath → FilePath → FirstAppendInterrupted Unit),
        stop.onOpenPhase opened flush stage sync rename (current.reached, state.cache, state.census, prepared.initial) =
          .error stop.logical.appendCall (poisoned, state.cache, stop.cutFiles) := by
  intro state
  obtain ⟨_, _, poisoned, _, wrote, poison, issued, _⟩ := current.stopsWriteAtFirstAppend stop
    (fun _ => pure ()) (fun _ _ => pure ()) (fun _ => pure ()) (fun _ _ => pure ())
  refine ⟨issued, poisoned, wrote, samePhase.symm ▸ poison, ?_⟩
  intro flush stage sync rename
  obtain ⟨_, _, sameHeap, _, otherWrite, _, _, stopped⟩ := current.stopsWriteAtFirstAppend stop flush stage sync rename
  have same := (EStateM.Result.ok.inj (wrote.symm.trans otherWrite)).2
  rw [same]
  exact stopped

/-- The prescribed opened write stops at its first keeper append. One
reported reboot with the original marker supplies the next raw open. -/
structure NativeOpenedFirstAppendReport (current : NativeOpenedPosition opened) (request : WriteRequest)
    (input : FilePath) (view : OpenCloseHeapView heap FileImage) (names : heap → FilePath → Option Nat)
    (bytes : heap → Nat → ByteArray) where
  prepared : NativeReadyWritePreparation current.current.ready.state
  stop : NativeFirstAppendStop prepared
  requestMatches : stop.request = request
  crash : NativeFirstAppendCrash stop
  plan : crash.Plan
  reader : NativeFirstAppendCrashReads crash input plan.layout plan.selected
  rebooted : heap
  calls : RawOpenAdmissionCallbacks heap
  init : OpenSyncCacheCallbacks heap
  stream : Type
  phaseIdentity : IO.Ref (Phase Installed) → Nat
  tokenIdentity : IO.Ref Unit → Nat
  allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))
  allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)
  remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)
  stage : LongKeeperStageCallbacks heap
  rename : FilePath → FilePath → EStateM IO.Error heap Unit
  physical : RawStoppedFirstAppendReopenEffects reader view calls init names bytes rebooted phaseIdentity tokenIdentity
    allocatePhase allocateToken stream remove stage rename
  samePhase : view.phase = opened.contents
  bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened
  assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
    IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable
  constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files)

variable {current : NativeOpenedPosition opened} {request : WriteRequest} {input : FilePath}
  {view : OpenCloseHeapView heap FileImage} {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}

/-- The original request and uncertain batch occupy one event. The
unchanged marker keeps the original history. -/
def NativeOpenedFirstAppendReport.event (seen : NativeOpenedFirstAppendReport current request input view names bytes) :
    NativeExecutionEvent :=
  .interruptedAppendCrashRecovered request input seen.prepared.batch

/-- Retain one exact issued append and its observed restored table.
The same captured checkpoint and WAL supply the prior client replay. -/
structure NativeOpenedFirstAppendReport.Returned (seen : NativeOpenedFirstAppendReport current request input view names bytes)
    {handle : NativeOpenedHandle heap} (start : NativeOpenedPosition handle) : Prop where
  sourceWrite : opened.table.UsesOpenWriteSchedules current.current.ready.state.session.directory opened.files opened.phase
  pending : NativePendingFirstAppend current.current.ready seen.stop
  issued : seen.stop.rawWrite seen.stop.handle (WAL.encodeBatch seen.prepared.batch)
    (seen.stop.selectedCensus, seen.prepared.initial) = .error seen.stop.logical.appendCall seen.stop.cutFiles
  interrupted :
    let state := current.current.ready.state
    ∃ poisoned, opened.set opened.phase .poisoned current.reached = .ok () poisoned ∧
      view.phase poisoned opened.phase = some .poisoned ∧
      ∀ (flush : CheckpointOpenHandle → FirstAppendInterrupted Unit)
        (stage : FilePath → ByteArray → FirstAppendInterrupted Unit)
        (sync : Array FilePath → FirstAppendInterrupted Unit) (rename : FilePath → FilePath → FirstAppendInterrupted Unit),
        seen.stop.onOpenPhase opened flush stage sync rename (current.reached, state.cache, state.census, seen.prepared.initial) =
          .error seen.stop.logical.appendCall (poisoned, state.cache, seen.stop.cutFiles)
  rebootProjection : (view.descriptors seen.rebooted, view.files seen.rebooted) = (seen.crash.raw.reboot, seen.crash.retry)
  emptyCensus : (view.descriptors seen.rebooted).slots = []
  noLater : seen.crash.retry.image.later.visible = []
  repair : seen.reader.opening.finish.UsesMeasuredRepair
  lockObject : names seen.rebooted (current.current.ready.state.session.directory.file .lock) =
    some ((view.handle seen.physical.raw.afterFlock seen.physical.raw.lock).1.inode
      (view.handle seen.physical.raw.afterFlock seen.physical.raw.lock).2.1.description)
  directoryObject : names seen.rebooted current.current.ready.state.session.directory.path =
    some ((view.handle seen.physical.seed.afterPending seen.physical.seed.handle).1.inode
      (view.handle seen.physical.seed.afterPending seen.physical.seed.handle).2.1.description)
  markerObject : names seen.rebooted seen.prepared.markerPath = some (seen.stop.view.modelObject seen.stop.marker.child)
  keeperObject : names seen.rebooted seen.prepared.keeperPath = some (seen.stop.view.modelObject seen.stop.keeper.child)
  survivorBytes : ∀ path payload, checkpointSurvivorPath current.current.ready.state.session.directory
    current.current.ready.state.writer seen.crash.retry.image.directory.active.manifest path →
    seen.reader.toNativeWriteCrashReads.ReadsSurvivor path payload →
    ∃ read : seen.reader.opening.reads.reads.ObservesFile path payload,
      names seen.rebooted path = some read.object ∧ bytes seen.rebooted read.object = payload
  recovery : ∃ next : NativeReadPosition current.current.history (current.current.submissions ++ [.uncertainBatch seen.prepared.batch]),
    NativeFirstAppendCrashContinuation current.current.ready seen.crash input next ∧
    start.current = ⟨current.current.history, current.current.submissions ++ [.uncertainBatch seen.prepared.batch], next⟩
  sourceOpen : ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles),
    let directory := current.current.ready.state.session.directory
    DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
    cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
      (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
      (fun value => liftM (IO.mkRef value)) makeCache ∧
    seen.physical.toRawHealthyMarkedOpenEffects.openTable seen.bootstrap seen.assemble makeCache = .ok handle.table start.reached
  common : NativeExecutionStep current.current seen.event start.current
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

/-- The same reported crash survivor produces the actual public table
for the next finite action. The interrupted write has no response. -/
theorem NativeOpenedFirstAppendReport.reaches (seen : NativeOpenedFirstAppendReport current request input view names bytes) :
    ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle), seen.Returned start := by
  obtain ⟨issued, stopped⟩ := seen.stop.stopsBeforeSuffix current seen.samePhase
  obtain ⟨source, pending, _, reboot, empty, noLater, repair, lockObject, directoryObject, marker, keeper, bytes,
    next, cacheOpen, makeCache, handle, start, cacheAction, cacheSource, recovered, common, rawOpen, reached, lock,
    cache, directory, contents, get, set, compare, token, pins, files, census, cached⟩ :=
    current.opensAfterStoppedFirstAppend seen.physical seen.samePhase (fun _ => pure ()) (fun _ _ => pure ())
      (fun _ => pure ()) (fun _ _ => pure ()) seen.bootstrap seen.assemble seen.constructs
  refine ⟨handle, start, source, pending, issued, stopped, reboot, empty, noLater, repair, lockObject, directoryObject,
    marker, keeper, bytes, ⟨next, recovered, reached⟩, ⟨cacheOpen, makeCache, cacheAction, cacheSource, rawOpen⟩,
    ?_, lock, cache, directory, contents, get, set, compare, ?_, pins, ?_, ?_, ?_⟩
  · simpa only [NativeOpenedFirstAppendReport.event, seen.requestMatches] using common
  · rw [reached]
    exact token
  · rw [reached]
    exact files
  · rw [reached]
    exact census
  · rw [reached]
    exact cached

end Alvoki.Storage.DiskSession
