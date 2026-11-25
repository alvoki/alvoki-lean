import Alvoki.Storage.Disk.NativeStoppedMarkerTableOpen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair CheckpointPublication

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- The opened write stops at its selected callback. Preserve the actual
outer interruption, whose reported operation differs between cuts. -/
def NativeMarkerPublicationStop.OnOpenedPhase (current : NativeOpenedPosition opened)
    {prepared : NativeReadyWritePreparation current.current.ready.state} (stop : NativeMarkerPublicationStop prepared)
    (view : OpenCloseHeapView heap FileImage) : Prop :=
  let state := current.current.ready.state
  match stop with
  | .stageWrite stopped =>
    NativePendingMarkerStageWrite current.current.ready stopped ∧
    ∃ poisoned, view.phase poisoned opened.phase = some .poisoned ∧
      ∀ flush sync rename, stopped.onOpenPhase opened flush sync rename
        (current.reached, state.cache, state.census, prepared.initial) =
          .error (prepared.stagedPath, prepared.marker) (poisoned, stopped.allocated.appendCache, stopped.reached)
  | .keeperSync stopped =>
    NativePendingKeeperSync current.current.ready stopped ∧
    ∃ poisoned, view.phase poisoned opened.phase = some .poisoned ∧
      ∀ rename, stopped.onOpenPhase opened rename (current.reached, state.cache, state.census, prepared.initial) =
        .error prepared.keeperPath (poisoned, stopped.staging.groupCache, stopped.reached)
  | .stagedSync stopped =>
    NativePendingStagedMarkerSync current.current.ready stopped ∧
    ∃ poisoned, view.phase poisoned opened.phase = some .poisoned ∧
      ∀ rename, stopped.onOpenPhase opened rename (current.reached, state.cache, state.census, prepared.initial) =
        .error prepared.stagedPath (poisoned, stopped.staging.appendCache, stopped.reached)
  | .rename stopped =>
    NativePendingMarkerRename current.current.ready stopped ∧
    ∃ poisoned, view.phase poisoned opened.phase = some .poisoned ∧
      stopped.onOpenPhase opened (current.reached, state.cache, state.census, prepared.initial) =
        .error (prepared.stagedPath, prepared.markerPath) (poisoned, stopped.synced.appendCache, stopped.reached)
  | .directorySync stopped _ _ =>
    NativePendingMarkerDirectory current.current.ready stopped ∧
    ∃ poisoned, view.phase poisoned opened.phase = some .poisoned ∧
      stopped.onOpenPhase opened (current.reached, state.cache, state.census, prepared.initial) =
        .error state.session.directory.path (poisoned, stopped.renamed.appendCache, stopped.reached)

theorem NativeMarkerPublicationStop.stopsOnOpenedPhase (current : NativeOpenedPosition opened)
    {prepared : NativeReadyWritePreparation current.current.ready.state} (stop : NativeMarkerPublicationStop prepared)
    {view : OpenCloseHeapView heap FileImage} (samePhase : view.phase = opened.contents) :
    stop.OnOpenedPhase current view := by
  cases stop with
  | stageWrite stopped =>
    obtain ⟨_, pending, poisoned, _, _, poison, issue⟩ := current.stopsWriteAtMarkerStageWrite stopped
    exact ⟨pending, poisoned, samePhase.symm ▸ poison, issue⟩
  | keeperSync stopped =>
    obtain ⟨_, pending, poisoned, _, _, poison, _, issue⟩ := current.stopsWriteAtKeeperSync stopped
    exact ⟨pending, poisoned, samePhase.symm ▸ poison, issue⟩
  | stagedSync stopped =>
    obtain ⟨_, pending, poisoned, _, _, poison, _, issue⟩ := current.stopsWriteAtStagedMarkerSync stopped
    exact ⟨pending, poisoned, samePhase.symm ▸ poison, issue⟩
  | rename stopped =>
    obtain ⟨_, pending, poisoned, _, _, poison, _, _, issue⟩ := current.stopsWriteAtMarkerRename stopped
    exact ⟨pending, poisoned, samePhase.symm ▸ poison, issue⟩
  | directorySync stopped _ _ =>
    obtain ⟨_, pending, poisoned, _, _, poison, _, _, issue⟩ := current.stopsWriteAtMarkerDirectory stopped
    exact ⟨pending, poisoned, samePhase.symm ▸ poison, issue⟩

/-- A prescribed write reaches a marker publication cut through
its original phase and callbacks. One reported survivor feeds the
matching reader of the next public open. -/
structure NativeOpenedStoppedMarkerReport (current : NativeOpenedPosition opened) (request : WriteRequest)
    (input : FilePath) (view : OpenCloseHeapView heap FileImage) (names : heap → FilePath → Option Nat)
    (bytes : heap → Nat → ByteArray) where
  prepared : NativeReadyWritePreparation current.current.ready.state
  stop : NativeMarkerPublicationStop prepared
  requestMatches : stop.request = request
  crash : NativeMarkerPublicationCrash stop
  plan : crash.Plan
  reader : NativeMarkerPublicationCrashReads crash input plan.layout plan.selected
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
  physical : RawStoppedMarkerReopenEffects reader view calls init names bytes rebooted phaseIdentity tokenIdentity
    allocatePhase allocateToken stream remove stage rename
  samePhase : view.phase = opened.contents
  bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened
  assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
    IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable
  constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files)

variable {current : NativeOpenedPosition opened} {request : WriteRequest} {input : FilePath}
  {view : OpenCloseHeapView heap FileImage} {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}

/-- The single event records the prescribed request and the recovered
rows. No acknowledgement is added for the interrupted write. -/
def NativeOpenedStoppedMarkerReport.event
    (seen : NativeOpenedStoppedMarkerReport current request input view names bytes) (retained : List WAL.Write) :
    NativeExecutionEvent :=
  .interruptedMarkerRecovered request input seen.prepared.batch retained

/-- Staging and file syncs leave the prior directory marker. A reported
effective final directory sync settles the new marker. -/
def NativeMarkerPublicationCrash.settledDirectory {state : NativeReadyState}
    {prepared : NativeReadyWritePreparation state} {stop : NativeMarkerPublicationStop prepared}
    (crash : NativeMarkerPublicationCrash stop) : Prop :=
  match stop with
  | .stageWrite _ | .keeperSync _ | .stagedSync _ => crash.usesNewMarker = false
  | .rename _ => True
  | .directorySync stopped _ _ => stopped.applied = true → crash.usesNewMarker = true

theorem NativeMarkerPublicationCrash.settledWhenEffective {state : NativeReadyState}
    {prepared : NativeReadyWritePreparation state} {stop : NativeMarkerPublicationStop prepared}
    (crash : NativeMarkerPublicationCrash stop) (valid : state.Valid) : crash.settledDirectory := by
  cases stop with
  | stageWrite _ => exact crash.oldMarkerAfterStageWrite valid
  | keeperSync _ => exact crash.oldMarkerAfterKeeperSync valid
  | stagedSync _ => exact crash.oldMarkerAfterStagedSync valid
  | rename _ => trivial
  | directorySync _ _ _ => exact crash.newMarkerAfterDirectoryEffect valid

/-- Retain one exact stopped issuance, its measured repair and its
actual returned table. The chosen marker explains both the prior
reads and the one newly recorded uncertain batch. -/
structure NativeOpenedStoppedMarkerReport.Returned
    (seen : NativeOpenedStoppedMarkerReport current request input view names bytes) (retained : List WAL.Write)
    {handle : NativeOpenedHandle heap} (start : NativeOpenedPosition handle) : Prop where
  sourceWrite : opened.table.UsesOpenWriteSchedules current.current.ready.state.session.directory opened.files opened.phase
  issue : seen.stop.OnOpenedPhase current view
  settled : seen.crash.settledDirectory
  rebootProjection : (view.descriptors seen.rebooted, view.files seen.rebooted) = (seen.crash.raw.reboot, seen.crash.retry)
  emptyCensus : (view.descriptors seen.rebooted).slots = []
  noLater : seen.crash.retry.image.later.visible = []
  tail : seen.plan.layout.tail.size = if seen.crash.usesNewMarker then 0 else seen.crash.keeperTail.size
  repair : seen.reader.RepairForTail (plan := seen.plan)
  lockObject : names seen.rebooted (current.current.ready.state.session.directory.file .lock) =
    some ((view.handle seen.physical.raw.afterFlock seen.physical.raw.lock).1.inode
      (view.handle seen.physical.raw.afterFlock seen.physical.raw.lock).2.1.description)
  directoryObject : names seen.rebooted current.current.ready.state.session.directory.path =
    some ((view.handle seen.physical.seed.afterPending seen.physical.seed.handle).1.inode
      (view.handle seen.physical.seed.afterPending seen.physical.seed.handle).2.1.description)
  markerObject : names seen.rebooted seen.prepared.markerPath = some (if seen.crash.usesNewMarker then
    current.current.ready.state.census.inode seen.stop.stageAllocation.markerSlot.description else
    seen.stop.stageAllocation.stageView.modelObject seen.stop.oldMarkerChild)
  survivorBytes : ∀ path payload, checkpointSurvivorPath current.current.ready.state.session.directory
    current.current.ready.state.writer seen.crash.pair.manifest path → seen.reader.toNativeWriteCrashReads.ReadsSurvivor path payload →
    ∃ read : seen.reader.opening.reads.reads.ObservesFile path payload,
      names seen.rebooted path = some read.object ∧ bytes seen.rebooted read.object = payload
  recovery : ∃ next : NativeReadPosition (current.current.history ++ retained)
      (current.current.submissions ++ [.uncertainBatch seen.prepared.batch]),
    NativeMarkerPublicationCrashContinuation current.current.ready seen.crash input retained next ∧
    start.current = ⟨current.current.history ++ retained,
      current.current.submissions ++ [.uncertainBatch seen.prepared.batch], next⟩
  sourceOpen : ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles),
    let directory := current.current.ready.state.session.directory
    DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
    cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
      (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
      (fun value => liftM (IO.mkRef value)) makeCache ∧
    seen.physical.openTable seen.bootstrap seen.assemble makeCache = .ok handle.table start.reached
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

/-- Each supported cut extends the common trace by one recovery event.
The same reported survivor supplies the exact next physical table. -/
theorem NativeOpenedStoppedMarkerReport.reaches
    (seen : NativeOpenedStoppedMarkerReport current request input view names bytes) :
    ∃ (retained : List WAL.Write) (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      seen.Returned retained start := by
  obtain ⟨reboot, empty, noLater, tail, repair, lockObject, directoryObject, marker, bytes, retained, next,
    cacheOpen, makeCache, handle, start, cacheAction, cacheSource, recovered, common, rawOpen, reached, lock,
    cache, directory, contents, get, set, compare, token, pins, files, census, cached⟩ :=
    seen.physical.returns current seen.samePhase seen.bootstrap seen.assemble seen.constructs
  refine ⟨retained, handle, start, current.uses.writeSchedules, seen.stop.stopsOnOpenedPhase current seen.samePhase,
    seen.crash.settledWhenEffective current.current.ready.readPrefix.refines.1,
    reboot, empty, noLater, tail, repair, lockObject, directoryObject, marker, bytes, ⟨next, recovered, reached⟩,
    ⟨cacheOpen, makeCache, cacheAction, cacheSource, rawOpen⟩, ?_, lock, cache, directory, contents, get, set,
    compare, ?_, pins, ?_, ?_, ?_⟩
  · simpa only [NativeOpenedStoppedMarkerReport.event, seen.requestMatches] using common
  · rw [reached]
    exact token
  · rw [reached]
    exact files
  · rw [reached]
    exact census
  · rw [reached]
    exact cached

end Alvoki.Storage.DiskSession
