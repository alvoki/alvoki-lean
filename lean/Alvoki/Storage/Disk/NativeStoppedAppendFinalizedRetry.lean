import Alvoki.Storage.Disk.NativeStoppedFirstAppendExitTableOpen
import Alvoki.Storage.Disk.NativeFinalizedOpenRetries

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- Begin the read-only retries after the stopped append's issuer and
its last lock reference are gone. Use the final retry heap and its own
inventory for the healthy open of the original live selected image. -/
structure NativeStoppedAppendFinalizedRetry (current : NativeOpenedPosition opened) (request : WriteRequest)
    (inputs : List FilePath) (input : FilePath) (view : OpenCloseHeapView heap FileImage)
    (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray) where
  prepared : NativeReadyWritePreparation current.current.ready.state
  stop : NativeFirstAppendStop prepared
  requestMatches : stop.request = request
  exit : NativeFirstAppendExit stop
  rawExit : RawStoppedFirstAppendExitEffects current stop exit view
  samePhase : view.phase = opened.contents
  calls : RawOpenAdmissionCallbacks heap
  init : OpenSyncCacheCallbacks heap
  release : IO.FS.Handle → heap → heap
  returns : List (FilePath × IO.Error)
  last : heap
  attempts : RawFinalizedOpenAttempts view current.current.ready.state.session.directory calls init release rawExit.released returns last
  ordered : returns.map Prod.fst = inputs
  vacant : TryLockObserves (view.files last).owners current.current.ready.state.session.directory (.ok true)
  plan : exit.Plan
  reader : MarkedReadyOpenObservations input current.current.ready.state.session.directory
    (view.descriptors last) ⟨exit.retry.image, (view.files last).owners⟩ plan.layout
    current.current.ready.state.writer.published vacant plan.selected
  originalView : reader.admission.view = stop.view
  originalRoot : reader.admission.root = stop.root
  liveNames : ∀ path, current.current.ready.state.crashPath path → names rawExit.cut path = reader.reads.bindings path
  stableNames : ∀ path, current.current.ready.state.crashPath path → names last path = names rawExit.cut path
  observedRead : ∀ path payload, current.current.ready.state.crashPath path →
    ∀ file : reader.reads.reads.ObservesFile path payload,
      reader.reads.bindings path = some file.object ∧ bytes rawExit.cut file.object = payload
  stableBytes : ∀ path inode, current.current.ready.state.crashPath path →
    names rawExit.cut path = some inode → bytes last inode = bytes rawExit.cut inode
  stream : Type
  phaseIdentity : IO.Ref (Phase Installed) → Nat
  tokenIdentity : IO.Ref Unit → Nat
  allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))
  allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)
  remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)
  stage : LongKeeperStageCallbacks heap
  rename : FilePath → FilePath → EStateM IO.Error heap Unit
  physical : RawHealthyMarkedOpenEffects reader view calls init last phaseIdentity tokenIdentity
    allocatePhase allocateToken stream remove stage rename
  bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened
  assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
    IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable
  constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files)
  get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)
  set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit
  phaseEffects : OpenPhaseCellEffects view.phase get set
  ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool

variable {current : NativeOpenedPosition opened} {request : WriteRequest}
  {inputs : List FilePath} {input : FilePath} {view : OpenCloseHeapView heap FileImage}
  {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}

/-- The stopped write has one submission and the failed opens retain
their ordered path and diagnostic pairs. -/
def NativeStoppedAppendFinalizedRetry.event
    (seen : NativeStoppedAppendFinalizedRetry current request inputs input view names bytes) : NativeExecutionEvent :=
  .interruptedAppendRetriesRecovered request seen.returns input seen.prepared.batch

/-- Ordered rejected opens keep the live checkpoint and WAL selection.
The exact returned table continues the prior reads and records one
uncertain submission for the interrupted write. -/
structure NativeStoppedAppendFinalizedRetry.Returned
    (seen : NativeStoppedAppendFinalizedRetry current request inputs input view names bytes)
    {handle : NativeOpenedHandle heap} (start : NativeOpenedPosition handle) : Prop where
  sourceWrite : opened.table.UsesOpenWriteSchedules current.current.ready.state.session.directory opened.files opened.phase
  requestMatches : seen.stop.request = request
  interrupted :
    let state := current.current.ready.state
    ∀ (flush : CheckpointOpenHandle → FirstAppendInterrupted Unit)
      (stage : FilePath → ByteArray → FirstAppendInterrupted Unit)
      (sync : Array FilePath → FirstAppendInterrupted Unit) (rename : FilePath → FilePath → FirstAppendInterrupted Unit),
      seen.stop.onOpenPhase opened flush stage sync rename
        (current.reached, state.cache, state.census, seen.prepared.initial) =
        .error seen.stop.logical.appendCall (seen.rawExit.poisoned, state.cache, seen.stop.cutFiles)
  rawStopped : seen.rawExit.StopsAppend
  nativeExit : let process := seen.stop.handle.2.1.reference.process
    seen.rawExit.exitProcess process seen.rawExit.cut = .error process seen.rawExit.afterExit
  released : seen.rawExit.Released
  attempts : RawFinalizedOpenAttempts view current.current.ready.state.session.directory seen.calls seen.init seen.release
    seen.rawExit.released seen.returns seen.last
  order : seen.returns.map Prod.fst = inputs
  restartImage : (view.files seen.last).image = seen.exit.retry.image
  inodeMap : (view.descriptors seen.last).inode = seen.exit.census.inode
  measured : seen.reader.finish.UsesMeasuredRepair
  root : names seen.last current.current.ready.state.session.directory.path = some (seen.stop.view.modelObject seen.stop.root)
  lockObject : names seen.last (current.current.ready.state.session.directory.file .lock) =
    some (seen.stop.view.modelObject seen.stop.lock.child)
  keeper : seen.reader.reads.wal.keeper.object = seen.stop.keeper.child
  liveRead : ∀ path payload, current.current.ready.state.crashPath path →
    ∀ file : seen.reader.reads.reads.ObservesFile path payload,
      names seen.rawExit.cut path = some file.object ∧ bytes seen.rawExit.cut file.object = payload ∧
      names seen.last path = some file.object ∧ bytes seen.last file.object = payload
  sourceOpen : ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles),
    let directory := current.current.ready.state.session.directory
    DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
    cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
      (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
      (fun value => liftM (IO.mkRef value)) makeCache ∧
    seen.physical.openTable seen.bootstrap seen.assemble makeCache = .ok handle.table start.reached
  reader : seen.reader.finish.run seen.reader.chronology =
    .ok start.current.ready.state.session (start.current.ready.state.census, start.current.ready.state.files)
  common : NativeExecutionStep current.current seen.event start.current
  lock : handle.lock = seen.physical.raw.lock
  cache : handle.files.UsesCacheReferences seen.physical.seed.activeRef seen.physical.seed.pendingRef seen.physical.seed.directoryRef
  cacheDirectory : handle.files.AtDirectory current.current.ready.state.session.directory.path
  contents : handle.contents = view.phase
  get : handle.get = seen.get
  set : handle.set = seen.set
  ptrEq : handle.ptrEq = seen.ptrEq
  token : seen.tokenIdentity handle.token = start.current.ready.state.session.sessionRef
  unpinned : start.pins = []
  files : view.files start.reached = start.current.ready.state.files
  census : view.descriptors start.reached = start.current.ready.state.census
  cached : view.cacheAt start.reached seen.physical.seed.directoryRef seen.physical.seed.activeRef
    seen.physical.seed.pendingRef = start.current.ready.state.cache
  history : start.current.history = current.current.history
  submissions : start.current.submissions = current.current.submissions ++ [.uncertainBatch seen.prepared.batch]
  reads : start.current.ready.reads = current.current.ready.reads
  replay : InstalledClientReplay (current.current.submissions ++ [.uncertainBatch seen.prepared.batch])
    current.current.ready.reads current.current.history start.current.ready.state.writer.installed start.current.ready.state.session

/-- Execute the exact raw healthy marked opener after the reached
finalized retry sequence. The continued replay is reconstructed from
the old marker plan and the original poisoned append. -/
theorem NativeStoppedAppendFinalizedRetry.reaches
    (seen : NativeStoppedAppendFinalizedRetry current request inputs input view names bytes) :
    ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle), seen.Returned start := by
  obtain ⟨_, poisoned, setter, _, stopped⟩ := seen.stop.stopsBeforeSuffix current seen.samePhase
  have samePoisoned := (EStateM.Result.ok.inj (setter.symm.trans seen.rawExit.setter)).2
  have released := seen.rawExit.releases
  obtain ⟨inodes, image⟩ := seen.attempts.preserves
  let pending := current.current.ready.stopsAtFirstAppend seen.stop
  obtain ⟨valid, history, _⟩ := current.current.ready.readPrefix.refines
  let marked := seen.plan.markedReport (log := current.current.submissions ++ [.uncertainBatch seen.prepared.batch])
    (reads := current.current.ready.reads) seen.reader valid (history.symm ▸ pending.replay) (history.symm ▸ pending.bounded)
  obtain ⟨measured, installed, cacheOpen, makeCache, cacheAction, cacheSource, ran⟩ :=
    marked.opensHealthyFromAdmission seen.physical.raw seen.physical.seed seen.physical.checkpoint seen.physical.listing
      seen.physical.extents seen.physical.seals seen.physical.keeper seen.physical.sameLookup seen.physical.flat
      seen.physical.marked seen.bootstrap seen.assemble seen.constructs seen.physical.allocations
  let next : NativeReadPosition current.current.history (current.current.submissions ++ [.uncertainBatch seen.prepared.batch]) :=
    ⟨seen.reader.finish.run seen.reader.chronology, installed.state, installed.state, current.current.ready.reads,
      .installed installed.nativeReturned installed.ready.refines.1 (installed.ready.refines.2.1.trans history)
        pending.replay pending.bounded⟩
  obtain ⟨handle, start, position, table, lock, files, contents, get, set, compare, token,
    reached, pins, sameFiles, sameCensus, sameCache⟩ :=
    installed.startsAtCheckpointReopen history next rfl installed.nativeReturned installed.cacheCaptured installed.ownerCaptured
      installed.directoryCaptured seen.phaseEffects seen.ptrEq
  have keeper : seen.reader.reads.wal.keeper.object = seen.stop.keeper.child := by
    have first : seen.plan.layout.keeper.first = current.current.ready.state.writer.installed.activeFirst :=
      seen.plan.recovery.first.trans (valid.retained.active.symm.trans valid.retained.resumed.keeper.symm)
    have path : seen.reader.admission.view.child seen.reader.admission.root (renderWalSegmentName seen.plan.layout.keeper.first) =
        seen.stop.view.child seen.stop.root seen.prepared.keeperName := by
      rw [seen.originalView, seen.originalRoot, first]
    exact (seen.stop.keeper.child_eq (path.symm.trans seen.reader.reads.wal.keeper.bound)).symm
  refine ⟨handle, start, current.uses.writeSchedules, seen.requestMatches, samePoisoned ▸ stopped,
    seen.rawExit.stopsAppend, seen.rawExit.departed, released,
    seen.attempts, seen.ordered, image.trans (congrArg LockedFileState.image released.files),
    inodes.trans (congrArg DescriptorInventory.inode released.census), measured, ?_, ?_, keeper, ?_,
    ⟨cacheOpen, makeCache, cacheAction, cacheSource, ?_⟩, ?_, ?_, lock, files.symm ▸ installed.cacheReferences,
    files.symm ▸ installed.cacheDirectory, contents, get, set, compare, ?_, pins, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have canonical := seen.reader.reads.canonicalDirectory
    rw [seen.originalView, seen.originalRoot] at canonical
    exact (seen.stableNames _ (.inl rfl)).trans ((seen.liveNames _ (.inl rfl)).trans canonical)
  · have canonical := seen.reader.reads.canonicalLock
    have bound := seen.reader.reads.lockEntry
    rw [seen.originalView, seen.originalRoot] at bound
    rw [seen.originalView, ← seen.stop.lock.child_eq bound] at canonical
    exact (seen.stableNames _ (.inr (.inl rfl))).trans ((seen.liveNames _ (.inr (.inl rfl))).trans canonical)
  · intro path payload selected file
    obtain ⟨bound, original⟩ := seen.observedRead path payload selected file
    have named := (seen.liveNames path selected).trans bound
    exact ⟨named, original, (seen.stableNames path selected).trans named,
      (seen.stableBytes path file.object selected named).trans original⟩
  · rw [table, reached]
    exact ran
  · rw [position]
    exact installed.nativeReturned
  · have stepped := NativeExecutionStep.recoverInterruptedAppendAfterRetries current.current seen.stop seen.exit pending
      released.files released.census seen.attempts seen.plan seen.reader seen.originalView seen.originalRoot keeper next rfl rfl
    rw [position]
    simpa only [NativeStoppedAppendFinalizedRetry.event, seen.requestMatches] using stepped
  · rw [position]
    exact token
  · rw [position]
    exact sameFiles
  · rw [position]
    exact sameCensus
  · rw [position]
    exact sameCache
  · rw [position]
  · rw [position]
  · rw [position]
  · rw [position]
    exact next.readPrefix.guardedReplay

end Alvoki.Storage.DiskSession
