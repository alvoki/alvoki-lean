import Alvoki.Storage.Disk.NativeOpenedFirstAppendReport
import Alvoki.Storage.Disk.NativeFirstAppendExitReopen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair CheckpointPublication SyncHandleRouting

variable {heap : Type} {opened : NativeOpenedHandle heap} {current : NativeOpenedPosition opened}
  {prepared : NativeReadyWritePreparation current.current.ready.state} {stop : NativeFirstAppendStop prepared}
  {exit : NativeFirstAppendExit stop} {view : OpenCloseHeapView heap FileImage}

/-- Report the selected keeper at the raw append and the process exit
on the reached heap. The local projections match the stopped append;
the raw heap may include effects beyond the phase-cell setter. -/
structure RawStoppedFirstAppendExitEffects (current : NativeOpenedPosition opened)
    {prepared : NativeReadyWritePreparation current.current.ready.state} (stop : NativeFirstAppendStop prepared)
    (exit : NativeFirstAppendExit stop) (view : OpenCloseHeapView heap FileImage) where
  poisoned : heap
  setter : opened.set opened.phase .poisoned current.reached = .ok () poisoned
  beforeAppend : heap
  writeHandle : IO.FS.Handle
  activeRef : IO.Ref (Option (FilePath × IO.FS.Handle))
  pendingRef : IO.Ref (List (FilePath × IO.FS.Handle))
  directoryRef : IO.Ref (Option IO.FS.Handle)
  references : opened.files.UsesCacheReferences activeRef pendingRef directoryRef
  poisonedCache : view.cacheAt poisoned directoryRef activeRef pendingRef = current.current.ready.state.cache
  rawOpenAppend : FilePath → EStateM IO.Error heap IO.FS.Handle
  selected : selectAppendHandle (view.active poisoned activeRef) rawOpenAppend prepared.keeperPath poisoned =
    .ok writeHandle beforeAppend
  sameHandle : view.handle beforeAppend writeHandle = stop.handle
  inputCensus : view.descriptors beforeAppend = stop.selectedCensus
  inputFiles : view.files beforeAppend = current.current.ready.state.files
  beforePhase : view.phase beforeAppend opened.phase = some .poisoned
  append : IO.FS.Handle → ByteArray → EStateM (FilePath × ByteArray) heap (Except IO.Error Unit)
  cut : heap
  issued : append writeHandle (WAL.encodeBatch prepared.batch) beforeAppend = .error stop.logical.appendCall cut
  cutCensus : view.descriptors cut = stop.cutFiles.1
  cutFiles : view.files cut = ⟨stop.files, current.current.ready.state.files.owners⟩
  cutPhase : view.phase cut opened.phase = some .poisoned
  owner : (view.handle cut opened.lock).1 = view.descriptors cut ∧
    (view.handle cut opened.lock).2.1 = exit.issuerLock
  exitProcess : Nat → EStateM Nat heap Unit
  afterExit : heap
  departed : let process := stop.handle.2.1.reference.process
    exitProcess process cut = .error process afterExit
  exitCensus : view.descriptors afterExit = (view.descriptors cut).afterDrops [exit.exit]
  exitFiles : view.files afterExit = (view.descriptors cut).dropLockState current.current.ready.state.session.descriptor
    [exit.exit] current.current.ready.state.session.directory (view.files cut)
  released : heap
  dropCensus : view.descriptors released = (view.descriptors afterExit).afterDrops exit.later
  dropFiles : view.files released = (view.descriptors afterExit).dropLockState current.current.ready.state.session.descriptor
    exit.later current.current.ready.state.session.directory (view.files afterExit)

private abbrev StoppedAppendHeap (heap : Type) :=
  ExceptT IO.Error (EStateM (FilePath × ByteArray) heap)

private def liftAppendCallback (call : EStateM IO.Error heap α) : StoppedAppendHeap heap α :=
  fun before => match call before with
    | .ok value reached => .ok (.ok value) reached
    | .error cause reached => .ok (.error cause) reached

/-- The append stops before any flush or cache update on the raw heap. -/
def RawStoppedFirstAppendExitEffects.StopsAppend
    (seen : RawStoppedFirstAppendExitEffects current stop exit view) : Prop :=
  ∀ (update : Option (FilePath × IO.FS.Handle) → StoppedAppendHeap heap Unit)
    (flush : IO.FS.Handle → StoppedAppendHeap heap Unit),
    appendWithActive (fun before => .ok (.ok (view.active before seen.activeRef)) before) update
      (fun path => liftAppendCallback (seen.rawOpenAppend path)) seen.append flush
      prepared.keeperPath (WAL.encodeBatch prepared.batch) seen.poisoned = .error stop.logical.appendCall seen.cut

/-- The raw append helper also stops on that same selected handle.
The cache setter and flush cannot run after the outer stop. -/
theorem RawStoppedFirstAppendExitEffects.stopsAppend
    (seen : RawStoppedFirstAppendExitEffects current stop exit view)
    (update : Option (FilePath × IO.FS.Handle) → StoppedAppendHeap heap Unit)
    (flush : IO.FS.Handle → StoppedAppendHeap heap Unit) :
    appendWithActive (fun before => .ok (.ok (view.active before seen.activeRef)) before) update
      (fun path => liftAppendCallback (seen.rawOpenAppend path)) seen.append flush
      prepared.keeperPath (WAL.encodeBatch prepared.batch) seen.poisoned = .error stop.logical.appendCall seen.cut := by
  have selected : selectAppendHandle (m := StoppedAppendHeap heap) (view.active seen.poisoned seen.activeRef)
      (fun path => liftAppendCallback (seen.rawOpenAppend path)) prepared.keeperPath seen.poisoned =
      .ok (.ok seen.writeHandle) seen.beforeAppend := by
    have reported := seen.selected
    cases seenActive : view.active seen.poisoned seen.activeRef with
    | none =>
      simp only [selectAppendHandle, seenActive] at reported
      simp [selectAppendHandle, liftAppendCallback, reported]
    | some entry =>
      obtain ⟨name, file⟩ := entry
      cases same : prepared.keeperPath == name <;>
        simp [selectAppendHandle, seenActive, same, liftAppendCallback, Pure.pure, EStateM.pure,
          ExceptT.pure, ExceptT.mk] at reported ⊢
      · rw [reported]
      · simp [reported.1, reported.2]
  simp [appendWithActive, selected, seen.issued, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
    EStateM.bind, MonadExcept.tryCatch, MonadExceptOf.tryCatch, tryCatchThe, ExceptT.tryCatch]

/-- Exit alone leaves the lock held while an alias remains in the
reported census. The eventual vacant heap retains the live file image. -/
structure RawStoppedFirstAppendExitEffects.Released
    (seen : RawStoppedFirstAppendExitEffects current stop exit view) : Prop where
  interval : LockCensusTrace current.current.ready.state.session.directory current.current.ready.state.session.descriptor
    (view.descriptors seen.cut) (view.files seen.cut) (view.descriptors seen.released) (view.files seen.released)
  afterExit : TryLockObserves (view.files seen.afterExit).owners current.current.ready.state.session.directory (.ok true) ↔
    (view.descriptors seen.afterExit).references current.current.ready.state.session.descriptor = []
  census : view.descriptors seen.released = exit.census
  files : view.files seen.released = exit.retry
  issuerRetired : ∀ slot ∈ (view.descriptors seen.released).slots, slot.reference.process ≠ stop.handle.2.1.reference.process
  available : TryLockObserves (view.files seen.released).owners current.current.ready.state.session.directory (.ok true)

/-- The reported exit and subsequent drops release the tracked lock
without changing the interrupted append's live file selection. -/
theorem RawStoppedFirstAppendExitEffects.releases
    (seen : RawStoppedFirstAppendExitEffects current stop exit view) : seen.Released := by
  let state := current.current.ready.state
  have valid := current.current.ready.readPrefix.refines.1
  have live : (view.descriptors seen.cut).references state.session.descriptor ≠ [] := by
    rw [seen.cutCensus]
    exact List.ne_nil_of_mem (stop.cutFiles.1.mem_references.mpr
      ⟨exit.issuerLock, exit.issuerLockLive, rfl, exit.issuerLockDescription⟩)
  have held : (view.files seen.cut).owners.Owns state.session.directory state.session.descriptor := by
    rw [seen.cutFiles]
    exact valid.retained.held
  have first : LockCensusTrace state.session.directory state.session.descriptor
      (view.descriptors seen.cut) (view.files seen.cut) (view.descriptors seen.afterExit) (view.files seen.afterExit) := by
    rw [seen.exitCensus, seen.exitFiles]
    exact .drops (.start held live) [exit.exit]
  have trace : LockCensusTrace state.session.directory state.session.descriptor
      (view.descriptors seen.cut) (view.files seen.cut) (view.descriptors seen.released) (view.files seen.released) := by
    rw [seen.dropCensus, seen.dropFiles]
    exact first.drops exit.later
  have census : view.descriptors seen.released = exit.census := by
    rw [seen.dropCensus, seen.exitCensus, seen.cutCensus, DescriptorInventory.afterDrops_append]
    rfl
  have files := trace.reached.2.2
  have last : exit.census.references state.session.descriptor = [] := exit.last
  rw [census, ite_eq_left last, seen.cutFiles] at files
  exact ⟨trace, first.freshFlockAllowed, census, files, census.symm ▸ exit.noIssuerSlots, files.symm ▸ exit.vacant⟩

/-- One prescribed write stops at its selected keeper before returning,
and one observed process exit and release lead to the healthy raw open.
The reports refer to live bytes and names throughout the exit interval. -/
structure NativeStoppedFirstAppendExitTableOpen (current : NativeOpenedPosition opened) (request : WriteRequest)
    (input : FilePath) (view : OpenCloseHeapView heap FileImage) (names : heap → FilePath → Option Nat)
    (bytes : heap → Nat → ByteArray) where
  prepared : NativeReadyWritePreparation current.current.ready.state
  stop : NativeFirstAppendStop prepared
  requestMatches : stop.request = request
  exit : NativeFirstAppendExit stop
  rawExit : RawStoppedFirstAppendExitEffects current stop exit view
  plan : exit.Plan
  reader : NativeFirstAppendExitReads exit input plan.layout plan.selected
  samePhase : view.phase = opened.contents
  liveNames : ∀ path, current.current.ready.state.crashPath path → names rawExit.cut path = reader.opening.reads.bindings path
  stableNames : ∀ path, current.current.ready.state.crashPath path → names rawExit.released path = names rawExit.cut path
  observedRead : ∀ path payload, current.current.ready.state.crashPath path →
    ∀ file : reader.opening.reads.reads.ObservesFile path payload,
      reader.opening.reads.bindings path = some file.object ∧ bytes rawExit.cut file.object = payload
  stableBytes : ∀ path inode, current.current.ready.state.crashPath path →
    names rawExit.cut path = some inode → bytes rawExit.released inode = bytes rawExit.cut inode
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
  physical : RawHealthyMarkedOpenEffects reader.opening view calls init rawExit.released phaseIdentity tokenIdentity
    allocatePhase allocateToken stream remove stage rename
  bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened
  assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
    IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable
  constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files)
  get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)
  set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit
  phaseEffects : OpenPhaseCellEffects view.phase get set
  ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool

variable {request : WriteRequest} {input : FilePath}
  {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}

/-- Reuse the live-marker plan at an admission with the same file
image and its own exact owner map and descriptor inventory. -/
def NativeFirstAppendExit.Plan.markedReport (plan : exit.Plan)
    {inventory : DescriptorInventory} {owners : LockOwners}
    {vacant : TryLockObserves owners current.current.ready.state.session.directory (.ok true)}
    (opening : MarkedReadyOpenObservations input current.current.ready.state.session.directory inventory
      ⟨exit.retry.image, owners⟩ plan.layout current.current.ready.state.writer.published vacant plan.selected)
    (valid : current.current.ready.state.Valid)
    (pending : PendingClientReplay log reads current.current.ready.state.writer.history)
    (bounded : ∀ read ∈ reads, read.BoundedBy current.current.ready.state.writer.history.length) :
    MarkedOpenSuccessReports input current.current.ready.state.session.directory current.current.ready.state.writer.history
      log reads where
  inventory := inventory
  retry := ⟨exit.retry.image, owners⟩
  layout := plan.layout
  published := current.current.ready.state.writer.published
  checkpoint := current.current.ready.state.writer.checkpoint
  selected := plan.selected
  vacant := vacant
  opening := opening
  prepared := plan.recovery.prepared
  following := opening.reads.walReads.selectedAfterWatermark plan.recovery.offsets plan.recovery.descriptors
  accepted := (congrArg DirectoryPublication.Bindings.manifest plan.pair).symm ▸ valid.retained.resumed.accepted
  ordered := valid.retained.resumed.ordered
  wal := current.current.ready.state.writer.wal
  walLayout := valid.retained.layout
  walValid := valid.retained.valid
  spans := valid.retained.spans
  active := valid.retained.walPair.trans (congrArg Target.pair plan.recovery.target).symm
  keeper := plan.recovery.first
  kept := plan.recovery.kept.trans valid.retained.sealedFiles
  pending := pending
  bounded := bounded

/-- The reached next table carries one interrupted submission,
without any write response, and preserves the prior replay. -/
structure NativeStoppedFirstAppendExitTableOpen.Returned
    (seen : NativeStoppedFirstAppendExitTableOpen current request input view names bytes)
    {handle : NativeOpenedHandle heap} (start : NativeOpenedPosition handle) : Prop where
  sourceWrite : opened.table.UsesOpenWriteSchedules current.current.ready.state.session.directory opened.files opened.phase
  pending : NativePendingFirstAppend current.current.ready seen.stop
  issued : seen.stop.rawWrite seen.stop.handle (WAL.encodeBatch seen.prepared.batch)
    (seen.stop.selectedCensus, seen.prepared.initial) = .error seen.stop.logical.appendCall seen.stop.cutFiles
  interrupted :
    let state := current.current.ready.state
    ∀ (flush : CheckpointOpenHandle → FirstAppendInterrupted Unit)
      (stage : FilePath → ByteArray → FirstAppendInterrupted Unit)
      (sync : Array FilePath → FirstAppendInterrupted Unit) (rename : FilePath → FilePath → FirstAppendInterrupted Unit),
      seen.stop.onOpenPhase opened flush stage sync rename (current.reached, state.cache, state.census, seen.prepared.initial) =
        .error seen.stop.logical.appendCall (seen.rawExit.poisoned, state.cache, seen.stop.cutFiles)
  selected : selectAppendHandle (view.active seen.rawExit.poisoned seen.rawExit.activeRef)
    seen.rawExit.rawOpenAppend seen.prepared.keeperPath seen.rawExit.poisoned =
    .ok seen.rawExit.writeHandle seen.rawExit.beforeAppend
  rawStopped : seen.rawExit.StopsAppend
  nativeExit : let process := seen.stop.handle.2.1.reference.process
    seen.rawExit.exitProcess process seen.rawExit.cut = .error process seen.rawExit.afterExit
  released : seen.rawExit.Released
  measured : seen.reader.opening.finish.UsesMeasuredRepair
  lockObject : names seen.rawExit.released (current.current.ready.state.session.directory.file .lock) =
    some ((view.handle seen.physical.raw.afterFlock seen.physical.raw.lock).1.inode
      (view.handle seen.physical.raw.afterFlock seen.physical.raw.lock).2.1.description)
  directoryObject : names seen.rawExit.released current.current.ready.state.session.directory.path =
    some ((view.handle seen.physical.seed.afterPending seen.physical.seed.handle).1.inode
      (view.handle seen.physical.seed.afterPending seen.physical.seed.handle).2.1.description)
  liveRead : ∀ path payload, current.current.ready.state.crashPath path →
    ∀ file : seen.reader.opening.reads.reads.ObservesFile path payload,
      names seen.rawExit.cut path = some file.object ∧ bytes seen.rawExit.cut file.object = payload ∧
      names seen.rawExit.released path = some file.object ∧ bytes seen.rawExit.released file.object = payload
  sourceOpen : ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles),
    let directory := current.current.ready.state.session.directory
    DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
    cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
      (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
      (fun value => liftM (IO.mkRef value)) makeCache ∧
    seen.physical.openTable seen.bootstrap seen.assemble makeCache = .ok handle.table start.reached
  recovery : ∃ next : NativeReadPosition current.current.history (current.current.submissions ++ [.uncertainBatch seen.prepared.batch]),
    NativeFirstAppendExitContinuation current.current.ready seen.stop seen.exit input next ∧
    seen.reader.opening.finish.run seen.reader.opening.chronology = next.opened ∧
    start.current = ⟨current.current.history, current.current.submissions ++ [.uncertainBatch seen.prepared.batch], next⟩
  common : NativeExecutionStep current.current (.interruptedAppendRecovered request input seen.prepared.batch) start.current
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

/-- Match the original stopped write to the reported process exit and
last reference drops, then execute the selected raw marked opener. -/
theorem NativeStoppedFirstAppendExitTableOpen.reaches
    (seen : NativeStoppedFirstAppendExitTableOpen current request input view names bytes) :
    ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle), seen.Returned start := by
  obtain ⟨issued, poisoned, setter, _, stopped⟩ := seen.stop.stopsBeforeSuffix current seen.samePhase
  have samePoisoned := (EStateM.Result.ok.inj (setter.symm.trans seen.rawExit.setter)).2
  obtain ⟨source, pending, _, _⟩ := current.stopsWriteAtFirstAppend seen.stop
    (fun _ => pure ()) (fun _ _ => pure ()) (fun _ => pure ()) (fun _ _ => pure ())
  obtain ⟨next, recovered, worker, nextReturned, cache, owner, slot⟩ :=
    current.current.ready.recoversFirstAppendAfterExitFrom seen.exit seen.plan seen.reader
  obtain ⟨valid, history, _⟩ := current.current.ready.readPrefix.refines
  let marked := seen.plan.markedReport (log := current.current.submissions ++ [.uncertainBatch seen.prepared.batch])
    (reads := current.current.ready.reads) seen.reader.opening valid (history.symm ▸ pending.replay) (history.symm ▸ pending.bounded)
  obtain ⟨measured, installed, cacheOpen, makeCache, cacheAction, cacheSource, _, ran⟩ :=
    marked.opensHealthyFromAdmission seen.physical.raw seen.physical.seed seen.physical.checkpoint seen.physical.listing
      seen.physical.extents seen.physical.seals seen.physical.keeper seen.physical.sameLookup seen.physical.flat
      seen.physical.marked seen.bootstrap seen.assemble seen.constructs seen.physical.allocations
  obtain ⟨handle, start, reached, rawTable, lock, files, contents, get, set, compare, token,
    reachedHeap, pins, sameFiles, sameCensus, sameCache⟩ :=
    installed.startsAtCheckpointReopen history next worker.symm nextReturned cache owner slot seen.phaseEffects seen.ptrEq
  refine ⟨handle, start, source, pending, issued, samePoisoned ▸ stopped, seen.rawExit.selected, seen.rawExit.stopsAppend,
    seen.rawExit.departed, seen.rawExit.releases, measured, ?_, ?_, ?_,
    ⟨cacheOpen, makeCache, cacheAction, cacheSource, ?_⟩, ⟨next, recovered, worker.symm, reached⟩, ?_,
    lock, files.symm ▸ installed.cacheReferences, files.symm ▸ installed.cacheDirectory, contents, get, set, compare,
    ?_, pins, ?_, ?_, ?_⟩
  · rw [seen.physical.raw.sameLock, seen.physical.raw.appendHandle]
    exact (seen.stableNames _ (.inr (.inl rfl))).trans ((seen.liveNames _ (.inr (.inl rfl))).trans
      seen.reader.opening.reads.sameObjects.2.1)
  · rw [seen.physical.seed.sameHandle, seen.physical.seed.openedHandle]
    exact (seen.stableNames _ (.inl rfl)).trans ((seen.liveNames _ (.inl rfl)).trans seen.reader.opening.reads.sameObjects.1)
  · intro path payload selected file
    obtain ⟨bound, returnedBytes⟩ := seen.observedRead path payload selected file
    have named := (seen.liveNames path selected).trans bound
    exact ⟨named, returnedBytes, (seen.stableNames path selected).trans named,
      (seen.stableBytes path file.object selected named).trans returnedBytes⟩
  · rw [rawTable, reachedHeap]
    exact ran
  · have step := NativeExecutionStep.recoverInterruptedAppend current.current seen.stop seen.exit next recovered
    rw [reached]
    simpa only [seen.requestMatches] using step
  · rw [reached]
    exact token
  · rw [reached]
    exact sameFiles
  · rw [reached]
    exact sameCensus
  · rw [reached]
    exact sameCache

end Alvoki.Storage.DiskSession
