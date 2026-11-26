import Alvoki.Storage.Disk.NativeUncertainWriteTableOpen
import Alvoki.Storage.Disk.NativePendingWriteProcessExit
import Alvoki.Storage.Disk.RawHealthyMarkedOpenEffects
import Alvoki.Storage.Disk.NativeExecutionTrace

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair CheckpointPublication

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- Observe the issuing process exit after the returned write error.
Its inherited aliases can survive until subsequent reported drops. -/
structure RawPendingWriteExitEffects (current : NativeOpenedPosition opened)
    (pending : NativePendingWrite current.current.ready) (exit : NativePendingWriteProcessExit pending)
    (view : OpenCloseHeapView heap FileImage) (failed : heap) where
  failedFiles : view.files failed = pending.files
  failedCensus : view.descriptors failed = pending.poisoned.descriptors
  beforeExit : heap
  beforeFiles : view.files beforeExit = exit.filesBeforeExit
  beforeCensus : view.descriptors beforeExit = exit.beforeExit
  beforePhase : view.phase beforeExit opened.phase = some .poisoned
  owner : (view.handle beforeExit opened.lock).1 = view.descriptors beforeExit ∧
    (view.handle beforeExit opened.lock).2.1 = current.current.ready.state.owner
  exitProcess : Nat → EStateM Nat heap Unit
  afterExit : heap
  exited : let process := current.current.ready.state.owner.reference.process
    exitProcess process beforeExit = .error process afterExit
  exitCensus : view.descriptors afterExit = exit.afterExit
  exitFiles : view.files afterExit = exit.filesAfterExit
  released : heap
  dropCensus : view.descriptors released = (view.descriptors afterExit).afterDrops exit.later
  dropFiles : view.files released = (view.descriptors afterExit).dropLockState current.current.ready.state.session.descriptor
    exit.later current.current.ready.state.session.directory (view.files afterExit)

variable {current : NativeOpenedPosition opened} {pending : NativePendingWrite current.current.ready}
  {exit : NativePendingWriteProcessExit pending} {view : OpenCloseHeapView heap FileImage} {failed : heap}

/-- The old lock is held through the reported interval before exit.
After exit its availability follows the exact alias census. Later
drops release the live file image, without a reboot selection. -/
structure RawPendingWriteExitEffects.Released (seen : RawPendingWriteExitEffects current pending exit view failed) : Prop where
  interval : LockCensusTrace current.current.ready.state.session.directory current.current.ready.state.session.descriptor
    (view.descriptors failed) (view.files failed) (view.descriptors seen.beforeExit) (view.files seen.beforeExit)
  held : ¬ TryLockObserves (view.files seen.beforeExit).owners current.current.ready.state.session.directory (.ok true)
  phase : view.phase seen.beforeExit opened.phase = some .poisoned
  rawOwner : (view.handle seen.beforeExit opened.lock).1 = view.descriptors seen.beforeExit ∧
    (view.handle seen.beforeExit opened.lock).2.1 = current.current.ready.state.owner
  stopped : let process := current.current.ready.state.owner.reference.process
    seen.exitProcess process seen.beforeExit = .error process seen.afterExit
  afterExit : TryLockObserves (view.files seen.afterExit).owners current.current.ready.state.session.directory (.ok true) ↔
    (view.descriptors seen.afterExit).references current.current.ready.state.session.descriptor = []
  noOwnerReferences : (view.descriptors seen.released).references current.current.ready.state.session.descriptor = []
  noWriterSlots : ∀ slot ∈ (view.descriptors seen.released).slots,
    slot.reference.process ≠ current.current.ready.state.owner.reference.process
  census : view.descriptors seen.released = exit.census
  files : view.files seen.released = pending.write.failure.released
  vacant : TryLockObserves (view.files seen.released).owners current.current.ready.state.session.directory (.ok true)

/-- The exact reported slot effects release the original poisoned
session's authority while preserving its selected live files. -/
theorem RawPendingWriteExitEffects.releases (seen : RawPendingWriteExitEffects current pending exit view failed) :
    seen.Released := by
  have release := exit.releases
  have census : view.descriptors seen.released = exit.census := by
    rw [seen.dropCensus, seen.exitCensus]
    rfl
  have files : view.files seen.released = pending.write.failure.released := by
    rw [seen.dropFiles, seen.exitCensus, seen.exitFiles]
    exact release.exactFiles
  refine ⟨?_, ?_, seen.beforePhase, seen.owner, seen.exited, ?_, ?_, ?_, census, files,
    files.symm ▸ pending.write.releasedVacant⟩
  · rw [seen.failedFiles, seen.failedCensus, seen.beforeFiles, seen.beforeCensus]
    exact exit.observed
  · rw [seen.beforeFiles]
    exact release.heldBeforeExit
  · rw [seen.exitFiles, seen.exitCensus]
    exact release.afterExit
  · rw [census]
    change ((exit.beforeExit.afterDrops [.exited current.current.ready.state.owner.reference.process]).afterDrops
      exit.later).references current.current.ready.state.session.descriptor = []
    rw [DescriptorInventory.afterDrops_append]
    exact exit.last
  · rw [census]
    exact release.noWriterSlots

/-- The actual classified write and the reported process exit precede
one healthy open of its live marker and checkpoint. The route has no
intervening client operations. -/
structure NativeUncertainWriteExitTableOpen (current : NativeOpenedPosition opened) (request : WriteRequest)
    (input : FilePath) (view : OpenCloseHeapView heap FileImage) (names : heap → FilePath → Option Nat)
    (bytes : heap → Nat → ByteArray) where
  pending : NativePendingWrite current.current.ready
  requestMatches : pending.write.request = request
  cause : IO.Error
  failed : heap
  failedFiles : OpenWriteFiles
  returned :
    let state := current.current.ready.state
    request.runOnOpenPhase state.session.directory pending.write.openCalls opened.phase opened.get opened.set
      (current.reached, (WriteRequest.readyCall state.writer state.cache).2.image) =
      .error (.commitUnknown cause) (failed, failedFiles)
  samePhase : view.phase = opened.contents
  activeRef : IO.Ref (Option (FilePath × IO.FS.Handle))
  pendingRef : IO.Ref (List (FilePath × IO.FS.Handle))
  directoryRef : IO.Ref (Option IO.FS.Handle)
  references : opened.files.UsesCacheReferences activeRef pendingRef directoryRef
  failedCache : view.cacheAt failed directoryRef activeRef pendingRef = pending.cache
  exit : NativePendingWriteProcessExit pending
  noCalls : exit.requests = []
  rawExit : RawPendingWriteExitEffects current pending exit view failed
  plan : pending.write.ReleasedPlan
  reader : MarkedReadyOpenObservations input current.current.ready.state.session.directory exit.census
    pending.write.failure.released plan.layout current.current.ready.state.writer.published pending.write.releasedVacant plan.selected
  lock : reader.reads.bindings (current.current.ready.state.session.directory.file .lock) =
    pending.observed.bindings (current.current.ready.state.session.directory.file .lock)
  directory : reader.reads.bindings current.current.ready.state.session.directory.path =
    pending.observed.bindings current.current.ready.state.session.directory.path
  previousRefs : current.current.ready.state.session.phaseRef ∈ reader.callbacks.liveRefs ∧
    current.current.ready.state.session.sessionRef ∈ reader.callbacks.liveRefs
  liveNames : ∀ path, current.current.ready.state.crashPath path → names failed path = reader.reads.bindings path
  stableNames : ∀ path, current.current.ready.state.crashPath path → names rawExit.released path = names failed path
  observedRead : ∀ path payload, current.current.ready.state.crashPath path →
    ∀ file : reader.reads.reads.ObservesFile path payload,
      reader.reads.bindings path = some file.object ∧ bytes failed file.object = payload
  stableBytes : ∀ path inode, current.current.ready.state.crashPath path →
    names failed path = some inode → bytes rawExit.released inode = bytes failed inode
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
  physical : RawHealthyMarkedOpenEffects reader view calls init rawExit.released phaseIdentity tokenIdentity
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

private def NativeUncertainWriteExitTableOpen.markedReport
    (seen : NativeUncertainWriteExitTableOpen current request input view names bytes)
    (valid : current.current.ready.state.Valid)
    (replay : PendingClientReplay seen.pending.submissions current.current.ready.reads seen.plan.history)
    (bounded : ∀ read ∈ current.current.ready.reads, read.BoundedBy seen.plan.history.length) :
    MarkedOpenSuccessReports input current.current.ready.state.session.directory seen.plan.history
      seen.pending.submissions current.current.ready.reads where
  inventory := seen.exit.census
  retry := seen.pending.write.failure.released
  layout := seen.plan.layout
  published := current.current.ready.state.writer.published
  checkpoint := current.current.ready.state.writer.checkpoint
  selected := seen.plan.selected
  vacant := seen.pending.write.releasedVacant
  opening := seen.reader
  prepared := seen.plan.prepared
  following := seen.reader.reads.walReads.selectedAfterWatermark seen.plan.offsets seen.plan.descriptors
  accepted := seen.plan.accepted
  ordered := seen.plan.ordered
  wal := seen.pending.write.releasedWal seen.plan.history
  walLayout := seen.plan.walLayout
  walValid := seen.plan.walValid
  spans := valid.retained.spans
  active := seen.plan.prepared.pair
  keeper := seen.plan.first
  kept := seen.plan.kept
  pending := replay
  bounded := bounded

/-- Record the original returned error, issuing process and submitted
group, with the complete suffix selected by the still-live marker. -/
def NativeUncertainWriteExitTableOpen.event
    (seen : NativeUncertainWriteExitTableOpen current request input view names bytes) (retained : List WAL.Write) :
    NativeExecutionEvent :=
  .uncertainWriteExitRecovered request input seen.cause [] current.current.ready.state.owner.reference.process
    seen.pending.write.failure.batch retained

/-- The exact result includes the original poisoned return, released
slot interval, observed live checkpoint and WAL reads, and newly
opened table. These facts all refer to one fixed report. -/
structure NativeUncertainWriteExitTableOpen.Returned
    (seen : NativeUncertainWriteExitTableOpen current request input view names bytes) (retained : List WAL.Write)
    {handle : NativeOpenedHandle heap} (start : NativeOpenedPosition handle) : Prop where
  sourceWrite : opened.table.UsesOpenWriteSchedules current.current.ready.state.session.directory opened.files opened.phase
  diagnostic : seen.cause = seen.pending.write.failure.cause
  failedFiles : seen.failedFiles = (seen.pending.cache, seen.pending.write.failure.failed)
  poisoned : view.phase seen.failed opened.phase = some .poisoned
  failedCache : view.cacheAt seen.failed seen.directoryRef seen.activeRef seen.pendingRef = seen.pending.cache
  released : seen.rawExit.Released
  measured : seen.reader.finish.UsesMeasuredRepair
  lockObject : names seen.rawExit.released (current.current.ready.state.session.directory.file .lock) =
    some ((view.handle seen.physical.raw.afterFlock seen.physical.raw.lock).1.inode
      (view.handle seen.physical.raw.afterFlock seen.physical.raw.lock).2.1.description)
  directoryObject : names seen.rawExit.released current.current.ready.state.session.directory.path =
    some ((view.handle seen.physical.seed.afterPending seen.physical.seed.handle).1.inode
      (view.handle seen.physical.seed.afterPending seen.physical.seed.handle).2.1.description)
  liveRead : ∀ path payload, current.current.ready.state.crashPath path →
    ∀ file : seen.reader.reads.reads.ObservesFile path payload,
      names seen.failed path = some file.object ∧ bytes seen.failed file.object = payload ∧
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
  recovery : ∃ next : NativeReadPosition (current.current.history ++ retained) seen.pending.submissions,
    NativePendingWriteExitReopened seen.exit input retained next ∧
    seen.reader.finish.run seen.reader.chronology = next.opened ∧
    start.current = ⟨current.current.history ++ retained, seen.pending.submissions, next⟩
  common : NativeExecutionStep current.current (seen.event retained) start.current
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

/-- Link one actual uncertain return and precisely the observed exit
and alias drops to the exact table returned by the live-marker opener.
The marked selection preserves the prior replay and adds one uncertain
group. The reported primitive effects supply the reached raw heaps. -/
theorem NativeUncertainWriteExitTableOpen.reaches
    (seen : NativeUncertainWriteExitTableOpen current request input view names bytes) :
    ∃ (retained : List WAL.Write) (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      seen.Returned retained start := by
  let state := current.current.ready.state
  have returned : seen.pending.write.request.runOnOpenPhase state.session.directory seen.pending.write.openCalls
      opened.phase opened.get opened.set
      (current.reached, (WriteRequest.readyCall state.writer state.cache).2.image) =
      .error (.commitUnknown seen.cause) (seen.failed, seen.failedFiles) := by
    simpa only [seen.requestMatches] using seen.returned
  obtain ⟨source, diagnostic, failedFiles, poison⟩ := current.classifiesPendingWriteReturn seen.pending returned
  have valid := current.current.ready.readPrefix.refines.1
  obtain ⟨nextState, recovered⟩ := current.current.ready.readPrefix.reopensReleasedUncertainWriteFrom
    seen.pending.write seen.plan seen.reader (seen.lock.trans seen.pending.custody.2.2.2.1)
    (seen.directory.trans seen.pending.custody.2.2.2.2) seen.previousRefs.1 seen.previousRefs.2
  obtain ⟨retained, next, reopened, chosen, worker, nextReturned, cache, owner, slot⟩ :=
    seen.pending.recoversAfterProcessExitFrom seen.exit seen.reader recovered
  have replay := next.readPrefix.refines.2.2
  have bounded := next.readPrefix.readsBounded
  rw [reopened.reads, ← chosen] at replay bounded
  let marked := seen.markedReport valid replay bounded
  obtain ⟨measured, installed, cacheOpen, makeCache, cacheAction, cacheSource, _, ran⟩ :=
    marked.opensHealthyFromAdmission seen.physical.raw seen.physical.seed seen.physical.checkpoint seen.physical.listing
      seen.physical.extents seen.physical.seals seen.physical.keeper seen.physical.sameLookup seen.physical.flat
      seen.physical.marked seen.bootstrap seen.assemble seen.constructs seen.physical.allocations
  obtain ⟨handle, start, reached, rawTable, lock, files, contents, get, set, compare, token,
    reachedHeap, pins, sameFiles, sameCensus, sameCache⟩ :=
    installed.startsAtCheckpointReopen chosen next worker.symm nextReturned cache owner slot seen.phaseEffects seen.ptrEq
  refine ⟨retained, handle, start, source, diagnostic, failedFiles, seen.samePhase.symm ▸ poison, seen.failedCache,
    seen.rawExit.releases, measured, ?_, ?_, ?_, ⟨cacheOpen, makeCache, cacheAction, cacheSource, ?_⟩,
    ⟨next, reopened, worker.symm, reached⟩, ?_, lock, files.symm ▸ installed.cacheReferences,
    files.symm ▸ installed.cacheDirectory, contents, get, set, compare, ?_, pins, ?_, ?_, ?_⟩
  · rw [seen.physical.raw.sameLock, seen.physical.raw.appendHandle]
    exact (seen.stableNames _ (.inr (.inl rfl))).trans ((seen.liveNames _ (.inr (.inl rfl))).trans
      seen.reader.reads.sameObjects.2.1)
  · rw [seen.physical.seed.sameHandle, seen.physical.seed.openedHandle]
    exact (seen.stableNames _ (.inl rfl)).trans ((seen.liveNames _ (.inl rfl)).trans seen.reader.reads.sameObjects.1)
  · intro path payload selected file
    obtain ⟨bound, returnedBytes⟩ := seen.observedRead path payload selected file
    have named := (seen.liveNames path selected).trans bound
    exact ⟨named, returnedBytes, (seen.stableNames path selected).trans named,
      (seen.stableBytes path file.object selected named).trans returnedBytes⟩
  · rw [rawTable, reachedHeap]
    exact ran
  · have step := NativeExecutionStep.recoverUncertainWriteAfterExit current.current seen.pending seen.exit retained next reopened
    rw [reached]
    simpa only [NativeUncertainWriteExitTableOpen.event, seen.requestMatches, diagnostic, seen.noCalls] using step
  · rw [reached]
    exact token
  · rw [reached]
    exact sameFiles
  · rw [reached]
    exact sameCensus
  · rw [reached]
    exact sameCache

end Alvoki.Storage.DiskSession
