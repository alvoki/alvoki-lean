import Alvoki.Storage.Disk.Proofs.Native.Open.NativeAlignedCloseTableOpen
import Alvoki.Storage.Disk.Proofs.Native.Checkpoint.NativeAlignedCheckpointReopenEffects
import Alvoki.Storage.Disk.Proofs.Native.Execution.NativeReadyProcessExit

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- Observe a writer's exit between calls. The raw exit has no return to
that process. The descriptor interval can retain aliases until later
reported drops, and the same selected names and bytes reach the opener. -/
structure NativeOpenedProcessExitReport (current : NativeOpenedPosition opened) (input : FilePath)
    (view : OpenCloseHeapView heap FileImage) (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray) where
  observed : NativeReadyProcessExitObservation current.current.ready.state input
  initial : (view.descriptors current.reached, view.files current.reached) =
    (current.current.ready.state.census, current.current.ready.state.files)
  beforeExit : heap
  beforeCensus : view.descriptors beforeExit = observed.exit.beforeExit
  beforeFiles : view.files beforeExit = observed.exit.filesBeforeExit
  beforePhase : view.phase beforeExit opened.phase = some current.current.ready.state.session.phase
  owner : (view.handle beforeExit opened.lock).1 = view.descriptors beforeExit ∧
    (view.handle beforeExit opened.lock).2.1 = current.current.ready.state.owner
  exitProcess : Nat → EStateM Nat heap Unit
  afterExit : heap
  exited : let process := current.current.ready.state.owner.reference.process
    exitProcess process beforeExit = .error process afterExit
  exitCensus : view.descriptors afterExit = observed.exit.afterExit
  exitFiles : view.files afterExit = observed.exit.filesAfterExit
  released : heap
  dropCensus : view.descriptors released = (view.descriptors afterExit).afterDrops observed.exit.later
  dropFiles : view.files released = (view.descriptors afterExit).dropLockState current.current.ready.state.session.descriptor
    observed.exit.later current.current.ready.state.session.directory (view.files afterExit)
  originalNames : ∀ path, current.current.ready.state.crashPath path → names current.reached path = observed.files.names path
  stableNames : ∀ path, current.current.ready.state.crashPath path → names released path = names current.reached path
  originalBytes : ∀ path inode payload, current.current.ready.state.crashPath path →
    observed.files.names path = some inode → observed.files.bytes inode = some payload → bytes current.reached inode = payload
  stableBytes : ∀ path inode, current.current.ready.state.crashPath path →
    names current.reached path = some inode → bytes released inode = bytes current.reached inode
  plan : ClosedReadyReopenLayout current.current.ready.state.writer current.current.ready.state.releasedFiles
  selected : SelectedIntegrityCheckpoint current.current.ready.state.writer.published.durable
    current.current.ready.state.releasedFiles.image.directory.active.manifest current.current.ready.state.writer.checkpoint
  reader : NativeCloseAlignedReads observed.files input observed.exit.census plan.layout selected
  calls : RawOpenAdmissionCallbacks heap
  init : OpenSyncCacheCallbacks heap
  stream : Type
  phaseIdentity : IO.Ref (Phase Installed) → Nat
  tokenIdentity : IO.Ref Unit → Nat
  allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))
  allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)
  reopen : RawAlignedReopenEffects reader view calls init released phaseIdentity tokenIdentity allocatePhase allocateToken stream
  remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)
  write : FilePath → ByteArray → EStateM IO.Error heap Unit
  rename : FilePath → FilePath → EStateM IO.Error heap Unit
  bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened
  assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
    IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable
  constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files)
  get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)
  set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit
  phaseEffects : OpenPhaseCellEffects view.phase get set
  ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool

variable {current : NativeOpenedPosition opened} {input : FilePath} {view : OpenCloseHeapView heap FileImage}
  {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}

/-- The same projected chronology starts at the old table's heap and
ends at the next opener's heap. An inherited reference keeps the lock
held immediately after exit. Later drops determine the released census. -/
structure NativeOpenedProcessExitReport.Released
    (seen : NativeOpenedProcessExitReport current input view names bytes) : Prop where
  beforeInterval : LockCensusTrace current.current.ready.state.session.directory current.current.ready.state.session.descriptor
    (view.descriptors current.reached) (view.files current.reached) (view.descriptors seen.beforeExit) (view.files seen.beforeExit)
  held : ¬ TryLockObserves (view.files seen.beforeExit).owners current.current.ready.state.session.directory (.ok true)
  phase : view.phase seen.beforeExit opened.phase = some (.ready current.current.ready.state.writer.installed)
  rawOwner : (view.handle seen.beforeExit opened.lock).1 = view.descriptors seen.beforeExit ∧
    (view.handle seen.beforeExit opened.lock).2.1 = current.current.ready.state.owner
  stopped : let process := current.current.ready.state.owner.reference.process
    seen.exitProcess process seen.beforeExit = .error process seen.afterExit
  afterExit : TryLockObserves (view.files seen.afterExit).owners current.current.ready.state.session.directory (.ok true) ↔
    (view.descriptors seen.afterExit).references current.current.ready.state.session.descriptor = []
  census : view.descriptors seen.released = seen.observed.exit.census
  files : view.files seen.released = current.current.ready.state.releasedFiles
  noOwnerReferences : (view.descriptors seen.released).references current.current.ready.state.session.descriptor = []
  noWriterSlots : ∀ slot ∈ (view.descriptors seen.released).slots,
    slot.reference.process ≠ current.current.ready.state.owner.reference.process
  available : TryLockObserves (view.files seen.released).owners current.current.ready.state.session.directory (.ok true)

/-- The observed exit alone need not release the lock. The exact
reported census at the later reopen excludes every old reference. -/
theorem NativeOpenedProcessExitReport.releases (seen : NativeOpenedProcessExitReport current input view names bytes) : seen.Released := by
  have valid := current.current.ready.readPrefix.refines.1
  have released := seen.observed.exit.releases valid.owner
  have beforeCensus : view.descriptors current.reached = current.current.ready.state.census := congrArg Prod.fst seen.initial
  have beforeFiles : view.files current.reached = current.current.ready.state.files := congrArg Prod.snd seen.initial
  have census : view.descriptors seen.released = seen.observed.exit.census := by
    rw [seen.dropCensus, seen.exitCensus]
    rfl
  have files : view.files seen.released = current.current.ready.state.releasedFiles := by
    rw [seen.dropFiles, seen.exitCensus, seen.exitFiles]
    exact released.exactFiles
  refine ⟨?_, ?_, valid.phase ▸ seen.beforePhase, seen.owner, seen.exited, ?_, census, files, ?_, ?_, ?_⟩
  · rw [beforeCensus, beforeFiles, seen.beforeCensus, seen.beforeFiles]
    exact seen.observed.exit.observed
  · rw [seen.beforeFiles]
    exact released.heldBeforeExit
  · rw [seen.exitFiles, seen.exitCensus]
    exact released.afterExit
  · rw [census, NativeWriterProcessExit.census, NativeWriterProcessExit.afterExit, DescriptorInventory.afterDrops_append]
    exact seen.observed.exit.last
  · rw [census]
    exact released.noWriterSlots
  · rw [files]
    exact current.current.ready.state.releasedVacant

/-- The next raw reader observes the same protected selected bytes as
before exit, including the selected inode's original binding. -/
theorem NativeOpenedProcessExitReport.readsReleasedFile
    (seen : NativeOpenedProcessExitReport current input view names bytes) {path : FilePath} {payload : ByteArray}
    (selected : current.current.ready.state.crashPath path) (read : seen.reader.ReadsOriginal path payload) :
    ∃ observed : seen.reader.opening.reads.reads.ObservesFile path payload,
      names current.reached path = some observed.object ∧ bytes current.reached observed.object = payload ∧
      names seen.released path = some observed.object ∧ bytes seen.released observed.object = payload := by
  obtain ⟨file, named, content⟩ := read
  have originalName := (seen.originalNames path selected).trans named
  have originalBytes := seen.originalBytes path file.object payload selected named content
  exact ⟨file, originalName, originalBytes, (seen.stableNames path selected).trans originalName,
    (seen.stableBytes path file.object selected originalName).trans originalBytes⟩

/-- The actual post-exit return carries the exact newly allocated
phase and cache, with the same selected files and client history. -/
structure NativeOpenedProcessExitReport.Returned
    (seen : NativeOpenedProcessExitReport current input view names bytes)
    {handle : NativeOpenedHandle heap} (start : NativeOpenedPosition handle) : Prop where
  released : seen.Released
  sourceOpen : ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles),
    let directory := current.current.ready.state.session.directory
    DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
    cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
      (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
      (fun value => liftM (IO.mkRef value)) makeCache ∧
    seen.reopen.openTable seen.remove seen.write seen.rename seen.bootstrap seen.assemble makeCache =
      .ok handle.table start.reached
  reader : seen.reader.run = start.current.ready.opened
  selectedReads : NativeCloseSelectedReads seen.reader
  lockObject : names seen.released (current.current.ready.state.session.directory.file .lock) =
    some ((view.handle seen.reopen.admission.raw.afterFlock seen.reopen.admission.raw.lock).1.inode
      (view.handle seen.reopen.admission.raw.afterFlock seen.reopen.admission.raw.lock).2.1.description)
  directoryObject : names seen.released current.current.ready.state.session.directory.path =
    some ((view.handle seen.reopen.admission.seed.afterPending seen.reopen.admission.seed.handle).1.inode
      (view.handle seen.reopen.admission.seed.afterPending seen.reopen.admission.seed.handle).2.1.description)
  selectedBytes : ∀ path payload, current.current.ready.state.crashPath path → seen.reader.ReadsOriginal path payload →
    ∃ read : seen.reader.opening.reads.reads.ObservesFile path payload,
      names current.reached path = some read.object ∧ bytes current.reached read.object = payload ∧
      names seen.released path = some read.object ∧ bytes seen.released read.object = payload
  recovery : ∃ next : NativeReadPosition current.current.history current.current.submissions,
    NativeReadyProcessExitReopened current.current.ready seen.observed next ∧
    start.current = ⟨current.current.history, current.current.submissions, next⟩
  common : NativeExecutionStep current.current
    (.readyExitRecovered input current.current.ready.state.owner.reference.process) start.current
  lock : handle.lock = seen.reopen.admission.raw.lock
  cache : handle.files.UsesCacheReferences seen.reopen.admission.seed.activeRef seen.reopen.admission.seed.pendingRef
    seen.reopen.admission.seed.directoryRef
  cacheDirectory : handle.files.AtDirectory current.current.ready.state.session.directory.path
  contents : handle.contents = view.phase
  get : handle.get = seen.get
  set : handle.set = seen.set
  ptrEq : handle.ptrEq = seen.ptrEq
  token : seen.tokenIdentity handle.token = start.current.ready.state.session.sessionRef
  unpinned : start.pins = []
  files : view.files start.reached = start.current.ready.state.files
  census : view.descriptors start.reached = start.current.ready.state.census
  cached : view.cacheAt start.reached seen.reopen.admission.seed.directoryRef seen.reopen.admission.seed.activeRef
    seen.reopen.admission.seed.pendingRef = start.current.ready.state.cache

/-- Derive one raw reopen after the reported process exit and reference
interval. Its common event records the original process with no close
or write response, and the reader preserves the earlier replay. -/
theorem NativeOpenedProcessExitReport.reaches (seen : NativeOpenedProcessExitReport current input view names bytes) :
    ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle), seen.Returned start := by
  let state := current.current.ready.state
  obtain ⟨valid, rows, previous⟩ := current.current.ready.readPrefix.refines
  have selected := seen.observed.files.reopensReleasedAlignedAt valid.retained rows previous
    current.current.ready.readPrefix.readsBounded seen.plan seen.selected seen.reader
  obtain ⟨next, reopened, readerRan, nextReturned, owner, slot, cache, selectedReads⟩ :=
    current.current.ready.reopensAfterProcessExitAt seen.observed seen.reader selected
  have pending : PendingClientReplay current.current.submissions current.current.ready.reads state.writer.history := by
    simpa only [state, rows] using previous
  have bounded : ∀ read ∈ current.current.ready.reads, read.BoundedBy state.writer.history.length := by
    simpa only [state, rows] using current.current.ready.readPrefix.readsBounded
  obtain ⟨installed, cacheOpen, makeCache, cacheAction, cacheSource, rawOpen⟩ :=
    seen.reopen.opens valid.retained pending bounded seen.remove seen.write seen.rename seen.bootstrap seen.assemble seen.constructs
  have sameReturn := (seen.reader.markedReport_run valid.retained pending bounded).trans readerRan
  obtain ⟨handle, start, currentEq, rawTable, lock, files, contents, get, set, compare, token, reached, pins,
    sameFiles, sameCensus, sameCache⟩ :=
    installed.startsAtCheckpointReopen rows next sameReturn nextReturned cache owner slot seen.phaseEffects seen.ptrEq
  refine ⟨handle, start, seen.releases, ⟨cacheOpen, makeCache, cacheAction, cacheSource, ?_⟩,
    ?_, selectedReads, ?_, ?_, (fun _ _ => seen.readsReleasedFile), ⟨next, reopened, currentEq⟩, ?_, lock,
    files.symm ▸ installed.cacheReferences, files.symm ▸ installed.cacheDirectory, contents, get, set, compare,
    ?_, pins, ?_, ?_, ?_⟩
  · rw [rawTable, reached]
    exact rawOpen
  · rw [currentEq]
    exact readerRan
  · rw [seen.reopen.admission.raw.sameLock, seen.reopen.admission.raw.appendHandle]
    exact (seen.stableNames _ (.inr (.inl rfl))).trans ((seen.originalNames _ (.inr (.inl rfl))).trans
      ((seen.reader.opening.reads.sameObjects.2.1.symm).trans seen.reader.lockObject).symm)
  · rw [seen.reopen.admission.seed.sameHandle, seen.reopen.admission.seed.openedHandle]
    exact (seen.stableNames _ (.inl rfl)).trans ((seen.originalNames _ (.inl rfl)).trans
      ((seen.reader.opening.reads.sameObjects.1.symm).trans seen.reader.directoryObject).symm)
  · rw [currentEq]
    exact .recoverReadyExit current.current seen.observed next reopened
  · rw [currentEq]
    exact token
  · rw [currentEq]
    exact sameFiles
  · rw [currentEq]
    exact sameCensus
  · rw [currentEq]
    exact sameCache

end Alvoki.Storage.DiskSession
