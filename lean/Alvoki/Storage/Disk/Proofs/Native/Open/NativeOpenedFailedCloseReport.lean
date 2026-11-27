import Alvoki.Storage.Disk.Proofs.Native.Open.NativeAlignedCloseTableOpen
import Alvoki.Storage.Disk.Proofs.Native.Checkpoint.NativeAlignedCheckpointReopenEffects
import Alvoki.Storage.Disk.Proofs.Native.Open.NativeOpenErrorLockFinalization

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- A returned unlock error leaves the phase and cache installed. The
later raw close targets the last slot of the same lock description.
The next aligned open begins at its observed returned heap. -/
structure NativeOpenedFailedCloseReport (current : NativeOpenedPosition opened) (input : FilePath)
    (view : OpenCloseHeapView heap FileImage) where
  active : IO.Ref (Option (FilePath × IO.FS.Handle))
  pending : IO.Ref (List (FilePath × IO.FS.Handle))
  directory : IO.Ref (Option IO.FS.Handle)
  references : opened.files.UsesCacheReferences active pending directory
  closeCalls : OpenCloseCallbacks heap
  samePhase : view.phase = opened.contents
  sameGet : closeCalls.getPhase = opened.get
  sameSet : @closeCalls.set (Phase Installed) = opened.set
  observed : NativeCloseReopenObservation current.current.ready.state input
  close : OpenCloseObservation observed.close.report view closeCalls opened.lock opened.phase
    active pending directory current.reached
  cause : IO.Error
  failed : observed.close.report.result = .error cause
  beforeDrop : heap
  slot : DescriptorSlot
  sameDescription : slot.description = current.current.ready.state.session.descriptor
  finalHandle : IO.FS.Handle
  release : IO.FS.Handle → heap → heap
  interval : LockCensusTrace current.current.ready.state.session.directory slot.description
    (view.descriptors close.afterUnlock) (view.files close.afterUnlock) (view.descriptors beforeDrop) (view.files beforeDrop)
  finalized : RawOpenErrorLockFinalization view current.current.ready.state.session.directory
    release finalHandle slot beforeDrop
  last : (view.descriptors finalized.reached).references slot.description = []
  plan : ClosedReadyReopenLayout current.current.ready.state.writer current.current.ready.state.releasedFiles
  selected : SelectedIntegrityCheckpoint current.current.ready.state.writer.published.durable
    current.current.ready.state.releasedFiles.image.directory.active.manifest current.current.ready.state.writer.checkpoint
  reader : NativeCloseAlignedReads observed.files input observed.inventory plan.layout selected
  openCalls : RawOpenAdmissionCallbacks heap
  init : OpenSyncCacheCallbacks heap
  stream : Type
  phaseIdentity : IO.Ref (Phase Installed) → Nat
  tokenIdentity : IO.Ref Unit → Nat
  allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))
  allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)
  reopen : RawAlignedReopenEffects reader view openCalls init finalized.reached phaseIdentity tokenIdentity
    allocatePhase allocateToken stream
  remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)
  write : FilePath → ByteArray → EStateM IO.Error heap Unit
  rename : FilePath → FilePath → EStateM IO.Error heap Unit
  bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened
  assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
    IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable
  constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files)

variable {current : NativeOpenedPosition opened} {input : FilePath} {view : OpenCloseHeapView heap FileImage}

/-- The actual final slot drop is the event that releases the old lock.
Its census and files agree with the entry of the chosen next opener. -/
structure NativeOpenedFailedCloseReport.Released (seen : NativeOpenedFailedCloseReport current input view) : Prop where
  close : seen.observed.CloseReturned
  liveSlot : (view.handle seen.beforeDrop seen.finalHandle).2.1 = seen.slot
  rawDrop : seen.release seen.finalHandle seen.beforeDrop = seen.finalized.reached
  priorHeld : ¬ TryLockObserves (view.files seen.beforeDrop).owners current.current.ready.state.session.directory (.ok true)
  returnFiles : view.files seen.finalized.reached = current.current.ready.state.releasedFiles
  returnCensus : view.descriptors seen.finalized.reached = seen.observed.inventory
  available : TryLockObserves (view.files seen.finalized.reached).owners current.current.ready.state.session.directory (.ok true)

/-- Relate the observed slot close to the model's last-reference edge.
The pre-release observations start at the failed unlock's actual heap. -/
theorem NativeOpenedFailedCloseReport.releases (seen : NativeOpenedFailedCloseReport current input view) : seen.Released := by
  let state := current.current.ready.state
  have failedView := seen.close.unlockedView
  rw [seen.failed] at failedView
  have initialCensus : view.descriptors seen.close.afterUnlock = state.census := failedView.2.2.2
  have initialFiles : view.files seen.close.afterUnlock = state.files := failedView.2.2.1
  have earlier := seen.interval
  rw [seen.sameDescription, initialCensus, initialFiles] at earlier
  let census := view.descriptors seen.beforeDrop
  let event := seen.slot.closeEvent
  have live : census.references state.session.descriptor ≠ [] := by
    exact List.ne_nil_of_mem (census.mem_references.mpr ⟨seen.slot, seen.finalized.live, rfl, seen.sameDescription⟩)
  have last : (census.afterDrops [event]).references state.session.descriptor = [] := by
    rw [← seen.sameDescription, ← seen.finalized.census]
    exact seen.last
  have finalFiles : view.files seen.finalized.reached = census.dropLockState state.session.descriptor [event]
      state.session.directory (view.files seen.beforeDrop) := by
    rw [← seen.sameDescription]
    exact seen.finalized.files
  have censusEq : view.descriptors seen.finalized.reached = seen.observed.inventory := seen.reopen.admission.raw.entryCensus
  have finished := earlier.drops [event]
  obtain ⟨failed, _, released, vacant⟩ := seen.observed.close.followsFailedUnlock
    current.current.ready.readPrefix.refines.1 seen.failed finished
  have same : view.files seen.beforeDrop = state.files := by
    have image := earlier.reached.2.2
    change view.files seen.beforeDrop = (if census.references state.session.descriptor = [] then state.releasedFiles else state.files) at image
    simpa only [ite_eq_right live] using image
  have held : ¬ TryLockObserves (view.files seen.beforeDrop).owners state.session.directory (.ok true) :=
    fun allowed => live (earlier.freshFlockAllowed.mp allowed)
  have removed : ∀ reference ∈ census.references state.session.descriptor, event.removes reference = true := by
    intro reference member
    by_cases hit : event.removes reference = true
    · exact hit
    · have survives : reference ∈ (census.afterDrops [event]).references state.session.descriptor := by
        rw [DescriptorInventory.references_afterDrops]
        exact List.mem_filter.mpr ⟨member, by simp [Bool.eq_false_iff.mpr hit]⟩
      simp only [last, List.not_mem_nil] at survives
  have releasedEq : census.dropLockState state.session.descriptor [event] state.session.directory
      (view.files seen.beforeDrop) = state.releasedFiles := by
    change census.dropLockState state.session.descriptor [event] state.session.directory (view.files seen.beforeDrop) =
      (if (census.afterDrops [event]).references state.session.descriptor = [] then state.releasedFiles else state.files) at released
    simpa only [last, ite_true] using released
  have available := vacant.mpr last
  refine ⟨?_, seen.finalized.sameSlot, seen.finalized.finalized, held, finalFiles.trans releasedEq, censusEq,
    finalFiles.symm ▸ available⟩
  simp only [NativeCloseReopenObservation.CloseReturned, seen.failed]
  exact ⟨failed, census, view.files seen.beforeDrop, event, earlier, live, same, held, removed,
    censusEq.symm.trans seen.finalized.census, censusEq ▸ seen.sameDescription ▸ seen.last, releasedEq, available⟩

/-- The failed public close, final descriptor drop and successful aligned
open all use their respective reached raw heaps. The next table carries
the history and read ledger of the previous session. -/
structure NativeOpenedFailedCloseReport.Returned (seen : NativeOpenedFailedCloseReport current input view)
    {handle : NativeOpenedHandle heap} (start : NativeOpenedPosition handle) : Prop where
  sourceClose : opened.table.close = closeSchedule opened.phase.get (fun _ => opened.lock.unlock)
    (seen.active.set none) (seen.pending.set []) (seen.directory.set none) (opened.phase.set .closed)
  error : current.closeOnOpenedCells seen.closeCalls seen.active seen.pending seen.directory =
    .error seen.cause seen.close.afterUnlock
  held : view.Matches opened.phase seen.active seen.pending seen.directory seen.close.afterUnlock
    current.current.ready.state.closeState
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
  recovery : ∃ next : NativeReadPosition current.current.history current.current.submissions,
    NativeCloseReopenStep current.current.ready seen.observed next ∧
    start.current = ⟨current.current.history, current.current.submissions, next⟩
  common : NativeExecutionStep current.current (.closedAndReopened input (.error seen.cause)) start.current
  lock : handle.lock = seen.reopen.admission.raw.lock
  cache : handle.files.UsesCacheReferences seen.reopen.admission.seed.activeRef seen.reopen.admission.seed.pendingRef
    seen.reopen.admission.seed.directoryRef
  cacheDirectory : handle.files.AtDirectory current.current.ready.state.session.directory.path
  contents : handle.contents = view.phase
  get : handle.get = opened.get
  set : handle.set = opened.set
  ptrEq : handle.ptrEq = opened.ptrEq
  token : seen.tokenIdentity handle.token = start.current.ready.state.session.sessionRef
  unpinned : start.pins = []
  files : view.files start.reached = start.current.ready.state.files
  census : view.descriptors start.reached = start.current.ready.state.census
  cached : view.cacheAt start.reached seen.reopen.admission.seed.directoryRef seen.reopen.admission.seed.activeRef
    seen.reopen.admission.seed.pendingRef = start.current.ready.state.cache

/-- A reported failed close can lead to a new ready position only after
its reported last-reference release. The same reader supplies both the
selected physical files and the continuation of the client replay. -/
theorem NativeOpenedFailedCloseReport.reaches (seen : NativeOpenedFailedCloseReport current input view) :
    ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle), seen.Returned start := by
  let state := current.current.ready.state
  have released := seen.releases
  obtain ⟨source, actual⟩ := current.closesOnOpenedReferences seen.references view seen.closeCalls
    seen.samePhase seen.sameGet seen.sameSet seen.observed seen.close released.close
  rw [seen.failed] at actual
  obtain ⟨closeError, immediatelyHeld⟩ := actual
  obtain ⟨valid, rows, previous⟩ := current.current.ready.readPrefix.refines
  have selected := seen.observed.files.reopensReleasedAlignedAt valid.retained rows previous
    current.current.ready.readPrefix.readsBounded seen.plan seen.selected seen.reader
  obtain ⟨next, reopened, readerRan, nextReturned, owner, slot, cache, selectedReads⟩ :=
    NativeCloseReopenStep.fromSelectedOpen current.current.ready seen.observed released.close seen.reader selected
  have pending : PendingClientReplay current.current.submissions current.current.ready.reads state.writer.history := by
    simpa only [state, rows] using previous
  have bounded : ∀ read ∈ current.current.ready.reads, read.BoundedBy state.writer.history.length := by
    simpa only [state, rows] using current.current.ready.readPrefix.readsBounded
  obtain ⟨installed, cacheOpen, makeCache, cacheAction, cacheSource, rawOpen⟩ :=
    RawAlignedReopenEffects.opens valid.retained pending bounded seen.reopen seen.remove seen.write seen.rename
      seen.bootstrap seen.assemble seen.constructs
  have sameReturn := (seen.reader.markedReport_run valid.retained pending bounded).trans readerRan
  have phases : OpenPhaseCellEffects view.phase opened.get opened.set := seen.samePhase.symm ▸ opened.phaseEffects
  obtain ⟨handle, start, currentEq, rawTable, lock, files, contents, get, set, compare, token, reached, pins,
    sameFiles, sameCensus, sameCache⟩ :=
    installed.startsAtCheckpointReopen rows next sameReturn nextReturned cache owner slot phases opened.ptrEq
  have common := NativeExecutionStep.closeAndReopen current.current seen.observed next reopened
  rw [seen.failed] at common
  refine ⟨handle, start, source, closeError, immediatelyHeld, released, ⟨cacheOpen, makeCache, cacheAction, cacheSource, ?_⟩,
    ?_, selectedReads, ⟨next, reopened, currentEq⟩, ?_, lock, files.symm ▸ installed.cacheReferences,
    files.symm ▸ installed.cacheDirectory, contents, get, set, compare, ?_, pins, ?_, ?_, ?_⟩
  · rw [rawTable, reached]
    exact rawOpen
  · rw [currentEq]
    exact readerRan
  · rw [currentEq]
    exact common
  · rw [currentEq]
    exact token
  · rw [currentEq]
    exact sameFiles
  · rw [currentEq]
    exact sameCensus
  · rw [currentEq]
    exact sameCache

end Alvoki.Storage.DiskSession
