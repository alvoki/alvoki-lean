import Alvoki.Storage.Disk.Checkpoint.PhysicalBarrierReopen
import Alvoki.Storage.Disk.NativeMarkedTableOpen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair CheckpointPublication

section

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {published : Image} {vacant : TryLockObserves retry.owners directory (.ok true)}
  {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {bindings : FilePath → Option Nat}
  {opening : CheckpointBarrierAlignedReports input directory inventory retry layout published vacant selected bindings}
  {chronology : CapturedMarkedReadCensus opening.reads opening.finish.readCustody}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}

/-- One recovered checkpoint reader indexes the raw admission, the
bounded reads and aligned repair, and the reference allocation effects. -/
structure RawAlignedCheckpointReopenEffects
    (opening : CheckpointBarrierAlignedReports input directory inventory retry layout published vacant selected bindings)
    (chronology : CapturedMarkedReadCensus opening.reads opening.finish.readCustody)
    (view : OpenCloseHeapView heap FileImage) (calls : RawOpenAdmissionCallbacks heap)
    (init : OpenSyncCacheCallbacks heap) (entry : heap)
    (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat)
    (allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed)))
    (allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)) (stream : Type) where
  raw : RawOpenAdmissionReport opening.admission view calls entry
  seed : OpenSyncCacheAllocations opening.admission.opened view init raw.afterFlock
  fileCalls : MarkedTemporaryReadCalls heap
  directoryCalls : MarkedDirectoryReadCalls heap stream
  slotOf : heap → stream → DescriptorSlot
  callbacks : AlignedKeeperCacheCallbacks heap
  checkpoint : NativeMarkedCheckpointReadHeap seed chronology fileCalls
  listing : MarkedDirectoryReadReport checkpoint directoryCalls slotOf
  extents : MarkedWalExtentReports checkpoint listing
  beforeKeeper : heap
  seals : MarkedSealReadChain seed fileCalls chronology.seals listing.reached beforeKeeper
  keeper : AlignedKeeperCacheReport opening.finish view init raw.afterFlock seed
    (callbacks.withFileReads fileCalls) beforeKeeper
  sameLookup : fileCalls.stat = calls.lookup
  flat : optionalMetadataWith (fileCalls.stat (directory.file .wal)) seed.afterPending =
    .ok none seed.afterPending
  marker : IO.FS.Metadata
  marked : optionalMetadataWith (fileCalls.stat (directory.file .walBoundary)) seed.afterPending =
    .ok (some marker) seed.afterPending
  allocations : ∀ opened,
    opening.finish.recoverFromCensus chronology.metadataRelease chronology.runs.released
      chronology.sealRelease directory opening.admission.cache
      (opening.admission.reached, opening.admission.held) =
      .ok opened (view.descriptors keeper.reached, view.files keeper.reached) →
    ∃ allocation : OpenReferenceAllocations allocatePhase allocateToken view.phase opened.installed keeper.reached,
      phaseIdentity allocation.phase = opening.callbacks.nextRef ∧
      tokenIdentity allocation.token = opening.callbacks.nextRef + 1 ∧
      CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef keeper.reached allocation.afterPhase ∧
      CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef allocation.afterPhase allocation.afterToken

def RawAlignedCheckpointReopenEffects.openTable
    (seen : RawAlignedCheckpointReopenEffects opening chronology view calls init entry phaseIdentity tokenIdentity
      allocatePhase allocateToken stream)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles) : EStateM.Result IO.Error heap DiskTable :=
  let seed := seen.seed
  calls.runOpen input init makeCache (fun resolved lock cache => do
    let opened ← calls.recoverMarkedWithCacheRefs seen.fileCalls seen.directoryCalls seen.callbacks seed.directoryRef
      seed.activeRef seed.pendingRef remove write rename bootstrap resolved cache
    installReady opened.installed allocatePhase allocateToken
      (fun phase token => pure (assemble resolved lock cache phase token))) entry

end

section

variable {heap : Type} {input : FilePath} {view : OpenCloseHeapView heap FileImage}
  {init : OpenSyncCacheCallbacks heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
  {directory : DiskDirectory} {history modelHistory : List WAL.Write}
  {log : List DatabaseSubmissions} {recorded : List RecordedSnapshotRead}
  {marked : MarkedOpenSuccessReports input directory modelHistory log recorded}
  {entry final : heap} {seed : OpenSyncCacheAllocations marked.opening.admission.opened view init entry}
  {lock : IO.FS.Handle} {lockIdentity : IO.FS.Handle → Nat}

theorem MarkedHeapInstallation.startsAtCheckpointReopen
    (installed : MarkedHeapInstallation marked view init entry seed lock lockIdentity phaseIdentity tokenIdentity
      allocatePhase allocateToken final)
    (rows : modelHistory = history) (next : NativeReadPosition history log)
    (sameReturn : marked.opening.finish.run marked.opening.chronology = next.opened)
    (returned : next.opened = .ok next.state.session (next.state.census, next.state.files))
    (cache : next.state.cache = marked.opening.admission.cache) (owner : next.state.owner = marked.opening.admission.owner)
    (slot : next.state.directorySlot = marked.opening.admission.cached)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects view.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      start.current = ⟨history, log, next⟩ ∧ handle.table = installed.table ∧ handle.lock = lock ∧
      handle.files = installed.files ∧ handle.contents = view.phase ∧ handle.get = get ∧ handle.set = set ∧
      handle.ptrEq = ptrEq ∧ tokenIdentity handle.token = next.state.session.sessionRef ∧
      start.reached = installed.allocation.afterToken ∧ start.pins = [] ∧
      view.files start.reached = next.state.files ∧ view.descriptors start.reached = next.state.census ∧
      view.cacheAt start.reached seed.directoryRef seed.activeRef seed.pendingRef = next.state.cache := by
  subst history
  obtain ⟨handle, start, table, _, sameLock, sameCache, _, _, contents, getEq, setEq, compared,
    current, heap, pins, files, census, cached, _, _, _, _, token⟩ :=
    installed.startsAtReportedPosition next sameReturn returned cache owner slot effects ptrEq
  exact ⟨handle, start, current, table, sameLock, sameCache, contents, getEq, setEq, compared, token,
    heap, pins, files, census, cached⟩

end

namespace RawAlignedCheckpointReopenEffects

section

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory}
  {history modelHistory : List WAL.Write} {log : List DatabaseSubmissions}
  {inventory : DescriptorInventory} {retry : LockedFileState FileImage}
  {layout : CanonicalKeeperLayout retry.image modelHistory} {published : Image}
  {vacant : TryLockObserves retry.owners directory (.ok true)} {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {bindings : FilePath → Option Nat}
  {opening : CheckpointBarrierAlignedReports input directory inventory retry layout published vacant selected bindings}
  {chronology : CapturedMarkedReadCensus opening.reads opening.finish.readCustody}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
  (seen : RawAlignedCheckpointReopenEffects opening chronology view calls init entry phaseIdentity tokenIdentity
    allocatePhase allocateToken stream)
  (next : NativeReadPosition history log)
  (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
  (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
  (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
  (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
  (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
  (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
  (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit)
  (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)

/-- The actual open returns the table and ready position of the fixed
reader, with the same cache, callback projections, and reference allocations. -/
structure ReturnedAt where
  cacheOpen : IO DiskTable.OpenSyncFiles
  makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
    IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles
  cacheAction : DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen
  cacheSource : cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
    (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
    (fun value => liftM (IO.mkRef value)) makeCache
  cacheUses : let cache := makeCache seen.seed.directoryRef seen.seed.activeRef seen.seed.pendingRef
    cache.UsesCacheReferences seen.seed.activeRef seen.seed.pendingRef seen.seed.directoryRef ∧ cache.AtDirectory directory.path
  handle : NativeOpenedHandle heap
  start : NativeOpenedPosition handle
  rawOpen : seen.openTable remove write rename bootstrap assemble makeCache = .ok handle.table start.reached
  position : start.current = ⟨history, log, next⟩
  lock : handle.lock = seen.raw.lock
  references : handle.files.UsesCacheReferences seen.seed.activeRef seen.seed.pendingRef seen.seed.directoryRef
  resolvedDirectory : next.state.session.directory = directory
  directory : handle.files.AtDirectory directory.path
  contents : handle.contents = view.phase
  readsPhase : handle.get = get
  writesPhase : handle.set = set
  comparesTokens : handle.ptrEq = ptrEq
  tokenRef : tokenIdentity handle.token = next.state.session.sessionRef
  pins : start.pins = []
  files : view.files start.reached = next.state.files
  census : view.descriptors start.reached = next.state.census
  cache : view.cacheAt start.reached seen.seed.directoryRef seen.seed.activeRef seen.seed.pendingRef = next.state.cache
  repairCensus : next.state.census = opening.finish.census
  capturedCache : next.state.cache = opening.admission.cache
  lockOwner : next.state.owner = opening.admission.owner
  directorySlot : next.state.directorySlot = opening.admission.cached
  allocation : ∃ allocated : OpenReferenceAllocations allocatePhase allocateToken view.phase
      next.state.writer.installed seen.keeper.reached,
    (handle.phase, handle.token, start.reached) = (allocated.phase, allocated.token, allocated.afterToken)

end

section

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory}
  {history modelHistory : List WAL.Write} {log : List DatabaseSubmissions} {recorded : List RecordedSnapshotRead}
  {report : MarkedOpenSuccessReports input directory modelHistory log recorded} {bindings : FilePath → Option Nat}
  {opening : CheckpointBarrierAlignedReports input directory report.inventory report.retry report.layout report.published
    report.vacant report.selected bindings}
  {chronology : CapturedMarkedReadCensus opening.reads opening.finish.readCustody}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
  (seen : RawAlignedCheckpointReopenEffects opening chronology view calls init entry phaseIdentity tokenIdentity
    allocatePhase allocateToken stream)
  (next : NativeReadPosition history log)
  (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
  (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
  (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
  (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
  (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
  (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
  (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit)
  (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)

variable {get set}

/-- Install the selected aligned reader's actual return at the proved
ready position. Survivor selection and the preceding effects belong to
the caller; the common suffix uses the reader and chronology once. -/
theorem installsAtReportedPosition (sameHistory : modelHistory = history)
    (sameReturn : opening.finish.runFromCensus chronology.metadataRelease chronology.runs.released
      chronology.sealRelease = next.opened)
    (returned : next.opened = .ok next.state.session (next.state.census, next.state.files))
    (cache : next.state.cache = opening.admission.cache) (owner : next.state.owner = opening.admission.owner)
    (slot : next.state.directorySlot = opening.admission.cached)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files))
    (effects : OpenPhaseCellEffects view.phase get set) :
    Nonempty (seen.ReturnedAt next remove write rename bootstrap assemble get set ptrEq) := by
  subst history
  let selectedReport : MarkedOpenSuccessReports input directory modelHistory log recorded :=
    { report with opening := ⟨opening.admission, opening.callbacks, opening.reads, .aligned opening.finish,
        chronology, opening.marker, opening.markerFound⟩ }
  obtain ⟨installed, cacheOpen, makeCache, cacheAction, cacheSource, cacheUses, openedTable⟩ :=
    selectedReport.opensAlignedFromAdmission seen.raw seen.seed opening.finish rfl seen.checkpoint seen.listing
      seen.extents seen.seals seen.keeper seen.sameLookup seen.flat seen.marked remove write rename bootstrap assemble
      constructs seen.allocations
  obtain ⟨handle, start, table, resolved, lock, files, phase, token, contents, getEq, setEq, compared, position,
    reached, pins, sameFiles, sameCensus, sameCache, _, _, _, _, tokenRef⟩ :=
    installed.startsAtReportedPosition next sameReturn returned cache owner slot effects ptrEq
  obtain ⟨_, atRepair, _⟩ := selectedReport.opening.finish.reachesInstaller chronology opening.markerFound
    (sameReturn.trans returned)
  have sameRepair := (EStateM.Result.ok.inj (atRepair.symm.trans installed.recovered)).2
  have resolvedAtPosition := start.directory.trans resolved
  rw [position] at resolvedAtPosition
  refine ⟨{
    cacheOpen := cacheOpen
    makeCache := makeCache
    cacheAction := cacheAction
    cacheSource := cacheSource
    cacheUses := cacheUses
    handle := handle
    start := start
    rawOpen := ?_
    position := position
    lock := lock
    references := files.symm ▸ installed.cacheReferences
    directory := files.symm ▸ installed.cacheDirectory
    contents := contents
    readsPhase := getEq
    writesPhase := setEq
    comparesTokens := compared
    tokenRef := tokenRef
    pins := pins
    files := sameFiles
    census := sameCensus
    cache := sameCache
    resolvedDirectory := resolvedAtPosition
    repairCensus := (congrArg Prod.fst sameRepair).trans seen.keeper.reachedCensus
    capturedCache := cache
    lockOwner := owner
    directorySlot := slot
    allocation := ?_ }⟩
  · rw [table, reached]
    exact openedTable
  · have stored := start.stored
    rw [contents, phase, reached, position, next.readPrefix.refines.1.phase] at stored
    have allocated := installed.allocation.keepsPhase.trans installed.allocation.initialized
    have payload := Phase.ready.inj (Option.some.inj (allocated.symm.trans stored))
    let Issued (value : Installed) : Prop :=
      ∃ refs : OpenReferenceAllocations allocatePhase allocateToken view.phase value seen.keeper.reached,
        (handle.phase, handle.token, start.reached) = (refs.phase, refs.token, refs.afterToken)
    have receipt : Issued installed.opened.installed := ⟨installed.allocation, by rw [phase, token, reached]⟩
    exact Eq.mp (congrArg Issued payload) receipt

end

end RawAlignedCheckpointReopenEffects

end Alvoki.Storage.DiskSession
