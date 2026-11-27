import Alvoki.Storage.Disk.Proofs.Keeper.NativeAlignedKeeperCache
import Alvoki.Storage.Disk.NativeOpenReadyTrace

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting

/-- A reference allocation preserves the three existing cache cells and
the filesystem and descriptor projections used by the database. -/
structure CacheAllocationFrame {heap image : Type} (view : OpenCloseHeapView heap image)
    (directory : IO.Ref (Option IO.FS.Handle))
    (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (before after : heap) : Prop where
  directoryCell : view.directory after directory = view.directory before directory
  activeCell : view.active after active = view.active before active
  pendingCell : view.pending after pending = view.pending before pending
  handles : ∀ handle, view.handle after handle = view.handle before handle
  files : view.files after = view.files before
  census : view.descriptors after = view.descriptors before

theorem CacheAllocationFrame.cache {heap image : Type} {view : OpenCloseHeapView heap image}
    {directory active pending before after} (observed : CacheAllocationFrame view directory active pending before after) :
    view.cacheAt after directory active pending = view.cacheAt before directory active pending := by
  simp only [OpenCloseHeapView.cacheAt, observed.directoryCell, observed.activeCell, observed.pendingCell,
    funext observed.handles]

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {checkpoint : Option (PackedTable × UInt64)}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {vacant : TryLockObserves retry.owners directory (.ok true)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {calls : CapturedAlignedCallbacks admission} {reads : CapturedMarkedReadReports admission layout published}

private theorem CapturedKeeperFinish.recoversAligned
    {selectedFinish : CapturedKeeperFinish calls reads vacant selected}
    (chronology : CapturedMarkedReadCensus reads selectedFinish.reader)
    (finish : CapturedAlignedFinish calls reads vacant selected)
    (aligned : selectedFinish = .aligned finish)
    (prepared : Prepared retry.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    ∃ opened, selectedFinish.markedWorker chronology directory admission.cache (admission.reached, admission.held) =
      .ok opened (finish.census, { admission.held with image := retry.image.syncDirectory.syncKeeper }) := by
  subst selectedFinish
  exact finish.recoversFromCensus chronology prepared following accepted ordered

variable {heap : Type} {log : List DatabaseSubmissions} {recorded : List RecordedSnapshotRead}

/-- The references and starting position of a marked table installed from
the heap reached by recovery. The same normalized result supplies both
the replay history and the phase value stored in the returned table. -/
structure MarkedHeapInstallation
    (report : MarkedOpenSuccessReports input directory history log recorded)
    (view : OpenCloseHeapView heap FileImage) (init : OpenSyncCacheCallbacks heap) (entry : heap)
    (seed : OpenSyncCacheAllocations report.opening.admission.opened view init entry)
    (lock : IO.FS.Handle) (lockIdentity : IO.FS.Handle → Nat)
    (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat)
    (allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed)))
    (allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit))
    (reached : heap) where
  state : NativeReadyState
  opened : Reopened
  allocation : OpenReferenceAllocations allocatePhase allocateToken view.phase opened.installed reached
  files : DiskTable.OpenSyncFiles
  table : DiskTable
  assemble : IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable
  recovered : report.opening.finish.markedWorker report.opening.chronology directory report.opening.admission.cache
    (report.opening.admission.reached, report.opening.admission.held) =
    .ok opened (view.descriptors reached, view.files reached)
  nativeReturned : report.opening.finish.run report.opening.chronology =
    .ok state.session (state.census, state.files)
  cacheCaptured : state.cache = report.opening.admission.cache
  ownerCaptured : state.owner = report.opening.admission.owner
  directoryCaptured : state.directorySlot = report.opening.admission.cached
  installed : opened.installed = state.writer.installed
  cacheReferences : files.UsesCacheReferences seed.activeRef seed.pendingRef seed.directoryRef
  cacheDirectory : files.AtDirectory directory.path
  cacheOpened : ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles),
    DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
    cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
      (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
      (fun value => liftM (IO.mkRef value)) makeCache ∧
    openSyncFilesWith (init.openDirectory directory.path) init.newRef init.newRef init.newRef makeCache entry =
      .ok files seed.afterPending
  constructor : DiskTable.OpenReferenceAssembly directory lock files assemble
  allocated : installReady opened.installed allocatePhase allocateToken (fun phase token => pure (assemble phase token))
    reached = .ok table allocation.afterToken
  references : table.UsesOpenReferences directory lock files allocation.phase allocation.token
  phaseStored : view.phase allocation.afterToken allocation.phase = some state.session.phase
  cachePreserved : view.cacheAt allocation.afterToken seed.directoryRef seed.activeRef seed.pendingRef = state.cache
  filesPreserved : view.files allocation.afterToken = state.files
  censusPreserved : view.descriptors allocation.afterToken = state.census
  lockRef : lockIdentity lock = state.session.descriptor
  phaseRef : phaseIdentity allocation.phase = state.session.phaseRef
  tokenRef : tokenIdentity allocation.token = state.session.sessionRef
  ready : NativeReadyReadPrefix (.ok state.session (state.census, state.files)) state history log recorded state
  fromOpen : ∀ (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
      (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit),
    OpenPhaseCellEffects view.phase get set →
    ∀ (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool),
    ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      handle.table = table ∧ handle.directory = directory ∧ handle.lock = lock ∧ handle.files = files ∧
      handle.phase = allocation.phase ∧ handle.token = allocation.token ∧ handle.contents = view.phase ∧
      handle.get = get ∧ handle.set = set ∧ handle.ptrEq = ptrEq ∧
      start.reached = allocation.afterToken ∧ start.current.ready.state = state ∧
      start.current.history = history ∧ start.current.submissions = log ∧
      start.current.ready.reads = recorded ∧ start.pins = []

/-- Start the raw opened-table trace at the already reached position of
the same marked return and admission. The raw heap has that position's
cache, file image and census, and the common position carries its ledger. -/
theorem MarkedHeapInstallation.startsAtReportedPosition
    {report : MarkedOpenSuccessReports input directory history log recorded}
    {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap} {entry : heap}
    {seed : OpenSyncCacheAllocations report.opening.admission.opened view init entry}
    {lock : IO.FS.Handle} {lockIdentity : IO.FS.Handle → Nat}
    {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
    {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
    {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)} {reached : heap}
    (installed : MarkedHeapInstallation report view init entry seed lock lockIdentity phaseIdentity tokenIdentity
      allocatePhase allocateToken reached) (next : NativeReadPosition history log)
    (sameReturn : report.opening.finish.run report.opening.chronology = next.opened)
    (reported : next.opened = .ok next.state.session (next.state.census, next.state.files))
    (nextCache : next.state.cache = report.opening.admission.cache)
    (nextOwner : next.state.owner = report.opening.admission.owner)
    (nextDirectorySlot : next.state.directorySlot = report.opening.admission.cached)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects view.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      handle.table = installed.table ∧ handle.directory = directory ∧ handle.lock = lock ∧ handle.files = installed.files ∧
      handle.phase = installed.allocation.phase ∧ handle.token = installed.allocation.token ∧ handle.contents = view.phase ∧
      handle.get = get ∧ handle.set = set ∧ handle.ptrEq = ptrEq ∧
      start.current = ⟨history, log, next⟩ ∧ start.reached = installed.allocation.afterToken ∧ start.pins = [] ∧
      view.files start.reached = next.state.files ∧ view.descriptors start.reached = next.state.census ∧
      view.cacheAt start.reached seed.directoryRef seed.activeRef seed.pendingRef = next.state.cache ∧
      next.state.owner = installed.state.owner ∧ next.state.directorySlot = installed.state.directorySlot ∧
      lockIdentity handle.lock = next.state.session.descriptor ∧
      phaseIdentity handle.phase = next.state.session.phaseRef ∧ tokenIdentity handle.token = next.state.session.sessionRef := by
  obtain ⟨sameSession, sameFiles⟩ := EStateM.Result.ok.inj (installed.nativeReturned.symm.trans (sameReturn.trans reported))
  obtain ⟨handle, original, table, path, sameLock, files, phase, token, contents, getEq, setEq, compared, _,
    originalState, _, _, _, _⟩ := installed.fromOpen get set effects ptrEq
  have nextDirectory : next.state.session.directory = handle.directory := by
    rw [← sameSession, ← originalState]
    exact original.directory
  have stored : handle.contents installed.allocation.afterToken handle.phase = some next.state.session.phase := by
    rw [contents, phase, ← sameSession]
    exact installed.phaseStored
  let start := NativeOpenedPosition.fromOpen handle ⟨history, log, next⟩ installed.allocation.afterToken nextDirectory stored
  refine ⟨handle, start, table, path, sameLock, files, phase, token, contents, getEq, setEq, compared, rfl, rfl, rfl,
    installed.filesPreserved.trans (congrArg Prod.snd sameFiles),
    installed.censusPreserved.trans (congrArg Prod.fst sameFiles),
    installed.cachePreserved.trans (installed.cacheCaptured.trans nextCache.symm),
    nextOwner.trans installed.ownerCaptured.symm, nextDirectorySlot.trans installed.directoryCaptured.symm, ?_, ?_, ?_⟩
  · rw [sameLock, ← sameSession]
    exact installed.lockRef
  · rw [phase, ← sameSession]
    exact installed.phaseRef
  · rw [token, ← sameSession]
    exact installed.tokenRef

/-- The exact raw recovery result supplies the payload and heap for
the two installer allocations. The projected worker identifies that
payload with the one already proved for the installation. -/
theorem MarkedHeapInstallation.installsAfterRawRecovery
    {report : MarkedOpenSuccessReports input directory history log recorded}
    {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap} {entry : heap}
    {seed : OpenSyncCacheAllocations report.opening.admission.opened view init entry}
    {lock : IO.FS.Handle} {lockIdentity : IO.FS.Handle → Nat}
    {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
    {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
    {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)} {reached : heap}
    (installed : MarkedHeapInstallation report view init entry seed lock lockIdentity phaseIdentity tokenIdentity
      allocatePhase allocateToken reached)
    (rawRecovery : EStateM IO.Error heap Reopened) {opened : Reopened}
    (rawReturned : rawRecovery seed.afterPending = .ok opened reached)
    (workerReturned : report.opening.finish.markedWorker report.opening.chronology directory report.opening.admission.cache
      (report.opening.admission.reached, report.opening.admission.held) =
        .ok opened (view.descriptors reached, view.files reached)) :
    (do
      let opened ← rawRecovery
      installReady opened.installed allocatePhase allocateToken
        (fun phase token => pure (installed.assemble phase token)) : EStateM IO.Error heap DiskTable)
      seed.afterPending = .ok installed.table installed.allocation.afterToken := by
  have samePayload := (EStateM.Result.ok.inj (workerReturned.symm.trans installed.recovered)).1
  simp only [Bind.bind, EStateM.bind, rawReturned, samePayload, installed.allocated]

/-- Allocate the real phase and token after a marked repair whose returned
checkpoint, WAL, file image, descriptor census and cache have been matched
to the reached raw heap. Each allocation frames the existing cache. -/
theorem MarkedOpenSuccessReports.installsFromRepairedHeap
    (report : MarkedOpenSuccessReports input directory history log recorded)
    (view : OpenCloseHeapView heap FileImage) (init : OpenSyncCacheCallbacks heap) (entry : heap)
    (seed : OpenSyncCacheAllocations report.opening.admission.opened view init entry)
    (reached : heap)
    (lock : IO.FS.Handle) (lockIdentity : IO.FS.Handle → Nat)
    (locked : lockIdentity lock = report.opening.admission.owner.description)
    (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat)
    (allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed)))
    (allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit))
    (worker : ∃ opened,
      report.opening.finish.markedWorker report.opening.chronology directory report.opening.admission.cache
        (report.opening.admission.reached, report.opening.admission.held) =
        .ok opened (view.descriptors reached, view.files reached))
    (cached : view.cacheAt reached seed.directoryRef seed.activeRef seed.pendingRef = report.opening.admission.cache)
    (observe : ∀ opened,
      report.opening.finish.markedWorker report.opening.chronology directory report.opening.admission.cache
        (report.opening.admission.reached, report.opening.admission.held) =
        .ok opened (view.descriptors reached, view.files reached) →
      ∃ allocation : OpenReferenceAllocations allocatePhase allocateToken view.phase opened.installed reached,
        phaseIdentity allocation.phase = report.opening.callbacks.nextRef ∧
        tokenIdentity allocation.token = report.opening.callbacks.nextRef + 1 ∧
        CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef reached allocation.afterPhase ∧
        CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef allocation.afterPhase allocation.afterToken) :
    Nonempty (MarkedHeapInstallation report view init entry seed lock lockIdentity phaseIdentity tokenIdentity
      allocatePhase allocateToken reached) := by
  obtain ⟨state, final, opened, returnedWorker, installed, returned, reachedState, path, cache, owner, cachedDirectory, _, ready⟩ :=
    report.recoversBeforeInstallation
  obtain ⟨exactOpened, exactWorker⟩ := worker
  rw [exactWorker] at returnedWorker
  obtain ⟨rfl, sameFinal⟩ := EStateM.Result.ok.inj returnedWorker
  have matched := sameFinal.trans reachedState
  obtain ⟨allocation, phase, token, phaseFrame, tokenFrame⟩ := observe exactOpened exactWorker
  obtain ⟨cacheOpen, makeCache, files, actualCache, cacheSource, allocatedCache, usesCache, atPath, _, _, _, _, _, _, _, _, _, _⟩ := seed.installs
  have constructor := DiskTable.openReferenceAssembly directory lock files
  obtain ⟨allocated, references, stored⟩ := allocation.installs constructor
  obtain ⟨sameOpened, workerAgain, session⟩ := report.opening.finish.reachesInstaller report.opening.chronology
    report.opening.markerFound returned
  have samePayload := (EStateM.Result.ok.inj (exactWorker.symm.trans (workerAgain.trans
    (congrArg (EStateM.Result.ok sameOpened) sameFinal.symm)))).1
  subst sameOpened
  have readyStored : view.phase allocation.afterToken allocation.phase = some state.session.phase := by
    rw [session]
    exact stored
  refine ⟨{
    state := state
    opened := exactOpened
    allocation := allocation
    files := files
    table := _
    assemble := _
    recovered := exactWorker
    nativeReturned := returned.trans (congrArg (EStateM.Result.ok state.session) reachedState)
    cacheCaptured := cache
    ownerCaptured := owner
    directoryCaptured := cachedDirectory
    installed := installed
    cacheReferences := usesCache
    cacheDirectory := atPath
    cacheOpened := ⟨cacheOpen, makeCache, actualCache, cacheSource, allocatedCache⟩
    constructor := constructor
    allocated := allocated
    references := references
    phaseStored := readyStored
    cachePreserved := tokenFrame.cache.trans (phaseFrame.cache.trans (cached.trans cache.symm))
    filesPreserved := tokenFrame.files.trans (phaseFrame.files.trans (congrArg Prod.snd matched))
    censusPreserved := tokenFrame.census.trans (phaseFrame.census.trans (congrArg Prod.fst matched))
    lockRef := ?_
    phaseRef := ?_
    tokenRef := ?_
    ready := ready
    fromOpen := ?_ }⟩
  · rw [session]
    exact locked
  · rw [session]
    exact phase
  · rw [session]
    exact token
  · intro get set effects ptrEq
    let handle : NativeOpenedHandle heap :=
      ⟨_, directory, lock, files, allocation.phase, allocation.token, references, view.phase, get, set, effects, ptrEq⟩
    let current : NativeExecutionPosition :=
      ⟨history, log, ⟨.ok state.session (state.census, state.files), state, state, recorded, ready⟩⟩
    let initial := NativeOpenedPosition.fromOpen handle current allocation.afterToken path readyStored
    exact ⟨handle, initial, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Use the heap reached by the reported raw aligned repair for the
actual two installer allocations. The decoded checkpoint and WAL come
from that same aligned worker. The returned DiskTable carries the cache
record allocated before the repair and the phase installed after it. -/
theorem MarkedOpenSuccessReports.installsFromAlignedCache
    (report : MarkedOpenSuccessReports input directory history log recorded)
    (finish : CapturedAlignedFinish report.opening.callbacks report.opening.reads report.vacant report.selected)
    (aligned : report.opening.finish = .aligned finish)
    (view : OpenCloseHeapView heap FileImage) (init : OpenSyncCacheCallbacks heap) (entry : heap)
    (seed : OpenSyncCacheAllocations report.opening.admission.opened view init entry)
    {callbacks : AlignedKeeperCacheCallbacks heap} {beforeKeeper : heap}
    (seen : AlignedKeeperCacheReport finish view init entry seed callbacks beforeKeeper)
    (lock : IO.FS.Handle) (lockIdentity : IO.FS.Handle → Nat)
    (locked : lockIdentity lock = report.opening.admission.owner.description)
    (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat)
    (allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed)))
    (allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit))
    (observe : ∀ opened,
      report.opening.finish.markedWorker report.opening.chronology directory report.opening.admission.cache
        (report.opening.admission.reached, report.opening.admission.held) =
        .ok opened (view.descriptors seen.reached, view.files seen.reached) →
      ∃ allocation : OpenReferenceAllocations allocatePhase allocateToken view.phase opened.installed seen.reached,
        phaseIdentity allocation.phase = report.opening.callbacks.nextRef ∧
        tokenIdentity allocation.token = report.opening.callbacks.nextRef + 1 ∧
        CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef seen.reached allocation.afterPhase ∧
        CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef allocation.afterPhase allocation.afterToken) :
    ∃ installed : MarkedHeapInstallation report view init entry seed lock lockIdentity phaseIdentity tokenIdentity
        allocatePhase allocateToken seen.reached,
      ∀ remove write rename,
        (do
          seen.schedule remove write rename
          installReady installed.opened.installed allocatePhase allocateToken
            (fun phase token => pure (installed.assemble phase token)) : EStateM IO.Error heap DiskTable)
          beforeKeeper = .ok installed.table installed.allocation.afterToken := by
  obtain ⟨opened, worker⟩ := report.opening.finish.recoversAligned report.opening.chronology finish aligned
    report.prepared report.following report.accepted report.ordered
  have recovered : report.opening.finish.markedWorker report.opening.chronology directory report.opening.admission.cache
      (report.opening.admission.reached, report.opening.admission.held) =
      .ok opened (view.descriptors seen.reached, view.files seen.reached) := by
    rw [seen.reachedCensus, seen.reachedFiles]
    exact worker
  have cached := congrArg Prod.fst
    (seen.returns (fun _ => pure (.ok ())) (fun _ _ => pure ()) (fun _ _ => pure ())).2.2.2.2
  obtain ⟨installed⟩ := report.installsFromRepairedHeap view init entry seed seen.reached lock lockIdentity
    locked phaseIdentity tokenIdentity allocatePhase allocateToken ⟨opened, recovered⟩ cached observe
  refine ⟨installed, ?_⟩
  intro remove write rename
  simp only [Bind.bind, EStateM.bind, (seen.returns remove write rename).1, installed.allocated]

end Alvoki.Storage.DiskSession
