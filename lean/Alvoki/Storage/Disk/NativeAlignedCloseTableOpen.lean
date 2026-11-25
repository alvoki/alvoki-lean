import Alvoki.Storage.Disk.NativeOpenCloseAdmissionTrace
import Alvoki.Storage.Disk.NativeMarkedTableOpen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap stream : Type} {input : FilePath} {state : NativeReadyState}
  {files : NativeCloseFiles state} {inventory : DescriptorInventory}
  {layout : CanonicalKeeperLayout state.releasedFiles.image state.writer.history}
  {selected : SelectedIntegrityCheckpoint state.writer.published.durable state.releasedFiles.image.directory.active.manifest
    state.writer.checkpoint}
  {reader : NativeCloseAlignedReads files input inventory layout selected}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {before : heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}

/-- Local observations of the aligned opening that follows a successful
close. The checkpoint and WAL reports are from the same chosen close
reader. The admission starts at the raw heap returned by close. -/
structure RawAlignedReopenEffects (reader : NativeCloseAlignedReads files input inventory layout selected)
    (view : OpenCloseHeapView heap FileImage) (calls : RawOpenAdmissionCallbacks heap)
    (init : OpenSyncCacheCallbacks heap) (before : heap)
    (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat)
    (allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed)))
    (allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)) (stream : Type) where
  admission : RawAlignedReopenAdmission reader view calls init before
  fileCalls : MarkedTemporaryReadCalls heap
  directoryCalls : MarkedDirectoryReadCalls heap stream
  slotOf : heap → stream → DescriptorSlot
  callbacks : AlignedKeeperCacheCallbacks heap
  checkpoint : NativeMarkedCheckpointReadHeap admission.seed reader.chronology fileCalls
  listing : MarkedDirectoryReadReport checkpoint directoryCalls slotOf
  extents : MarkedWalExtentReports checkpoint listing
  beforeKeeper : heap
  seals : MarkedSealReadChain admission.seed fileCalls reader.chronology.seals listing.reached beforeKeeper
  keeper : AlignedKeeperCacheReport reader.opening.finish view init admission.raw.afterFlock admission.seed
    (callbacks.withFileReads fileCalls) beforeKeeper
  sameLookup : fileCalls.stat = calls.lookup
  flat : optionalMetadataWith (fileCalls.stat (state.session.directory.file .wal)) admission.seed.afterPending =
    .ok none admission.seed.afterPending
  marker : IO.FS.Metadata
  marked : optionalMetadataWith (fileCalls.stat (state.session.directory.file .walBoundary)) admission.seed.afterPending =
    .ok (some marker) admission.seed.afterPending
  allocations : ∀ opened,
    reader.opening.finish.recoverFromCensus reader.chronology.metadataRelease reader.chronology.runs.released
      reader.chronology.sealRelease state.session.directory reader.opening.admission.cache
      (reader.opening.admission.reached, reader.opening.admission.held) =
      .ok opened (view.descriptors keeper.reached, view.files keeper.reached) →
    ∃ allocation : OpenReferenceAllocations allocatePhase allocateToken view.phase opened.installed keeper.reached,
      phaseIdentity allocation.phase = reader.opening.callbacks.nextRef ∧
      tokenIdentity allocation.token = reader.opening.callbacks.nextRef + 1 ∧
      CacheAllocationFrame view admission.seed.directoryRef admission.seed.activeRef admission.seed.pendingRef
        keeper.reached allocation.afterPhase ∧
      CacheAllocationFrame view admission.seed.directoryRef admission.seed.activeRef admission.seed.pendingRef
        allocation.afterPhase allocation.afterToken

variable (effects : RawAlignedReopenEffects reader view calls init before phaseIdentity tokenIdentity
  allocatePhase allocateToken stream)

/-- The actual held worker for this reopening uses the cache initialized
by the admission, including its original pending descriptor cell. -/
def RawAlignedReopenEffects.recover
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (resolved : DiskDirectory) (cache : DiskTable.OpenSyncFiles) : EStateM IO.Error heap Reopened :=
  calls.recoverMarkedWithCacheRefs effects.fileCalls effects.directoryCalls effects.callbacks
    effects.admission.seed.directoryRef effects.admission.seed.activeRef effects.admission.seed.pendingRef
    remove write rename bootstrap resolved cache

/-- The shared native open schedule, interpreted from the preceding
close's exact returned heap. -/
def RawAlignedReopenEffects.openTable
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
      IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles) : EStateM.Result IO.Error heap DiskTable :=
  calls.runOpen input init makeCache (fun resolved lock cache => do
    let opened ← effects.recover remove write rename bootstrap resolved cache
    installReady opened.installed allocatePhase allocateToken
      (fun phase token => pure (assemble resolved lock cache phase token))) before

variable {log : List DatabaseSubmissions} {recorded : List RecordedSnapshotRead}

/-- The whole next opening returns the table carrying the same state
that the close/reopen model selected. Observations of the allocator
are local to the heap reached by that same read and repair sequence. -/
theorem RawAlignedReopenEffects.opens
    (retained : state.writer.RetainedReady state.session.directory state.session.descriptor)
    (pending : PendingClientReplay log recorded state.writer.history)
    (bounded : ∀ read ∈ recorded, read.BoundedBy state.writer.history.length)
    {plan : ClosedReadyReopenLayout state.writer state.releasedFiles}
    {reader : NativeCloseAlignedReads files input inventory plan.layout selected}
    (seen : RawAlignedReopenEffects reader view calls init before phaseIdentity tokenIdentity
      allocatePhase allocateToken stream)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
      IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files)) :
    let report := reader.markedReport retained pending bounded
    let lockIdentity := fun handle => (view.handle seen.admission.raw.afterFlock handle).2.1.description
    ∃ (installed : MarkedHeapInstallation report view init seen.admission.raw.afterFlock seen.admission.seed
        seen.admission.raw.lock lockIdentity phaseIdentity tokenIdentity allocatePhase allocateToken seen.keeper.reached)
      (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles),
      DiskTable.OpenSyncFiles.IsOpenAction state.session.directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk state.session.directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      seen.openTable remove write rename bootstrap assemble makeCache =
        .ok installed.table installed.allocation.afterToken := by
  let report := reader.markedReport retained pending bounded
  exact report.opensAlignedFromAdmission seen.admission.raw seen.admission.seed reader.opening.finish rfl
    seen.checkpoint seen.listing seen.extents seen.seals seen.keeper seen.sameLookup seen.flat seen.marked
    remove write rename bootstrap assemble constructs seen.allocations

section

variable {root : DiskDirectory} {modelHistory : List WAL.Write}
  {report : MarkedOpenSuccessReports input root modelHistory log recorded}
  {entry reached : heap} {seed : OpenSyncCacheAllocations report.opening.admission.opened view init entry}
  {lock : IO.FS.Handle} {lockIdentity : IO.FS.Handle → Nat}

/-- The same exact returned table can start at the ready position with
the client's already proved history. The two histories agree by refinement. -/
private theorem startsAtSameHistory
    (installed : MarkedHeapInstallation report view init entry seed lock lockIdentity phaseIdentity tokenIdentity
      allocatePhase allocateToken reached)
    {priorHistory : List WAL.Write} (rows : modelHistory = priorHistory)
    (next : NativeReadPosition priorHistory log)
    (sameReturn : report.opening.finish.run report.opening.chronology = next.opened)
    (reported : next.opened = .ok next.state.session (next.state.census, next.state.files))
    (cache : next.state.cache = report.opening.admission.cache)
    (owner : next.state.owner = report.opening.admission.owner)
    (slot : next.state.directorySlot = report.opening.admission.cached)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (phaseEffects : OpenPhaseCellEffects view.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      start.current = ⟨priorHistory, log, next⟩ ∧ handle.table = installed.table ∧
      handle.lock = lock ∧ handle.files = installed.files ∧
      handle.phase = installed.allocation.phase ∧ handle.token = installed.allocation.token ∧
      handle.get = get ∧ handle.set = set ∧ handle.ptrEq = ptrEq ∧
      start.reached = installed.allocation.afterToken ∧ start.pins = [] ∧
      view.files start.reached = next.state.files ∧ view.descriptors start.reached = next.state.census ∧
      view.cacheAt start.reached seed.directoryRef seed.activeRef seed.pendingRef = next.state.cache := by
  subst priorHistory
  obtain ⟨handle, start, table, _, sameLock, sameCache, phase, token, _, getEq, setEq, compared,
    current, heap, pins, files, census, cached, _, _, _, _, _⟩ :=
    installed.startsAtReportedPosition next sameReturn reported cache owner slot phaseEffects ptrEq
  exact ⟨handle, start, current, table, sameLock, sameCache, phase, token, getEq, setEq, compared, heap, pins, files,
    census, cached⟩

end

variable {opened : NativeOpenedHandle heap} {initial current : NativeOpenedPosition opened}
  {active : IO.Ref (Option (FilePath × IO.FS.Handle))}
  {pending : IO.Ref (List (FilePath × IO.FS.Handle))}
  {directory : IO.Ref (Option IO.FS.Handle)}

/-- A finite trace on an opened table can close that exact table, run a
healthy aligned reopen from its returned heap, and admit later calls
at the new table's reported ready position. The selected reader is the
one from the close/reopen edge that preserves the client's history. -/
theorem NativeOpenedTrace.closesThenOpensAligned
    (prior : NativeOpenedTrace initial instructions events current)
    (references : opened.files.UsesCacheReferences active pending directory)
    (view : OpenCloseHeapView heap FileImage) (closeCalls : OpenCloseCallbacks heap)
    (samePhase : view.phase = opened.contents) (sameGet : closeCalls.getPhase = opened.get)
    (sameSet : @closeCalls.set (Phase Installed) = opened.set)
    (observed : NativeCloseReopenObservation current.current.ready.state input)
    (close : OpenCloseObservation observed.close.report view closeCalls opened.lock opened.phase
      active pending directory current.reached)
    (success : observed.close.report.result = .ok ())
    (openCalls : RawOpenAdmissionCallbacks heap) (init : OpenSyncCacheCallbacks heap)
    (observe : ∀ after, current.closeOnOpenedCells closeCalls active pending directory = .ok () after →
      ∀ (plan : ClosedReadyReopenLayout current.current.ready.state.writer current.current.ready.state.releasedFiles)
        (selected : SelectedIntegrityCheckpoint current.current.ready.state.writer.published.durable
          current.current.ready.state.releasedFiles.image.directory.active.manifest current.current.ready.state.writer.checkpoint)
        (reader : NativeCloseAlignedReads observed.files input observed.inventory plan.layout selected),
        Nonempty (RawAlignedReopenEffects reader view openCalls init after phaseIdentity tokenIdentity
          allocatePhase allocateToken stream))
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
      IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files)) :
    let state := current.current.ready.state
    opened.table.close = closeSchedule opened.phase.get (fun _ => opened.lock.unlock)
      (active.set none) (pending.set []) (directory.set none) (opened.phase.set .closed) ∧
    ∃ (next : NativeReadPosition current.current.history current.current.submissions)
      (after : heap) (plan : ClosedReadyReopenLayout state.writer state.releasedFiles)
      (selected : SelectedIntegrityCheckpoint state.writer.published.durable
        state.releasedFiles.image.directory.active.manifest state.writer.checkpoint)
      (reader : NativeCloseAlignedReads observed.files input observed.inventory plan.layout selected)
      (seen : RawAlignedReopenEffects reader view openCalls init after phaseIdentity tokenIdentity
        allocatePhase allocateToken stream)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      current.closeOnOpenedCells closeCalls active pending directory = .ok () after ∧
      opened.contents after opened.phase = some .closed ∧
      view.files after = state.releasedFiles ∧ view.descriptors after = observed.inventory ∧
      NativeCloseSelectedReads reader ∧ NativeCloseReopenStep current.current.ready observed next ∧
      NativeExecutionTrace initial.current (events ++ [.closedAndReopened input (.ok ())]) start.current ∧
      seen.openTable remove write rename bootstrap assemble makeCache = .ok handle.table start.reached ∧
      start.current = ⟨current.current.history, current.current.submissions, next⟩ ∧
      handle.lock = seen.admission.raw.lock ∧
      handle.get = opened.get ∧ handle.set = opened.set ∧ handle.ptrEq = opened.ptrEq ∧ start.pins = [] ∧
      view.files start.reached = next.state.files ∧ view.descriptors start.reached = next.state.census ∧
      view.cacheAt start.reached seen.admission.seed.directoryRef seen.admission.seed.activeRef
        seen.admission.seed.pendingRef = next.state.cache := by
  intro state
  obtain ⟨source, next, reopened, trace, physical⟩ :=
    prior.closesAndReopens references view closeCalls samePhase sameGet sameSet observed close
  rw [success] at trace physical
  obtain ⟨after, returned, shut, _, files, census⟩ := physical
  obtain ⟨plan, selected, reader, nextReturned, nextOpened, _, owner, slot, cache, _, reads⟩ := reopened.exactOpen
  obtain ⟨valid, rows, previous⟩ := current.current.ready.readPrefix.refines
  have pendingReplay : PendingClientReplay current.current.submissions current.current.ready.reads state.writer.history := by
    simpa only [state, rows] using previous
  have bounded : ∀ read ∈ current.current.ready.reads, read.BoundedBy state.writer.history.length := by
    simpa only [state, rows] using current.current.ready.readPrefix.readsBounded
  obtain ⟨seen⟩ := observe after returned plan selected reader
  obtain ⟨installed, _, makeCache, _, _, rawOpen⟩ :=
    RawAlignedReopenEffects.opens valid.retained pendingReplay bounded seen remove write rename bootstrap assemble constructs
  have phaseEffects : OpenPhaseCellEffects view.phase opened.get opened.set := by
    rw [samePhase]
    exact opened.phaseEffects
  obtain ⟨handle, start, reachedPosition, table, lock, _, _, _, getEq, setEq, compared, reachedHeap, pins,
    sameFiles, sameCensus, sameCache⟩ := startsAtSameHistory installed rows next nextOpened.symm
      (nextOpened.trans nextReturned) cache owner slot phaseEffects opened.ptrEq
  refine ⟨source, next, after, plan, selected, reader, seen, makeCache, handle, start,
    returned, shut, files, census, reads, reopened, ?_, ?_, reachedPosition, lock, getEq, setEq, compared,
    pins, sameFiles, sameCensus, sameCache⟩
  · rw [reachedPosition]
    exact trace
  · rw [table, reachedHeap]
    exact rawOpen

end Alvoki.Storage.DiskSession
