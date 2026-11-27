import Alvoki.Storage.Disk.Proofs.Native.Open.NativeAlignedCloseTableOpen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- A successful close on the reached table, with one healthy aligned
read and repair report from the exact returned close heap. -/
structure NativeOpenedAlignedCloseReport (current : NativeOpenedPosition opened) (input : FilePath)
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
  success : observed.close.report.result = .ok ()
  openCalls : RawOpenAdmissionCallbacks heap
  init : OpenSyncCacheCallbacks heap
  stream : Type
  phaseIdentity : IO.Ref (Phase Installed) → Nat
  tokenIdentity : IO.Ref Unit → Nat
  allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))
  allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)
  observe : ∀ after, current.closeOnOpenedCells closeCalls active pending directory = .ok () after →
    ∃ (plan : ClosedReadyReopenLayout current.current.ready.state.writer current.current.ready.state.releasedFiles)
      (selected : SelectedIntegrityCheckpoint current.current.ready.state.writer.published.durable
        current.current.ready.state.releasedFiles.image.directory.active.manifest current.current.ready.state.writer.checkpoint)
      (reader : NativeCloseAlignedReads observed.files input observed.inventory plan.layout selected),
      Nonempty (RawAlignedReopenEffects reader view openCalls init after phaseIdentity tokenIdentity
        allocatePhase allocateToken stream)
  remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)
  write : FilePath → ByteArray → EStateM IO.Error heap Unit
  rename : FilePath → FilePath → EStateM IO.Error heap Unit
  bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened
  assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
    IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable
  constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files)

variable {current : NativeOpenedPosition opened} {input : FilePath} {view : OpenCloseHeapView heap FileImage}

/-- The native close, selected reader and new table share one sequence
of returned heaps. The current handle's callbacks and the new table's
fresh phase, token and cache supply the continuation. -/
structure NativeOpenedAlignedCloseReport.Returned (seen : NativeOpenedAlignedCloseReport current input view)
    {handle : NativeOpenedHandle heap} (start : NativeOpenedPosition handle) : Prop where
  sourceClose : opened.table.close = closeSchedule opened.phase.get (fun _ => opened.lock.unlock)
    (seen.active.set none) (seen.pending.set []) (seen.directory.set none) (opened.phase.set .closed)
  witnessed :
    let state := current.current.ready.state
    ∃ (after : heap) (plan : ClosedReadyReopenLayout state.writer state.releasedFiles)
      (selected : SelectedIntegrityCheckpoint state.writer.published.durable
        state.releasedFiles.image.directory.active.manifest state.writer.checkpoint)
      (reader : NativeCloseAlignedReads seen.observed.files input seen.observed.inventory plan.layout selected)
      (reopen : RawAlignedReopenEffects reader view seen.openCalls seen.init after seen.phaseIdentity seen.tokenIdentity
        seen.allocatePhase seen.allocateToken seen.stream)
      (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles),
      current.closeOnOpenedCells seen.closeCalls seen.active seen.pending seen.directory = .ok () after ∧
      opened.contents after opened.phase = some .closed ∧
      view.files after = state.releasedFiles ∧ view.descriptors after = seen.observed.inventory ∧
      DiskTable.OpenSyncFiles.IsOpenAction state.session.directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk state.session.directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      reader.run = start.current.ready.opened ∧ NativeCloseSelectedReads reader ∧
      reopen.openTable seen.remove seen.write seen.rename seen.bootstrap seen.assemble makeCache =
        .ok handle.table start.reached ∧
      handle.lock = reopen.admission.raw.lock ∧
      handle.files.UsesCacheReferences reopen.admission.seed.activeRef reopen.admission.seed.pendingRef
        reopen.admission.seed.directoryRef ∧ handle.files.AtDirectory state.session.directory.path ∧
      view.cacheAt start.reached reopen.admission.seed.directoryRef reopen.admission.seed.activeRef
        reopen.admission.seed.pendingRef = start.current.ready.state.cache
  common : NativeExecutionStep current.current (.closedAndReopened input (.ok ())) start.current
  contents : handle.contents = view.phase
  sameGet : handle.get = opened.get
  sameSet : handle.set = opened.set
  samePtrEq : handle.ptrEq = opened.ptrEq
  token : seen.tokenIdentity handle.token = start.current.ready.state.session.sessionRef
  unpinned : start.pins = []
  files : view.files start.reached = start.current.ready.state.files
  census : view.descriptors start.reached = start.current.ready.state.census

/-- The close and reopen derive one ready successor at the raw returned
table. The common edge uses the same reader and recorded close result. -/
theorem NativeOpenedAlignedCloseReport.reaches (seen : NativeOpenedAlignedCloseReport current input view) :
    ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle), seen.Returned start := by
  have prior : NativeOpenedTrace current [] [] current := .empty
  obtain ⟨source, next, after, plan, selected, reader, reopen, cacheOpen, makeCache, handle, start, closed,
    shut, released, closeCensus, cacheAction, cacheSource, readerRan, _, reads, reopened, _, rawOpen, reached,
    lock, cache, cachePath, token, contents, get, set, ptrEq, pins, files, census, cached⟩ := prior.closesThenOpensAligned
    seen.references view seen.closeCalls seen.samePhase seen.sameGet seen.sameSet seen.observed seen.close seen.success
    seen.openCalls seen.init seen.observe seen.remove seen.write seen.rename seen.bootstrap seen.assemble seen.constructs
  have edge := NativeExecutionStep.closeAndReopen current.current seen.observed next reopened
  rw [seen.success] at edge
  refine ⟨handle, start, source, ?_, ?_, contents, get, set, ptrEq, ?_, pins, ?_, ?_⟩
  · refine ⟨after, plan, selected, reader, reopen, cacheOpen, makeCache, closed, shut, released, closeCensus,
      cacheAction, cacheSource, ?_, reads, rawOpen, lock, cache, cachePath, ?_⟩
    · rw [reached]
      exact readerRan
    · rw [reached]
      exact cached
  · rw [reached]
    exact edge
  · rw [reached]
    exact token
  · rw [reached]
    exact files
  · rw [reached]
    exact census

end Alvoki.Storage.DiskSession
