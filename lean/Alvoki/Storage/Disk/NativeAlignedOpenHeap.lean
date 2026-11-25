import Alvoki.Storage.Disk.NativeAlignedKeeperCache
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
    ∃ (state : NativeReadyState) (opened : Reopened)
      (allocation : OpenReferenceAllocations allocatePhase allocateToken view.phase opened.installed seen.reached)
      (files : DiskTable.OpenSyncFiles) (db : DiskTable)
      (assemble : IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable),
      report.opening.finish.markedWorker report.opening.chronology directory report.opening.admission.cache
        (report.opening.admission.reached, report.opening.admission.held) =
        .ok opened (view.descriptors seen.reached, view.files seen.reached) ∧
      opened.installed = state.writer.installed ∧
      files.UsesCacheReferences seed.activeRef seed.pendingRef seed.directoryRef ∧ files.AtDirectory directory.path ∧
      (∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
          (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
            IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles),
        DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
        cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
          (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
          (fun value => liftM (IO.mkRef value)) makeCache ∧
        openSyncFilesWith (init.openDirectory directory.path) init.newRef init.newRef init.newRef makeCache entry =
          .ok files seed.afterPending) ∧
      DiskTable.OpenReferenceAssembly directory lock files assemble ∧
      installReady opened.installed allocatePhase allocateToken (fun phase token => pure (assemble phase token))
        seen.reached = .ok db allocation.afterToken ∧
      (∀ remove write rename,
        (do
          seen.schedule remove write rename
          installReady opened.installed allocatePhase allocateToken (fun phase token => pure (assemble phase token)) :
          EStateM IO.Error heap DiskTable) beforeKeeper = .ok db allocation.afterToken) ∧
      db.UsesOpenReferences directory lock files allocation.phase allocation.token ∧
      view.phase allocation.afterToken allocation.phase = some state.session.phase ∧
      view.cacheAt allocation.afterToken seed.directoryRef seed.activeRef seed.pendingRef = state.cache ∧
      view.files allocation.afterToken = state.files ∧ view.descriptors allocation.afterToken = state.census ∧
      lockIdentity lock = state.session.descriptor ∧ phaseIdentity allocation.phase = state.session.phaseRef ∧
      tokenIdentity allocation.token = state.session.sessionRef ∧
      NativeReadyReadPrefix (.ok state.session (state.census, state.files)) state history log recorded state ∧
      ∀ (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
        (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit),
        OpenPhaseCellEffects view.phase get set →
        ∀ (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool),
        ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
          handle.table = db ∧ handle.directory = directory ∧ handle.lock = lock ∧ handle.files = files ∧
          handle.phase = allocation.phase ∧ handle.token = allocation.token ∧ handle.contents = view.phase ∧
          handle.get = get ∧ handle.set = set ∧ handle.ptrEq = ptrEq ∧
          start.reached = allocation.afterToken ∧ start.current.ready.state = state ∧
          start.current.history = history ∧ start.current.submissions = log ∧
          start.current.ready.reads = recorded ∧ start.pins = [] := by
  obtain ⟨state, final, opened, worker, installed, returned, reached, path, cache, _, _, _, ready⟩ :=
    report.recoversBeforeInstallation
  obtain ⟨exactOpened, exactWorker⟩ := report.opening.finish.recoversAligned report.opening.chronology finish
    aligned report.prepared report.following report.accepted report.ordered
  rw [exactWorker] at worker
  obtain ⟨rfl, sameFinal⟩ := EStateM.Result.ok.inj worker
  have matched : (view.descriptors seen.reached, view.files seen.reached) = (state.census, state.files) :=
    (Prod.mk.injEq _ _ _ _).mpr ⟨seen.reachedCensus, seen.reachedFiles⟩ |>.trans (sameFinal.trans reached)
  have recovered : report.opening.finish.markedWorker report.opening.chronology directory report.opening.admission.cache
      (report.opening.admission.reached, report.opening.admission.held) =
      .ok exactOpened (view.descriptors seen.reached, view.files seen.reached) := by
    rw [seen.reachedCensus, seen.reachedFiles]
    exact exactWorker
  obtain ⟨allocation, phase, token, phaseFrame, tokenFrame⟩ := observe exactOpened recovered
  obtain ⟨cacheOpen, makeCache, files, actualCache, cacheSource, allocatedCache, usesCache, atPath, _, _, _, _, _, _, _, _, _, _⟩ := seed.installs
  have constructor := DiskTable.openReferenceAssembly directory lock files
  obtain ⟨allocated, references, stored⟩ := allocation.installs constructor
  obtain ⟨sameOpened, workerAgain, session⟩ := report.opening.finish.reachesInstaller report.opening.chronology
    report.opening.markerFound returned
  have samePayload := (EStateM.Result.ok.inj (exactWorker.symm.trans (workerAgain.trans
    (congrArg (EStateM.Result.ok sameOpened) sameFinal.symm)))).1
  subst sameOpened
  have cacheReached : view.cacheAt seen.reached seed.directoryRef seed.activeRef seed.pendingRef = state.cache := by
    have projected := seen.returns (fun _ => pure (.ok ())) (fun _ _ => pure ()) (fun _ _ => pure ())
    exact (congrArg Prod.fst projected.2.2.2.2).trans cache.symm
  have readyStored : view.phase allocation.afterToken allocation.phase = some state.session.phase := by
    rw [session]
    exact stored
  refine ⟨state, exactOpened, allocation, files, _, _, recovered, installed, usesCache, atPath,
    ⟨cacheOpen, makeCache, actualCache, cacheSource, allocatedCache⟩, constructor, allocated, ?_,
    references, readyStored, tokenFrame.cache.trans (phaseFrame.cache.trans cacheReached),
    tokenFrame.files.trans (phaseFrame.files.trans (congrArg Prod.snd matched)),
    tokenFrame.census.trans (phaseFrame.census.trans (congrArg Prod.fst matched)), ?_, ?_, ?_, ready, ?_⟩
  · intro remove write rename
    simp only [Bind.bind, EStateM.bind, (seen.returns remove write rename).1, allocated]
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

end Alvoki.Storage.DiskSession
