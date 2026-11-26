import Alvoki.Storage.Disk.NativeBootstrapMarkerPhysical
import Alvoki.Storage.Disk.NativeBootstrapOpenHeap
import Alvoki.Storage.Disk.NativeAlignedOpenHeap

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

private abbrev BootstrapImage := WalSegmentRotation.State

private def ownsAcross (view : OpenCloseHeapView heap BootstrapImage) (before : heap) : List heap → Prop
  | [] => True
  | after :: rest => (view.files after).owners = (view.files before).owners ∧ ownsAcross view after rest

private theorem ownsAcross_last {view : OpenCloseHeapView heap BootstrapImage} {start : heap}
    {reached : List heap} (kept : ownsAcross view start reached) :
    (view.files (reached.getLastD start)).owners = (view.files start).owners := by
  induction reached generalizing start with
  | nil => rfl
  | cons next rest earlier =>
    cases rest with
    | nil => exact kept.1
    | cons reached rest => exact (earlier kept.2).trans kept.1

variable {heap : Type} {input : FilePath} {directory : DiskDirectory} {report : EmptyOpenSuccessReports input directory}
  {view : OpenCloseHeapView heap BootstrapImage} {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {seed : OpenSyncCacheAllocations report.captured.opened view init entry} {calls : FreshBootstrapCacheCalls heap}

/-- Preserve the acquired owner at each reached primitive, including
both pending-reference operations and both directory barriers. -/
def FreshBootstrapCacheChronology.PreservesOwner (raw : FreshBootstrapCacheChronology seed calls) : Prop :=
  ownsAcross view seed.afterPending
    [raw.afterList, raw.afterEmpty, raw.prepared, raw.keeper.produced, raw.keeper.recorded,
      raw.keeper.consumed, raw.keeper.reached, raw.keeperDirectory.reached, raw.marker.produced,
      raw.marker.recorded, raw.marker.consumed, raw.marker.reached, raw.afterRename, raw.markerDirectory.reached]

/-- The same admitted namespace supplies the fresh raw worker, its
allocation-time cache and the physical keeper and marker reports. -/
structure FreshBootstrapOpenHeap
    (report : EmptyOpenSuccessReports input directory)
    {seed : OpenSyncCacheAllocations report.captured.opened view init entry}
    (raw : FreshBootstrapCacheChronology seed calls) where
  keeper : BootstrapFreshZeroKeeper report.listed
  route : report.keeper = .fresh keeper
  keeperPhysical : FreshBootstrapKeeperPhysical keeper raw.keeper raw.keeperDirectory
  markerPhysical : FreshBootstrapMarkerPhysical raw keeperPhysical (route ▸ report.handoff) report.effects
  flatAbsent : calls.metadata (directory.file .wal) seed.afterPending = .ok none seed.afterPending
  markerAbsent : calls.metadata (directory.file .walBoundary) seed.afterPending = .ok none seed.afterPending
  listing : raw.entries = report.listed.scan.scan.entries directory.path
  ownerFrames : raw.PreservesOwner
  directoryProjection : view.handle raw.markerDirectory.reached seed.handle = view.handle seed.afterPending seed.handle

private theorem EmptyOpenSuccessReports.returnedBootstrapPayload (report : EmptyOpenSuccessReports input directory)
    {opened : Reopened} {after : BootstrapImage}
    (worker : report.calls.bootstrapAt directory report.captured.cache report.before.image = .ok opened after) :
    opened = ⟨.empty, 0, 0, 0⟩ := by
  unfold BootstrapOpenCalls.bootstrapAt bootstrapSegmentedWith bootstrapEmptyWith at worker
  simp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure] at worker
  split at worker <;> try contradiction
  split at worker <;> try contradiction
  split at worker <;> try contradiction
  exact (EStateM.Result.ok.inj worker).1.symm

namespace FreshBootstrapOpenHeap

variable {raw : FreshBootstrapCacheChronology seed calls}

private theorem reachesFiles (seen : FreshBootstrapOpenHeap report raw) :
    ∃ (state : NativeReadyState) (after : LockedFileState BootstrapImage),
      let final := raw.markerDirectory.reached
      let opened : Reopened := ⟨.empty, 0, 0, 0⟩
      report.calls.run report.admission = .ok state.session after ∧
      state.session = ⟨directory, report.calls.slot.description, .ready opened.installed,
        report.calls.nextRef, report.calls.nextRef + 1⟩ ∧
      (NativeOpenSuccessReports.empty report).UsesReachedState state after ∧
      view.files final = after ∧ view.descriptors final = state.census ∧
      view.cacheAt final seed.directoryRef seed.activeRef seed.pendingRef = state.cache ∧
      NativeReadyReadPrefix (.ok state.session (state.census, state.files)) state [] [] [] state := by
  obtain ⟨state, after, opened, worker, _, returned, session, reached, ready⟩ := report.recoversBeforeInstallation
  have emptyPayload := report.returnedBootstrapPayload worker
  subst opened
  have published := report.marker.publishedImage report.admission (report.empty.symm ▸ bootstrap_fresh)
    report.keeper.rotationHealthy returned
  have owned : after.owners = report.before.owners.set (directory.file .lock) (some report.calls.slot.description) := by
    have run := returned
    rw [report.calls.runMarkerless report.admission report.captured.captures.1,
      runOpenWithInstallation_outcome, runOpenWithImage_acquired, worker] at run
    exact (congrArg LockedFileState.owners (EStateM.Result.ok.inj run).2).symm
  have initial := seed.pendingFiles.trans (seed.activeFiles.trans (seed.directoryFiles.trans seed.openedFiles))
  have owner := ownsAcross_last seen.ownerFrames
  change (view.files raw.markerDirectory.reached).owners = (view.files seed.afterPending).owners at owner
  rw [initial] at owner
  change (view.files raw.markerDirectory.reached).owners =
    report.before.owners.set (directory.file .lock) (some report.calls.slot.description) at owner
  obtain ⟨_, _, _, _, image, _, _, _, _, _, census, _, _, _⟩ := seen.markerPhysical.settles
  have files : view.files raw.markerDirectory.reached = after := by
    change LockedFileState.mk _ _ = LockedFileState.mk _ _
    exact (LockedFileState.mk.injEq _ _ _ _).mpr ⟨image.trans published.symm, owner.trans owned.symm⟩
  obtain ⟨_, _, _, _, _, _, _, _, directoryValue, activeValue, pendingValue, _, _⟩ := raw.returns
  have cache : view.cacheAt raw.markerDirectory.reached seed.directoryRef seed.activeRef seed.pendingRef = state.cache := by
    rw [reached.2.2.2.2.1]
    simp only [OpenCloseHeapView.cacheAt, directoryValue, activeValue, pendingValue, Option.map_some,
      Option.map_none, List.map_nil, seen.directoryProjection, seed.sameHandle, seed.openedHandle]
    rfl
  exact ⟨state, after, returned, session, reached, files, census.trans reached.2.1.symm, cache, ready⟩

/-- A fresh open's physical publication supplies the exact heap and
payload for `installReady`. Its returned references, reached files,
cache and empty client position belong to the same native schedule. -/
theorem installs (seen : FreshBootstrapOpenHeap report raw)
    (lock : IO.FS.Handle) (lockIdentity : IO.FS.Handle → Nat)
    (locked : lockIdentity lock = report.calls.slot.description)
    (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat)
    (allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed)))
    (allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit))
    (allocation : OpenReferenceAllocations allocatePhase allocateToken view.phase
      (⟨.empty, 0, 0, 0⟩ : Reopened).installed raw.markerDirectory.reached)
    (phaseID : phaseIdentity allocation.phase = report.calls.nextRef)
    (tokenID : tokenIdentity allocation.token = report.calls.nextRef + 1)
    (phaseFrame : CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef
      raw.markerDirectory.reached allocation.afterPhase)
    (tokenFrame : CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef
      allocation.afterPhase allocation.afterToken)
    (phaseInodes : seen.keeperPhysical.inodes allocation.afterPhase = seen.keeperPhysical.inodes raw.markerDirectory.reached)
    (tokenInodes : seen.keeperPhysical.inodes allocation.afterToken = seen.keeperPhysical.inodes allocation.afterPhase) :
    ∃ (state : NativeReadyState) (after : LockedFileState BootstrapImage) (files : DiskTable.OpenSyncFiles)
      (db : DiskTable) (assemble : IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable),
      (∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
          (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
            IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles),
        DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
        cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
          (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
          (fun value => liftM (IO.mkRef value)) makeCache ∧
        openSyncFilesWith (init.openDirectory directory.path) init.newRef init.newRef init.newRef makeCache entry =
          .ok files seed.afterPending) ∧
      files.UsesBootstrapCacheSchedules directory seed.activeRef seed.pendingRef seed.directoryRef ∧
      calls.list directory.path seed.afterPending = .ok (report.listed.scan.scan.entries directory.path) raw.afterList ∧
      DiskTable.OpenReferenceAssembly directory lock files assemble ∧
      (∀ marked : EStateM IO.Error heap Reopened,
        (do
          let opened ← recoverSegmentedWalWith
            (rejectFlatWalWith directory (calls.metadata (directory.file .wal)))
            (calls.metadata (directory.file .walBoundary)) marked
            (calls.run directory seed.directoryRef seed.activeRef seed.pendingRef)
          installReady opened.installed allocatePhase allocateToken (fun phase token => pure (assemble phase token)) :
            EStateM IO.Error heap DiskTable) seed.afterPending = .ok db allocation.afterToken) ∧
      db.UsesOpenReferences directory lock files allocation.phase allocation.token ∧
      view.phase allocation.afterToken allocation.phase = some state.session.phase ∧
      view.files allocation.afterToken = after ∧ view.descriptors allocation.afterToken = state.census ∧
      view.cacheAt allocation.afterToken seed.directoryRef seed.activeRef seed.pendingRef = state.cache ∧
      lockIdentity lock = state.session.descriptor ∧ phaseIdentity allocation.phase = state.session.phaseRef ∧
      tokenIdentity allocation.token = state.session.sessionRef ∧
      report.calls.run report.admission = .ok state.session after ∧
      (NativeOpenSuccessReports.empty report).UsesReachedState state after ∧
      (seen.keeperPhysical.inodes allocation.afterToken).crashBytes
        (BootstrapZeroKeeperRoute.settledImage (.fresh seen.keeper)).active = [ByteArray.empty] ∧
      (seen.keeperPhysical.inodes allocation.afterToken).crashBytes report.marker.inodeState.active = [WAL.Boundary.encode 0] ∧
      (∀ (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
        (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit),
        OpenPhaseCellEffects view.phase get set →
        ∀ (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool),
        ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
          handle.table = db ∧ handle.directory = directory ∧ handle.lock = lock ∧ handle.files = files ∧
          handle.phase = allocation.phase ∧ handle.token = allocation.token ∧ handle.contents = view.phase ∧
          handle.get = get ∧ handle.set = set ∧ handle.ptrEq = ptrEq ∧
          start.reached = allocation.afterToken ∧ start.current.ready.state = state ∧
          start.current.history = [] ∧ start.current.submissions = [] ∧ start.current.ready.reads = [] ∧ start.pins = []) ∧
      files.UsesCacheReferences seed.activeRef seed.pendingRef seed.directoryRef ∧
      files.AtDirectory directory.path := by
  obtain ⟨state, after, returned, session, physical, reachedFiles, reachedCensus, reachedCache, ready⟩ := seen.reachesFiles
  obtain ⟨cacheOpen, makeCache, files, starts, cacheSource, initialized, schedules, worker, _, _, _, cacheRefs,
    atDirectory⟩ := raw.returns
  have constructor := DiskTable.openReferenceAssembly directory lock files
  obtain ⟨allocated, references, stored⟩ := allocation.installs constructor
  have readyStored : view.phase allocation.afterToken allocation.phase = some state.session.phase := by
    rw [session]
    exact stored
  obtain ⟨_, _, _, _, _, _, _, _, keeperBytes, markerBytes, _, _, _, _⟩ := seen.markerPhysical.settles
  have inodesKept := tokenInodes.trans phaseInodes
  have listed := raw.checked
  rw [seen.listing] at listed
  refine ⟨state, after, files, _, _, ⟨cacheOpen, makeCache, starts, cacheSource, initialized⟩, schedules,
    listed, constructor, ?_, references, readyStored, tokenFrame.files.trans (phaseFrame.files.trans reachedFiles),
    tokenFrame.census.trans (phaseFrame.census.trans reachedCensus), tokenFrame.cache.trans (phaseFrame.cache.trans reachedCache),
    ?_, ?_, ?_, returned, physical, inodesKept.symm ▸ keeperBytes, inodesKept.symm ▸ markerBytes, ?_, cacheRefs, atDirectory⟩
  · intro marked
    simp [recoverSegmentedWalWith, rejectFlatWalWith, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
      seen.flatAbsent, seen.markerAbsent, worker]
    exact allocated
  · rw [session]
    exact locked
  · rw [session]
    exact phaseID
  · rw [session]
    exact tokenID
  · intro get set effects ptrEq
    let handle : NativeOpenedHandle heap :=
      ⟨_, directory, lock, files, allocation.phase, allocation.token, references, view.phase, get, set, effects, ptrEq⟩
    let current : NativeExecutionPosition :=
      ⟨[], [], ⟨.ok state.session (state.census, state.files), state, state, [], ready⟩⟩
    let initial := NativeOpenedPosition.fromOpen handle current allocation.afterToken (by rw [session]) readyStored
    exact ⟨handle, initial, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FreshBootstrapOpenHeap

end Alvoki.Storage.DiskSession
