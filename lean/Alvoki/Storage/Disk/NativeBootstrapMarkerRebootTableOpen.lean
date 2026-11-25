import Alvoki.Storage.Disk.NativeBootstrapMarkerDirectoryReboot
import Alvoki.Storage.Disk.RawHealthyMarkedOpenEffects

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

namespace RawBootstrapMarkerDirectoryStop.EffectiveReboot

variable {heap : Type} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {fileCalls : BootstrapOpenCalls (Cache CheckpointOpenHandle) directory before}
  {captured : BootstrapCacheOpen fileCalls.toBootstrapAdmissionCalls} {listed : BootstrapCheckedListing captured}
  {view : OpenCloseHeapView heap WalSegmentRotation.State} {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {seed : OpenSyncCacheAllocations captured.opened view init entry} {calls : FreshBootstrapCacheCalls heap}
  {observed : BootstrapReusedZeroKeeper listed} {guards : ReusedBootstrapKeeperGuards observed seed calls}
  {keeper : ReusedBootstrapKeeperHeap guards} {stop : RawBootstrapMarkerDirectoryStop keeper}
  {marker : BootstrapMarkerRenamed listed} {handoff : BootstrapKeeperMarkerRename (.reused observed) marker}
  {physical : stop.Physical handoff} (reboot : EffectiveReboot physical) (valid : BootstrapValid before.image)

/-- Interpret the selected bootstrap reboot in the marked recovery
model. The directory image and vacant owner are those of the reboot. -/
def markedInput : LockedFileState FileImage :=
  ⟨(reboot.selects valid).marked.files, (view.files reboot.rebooted).owners⟩

def layout : CanonicalKeeperLayout (reboot.markedInput valid).image [] :=
  (reboot.selects valid).marked.layout

def checkpointImage : CheckpointPublication.Image :=
  (reboot.selects valid).marked.checkpoint

theorem noCheckpoint : SelectedIntegrityCheckpoint (reboot.checkpointImage valid).durable
    (reboot.markedInput valid).image.directory.active.manifest none := by
  change SelectedIntegrityCheckpoint _ (view.files reboot.rebooted).image.metadata.active.manifest none
  rw [(reboot.selects valid).ready.manifestAbsent]
  exact .absent

private theorem prepared :
    Prepared (reboot.markedInput valid).image (reboot.layout valid).target (reboot.layout valid).plan := by
  refine ⟨rfl, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · exact Publication.Image.settled_valid (reboot.layout valid).target.acceptsTrimmed
  · simp [markedInput, BootstrapMarkedZero.files, LaterNames.settled, LaterNames.Beyond]

variable {input : FilePath}

private abbrev OpenObservation (reboot : EffectiveReboot physical) (valid : BootstrapValid before.image) :=
  MarkedReadyOpenObservations input directory (view.descriptors reboot.rebooted)
    (reboot.markedInput valid) (reboot.layout valid) (reboot.checkpointImage valid)
    (reboot.selects valid).vacant (reboot.noCheckpoint valid)

/-- The accepted marked preparation and empty replay are fixed by the
selected reboot. The caller supplies the reached read and repair events. -/
def markedReport (opening : OpenObservation (input := input) reboot valid) :
    MarkedOpenSuccessReports input directory [] [] [] where
  inventory := view.descriptors reboot.rebooted
  retry := reboot.markedInput valid
  layout := reboot.layout valid
  published := reboot.checkpointImage valid
  checkpoint := none
  selected := reboot.noCheckpoint valid
  vacant := (reboot.selects valid).vacant
  opening := opening
  prepared := reboot.prepared valid
  following := by
    intro offset occurs
    cases occurs
  accepted := (reboot.selects valid).ready.appendReady.accepted
  ordered := trivial
  wal := (reboot.selects valid).ready.walImage
  walLayout := (reboot.selects valid).ready.walCanonical.2.1
  walValid := (reboot.selects valid).ready.walCanonical.2.2
  spans := by
    intro segment occurs
    cases occurs
  active := rfl
  keeper := rfl
  kept := by
    funext offset
    rfl
  pending := ⟨.empty, .nil _, .start, .slnil, .slnil, by simp⟩
  bounded := by simp

/-- Both actual reads come from the same selected reboot objects. The
root and its stable child and object maps are local filesystem reports. -/
structure SameReboot (opening : OpenObservation (input := input) reboot valid) : Prop where
  root : opening.admission.root = captured.root
  children : ∀ name, opening.admission.view.child opening.admission.root name =
    (physical.names reboot.rebooted).child captured.root name
  objects : opening.admission.view.modelObject = (physical.names reboot.rebooted).modelObject

structure SelectedReads (opening : OpenObservation (input := input) reboot valid) : Prop where
  directoryObject : opening.reads.bindings directory.path =
    some ((view.descriptors stop.afterRename).inode captured.cached.description)
  lockObject : opening.reads.bindings (directory.file .lock) =
    some (captured.reached.inode fileCalls.slot.description)
  manifest : opening.admission.view.child opening.admission.root "MANIFEST" = none
  marker : ∃ file : opening.reads.reads.ObservesFile (directory.file .walBoundary) (WAL.Boundary.encode 0),
    file.object = (physical.names reboot.rebooted).modelObject marker.stageChild.child
  keeper : ∃ file : opening.reads.reads.ObservesFile (directory.file (.walSegment 0)) ByteArray.empty,
    file.object = (physical.names reboot.rebooted).modelObject observed.statChild.child

theorem readsSelectedReboot (opening : OpenObservation (input := input) reboot valid)
    (same : reboot.SameReboot valid opening) : reboot.SelectedReads valid opening := by
  have chosen := reboot.selects valid
  have mark := opening.reads.metadata.markerFile (WAL.Boundary.encode 0) chosen.ready.zeroMarker
  obtain ⟨markerRead, _⟩ := mark
  have rawKeeper := opening.reads.wal.keeper
  have markerID : markerRead.object = marker.stageChild.child := by
    apply Option.some.inj
    exact markerRead.bound.symm.trans ((same.children "WAL.commit").trans chosen.markerBinding)
  have lockID : opening.reads.lock = listed.lifetime.lock := by
    apply Option.some.inj
    exact opening.reads.lockEntry.symm.trans ((same.children "LOCK").trans chosen.lock)
  refine ⟨?_, ?_, (same.children "MANIFEST").trans chosen.manifestMissing, ⟨markerRead.observesFile, ?_⟩, ?_⟩
  · rw [opening.reads.canonicalDirectory, same.root, same.objects, chosen.directory]
  · rw [opening.reads.canonicalLock, lockID, same.objects, chosen.lockObject]
  · change markerRead.calls.statObject = _
    rw [← markerRead.calls.identifiedStat, markerRead.calls.statLookup.child_eq markerRead.bound, markerID, same.objects]
  · have bound := rawKeeper.bound
    change opening.admission.view.child opening.admission.root (renderWalSegmentName 0) = some rawKeeper.object at bound
    have keeperID : rawKeeper.object = observed.statChild.child := by
      apply Option.some.inj
      exact bound.symm.trans ((same.children _).trans chosen.keeperBinding)
    refine ⟨rawKeeper.observesFile, ?_⟩
    change rawKeeper.calls.statObject = _
    rw [← rawKeeper.calls.identifiedStat, rawKeeper.calls.statLookup.child_eq rawKeeper.bound, keeperID, same.objects]

private theorem exactEmptyPhase (opening : OpenObservation (input := input) reboot valid)
    {session : SegmentedSession} {census : DescriptorInventory} {files : LockedFileState FileImage}
    (returned : opening.finish.run opening.chronology = .ok session (census, files)) :
    session.phase = .ready ⟨.empty, 0, 0, 0⟩ := by
  let report := reboot.markedReport valid opening
  obtain ⟨installed, final, ran, _, _, _, normalized⟩ := opening.finish.installsFromCensus opening.chronology
    opening.markerFound report.prepared report.following report.accepted report.ordered
  obtain ⟨opened, checkpoint, _, result, reached, exactResult, _, _, phase,
    _, _, _, _, _, _, _, _, _, _, selected, replay, generation, bytes, keeperFirst, _⟩ := normalized
  have sameSession : session = result :=
    (EStateM.Result.ok.inj (returned.symm.trans ran)).1.trans (EStateM.Result.ok.inj exactResult).1
  have noCheckpoint := selected.uniqueResult (reboot.noCheckpoint valid)
  have replayEmpty : recoverSelected .empty (WAL.encode []) = .ok .empty :=
    recoverSelected_encoded .empty [] [] trivial rfl
  rw [noCheckpoint, show (none : Option (PackedTable × UInt64)).getD (.empty, 0) = (.empty, 0) from rfl,
    replayEmpty] at replay
  have empty : opened.table = .empty := (Except.ok.inj replay).symm
  rw [sameSession, phase]
  simp [Reopened.installed, empty, generation, noCheckpoint, bytes, keeperFirst, layout, BootstrapMarkedZero.layout]

private theorem choosesAligned (opening : OpenObservation (input := input) reboot valid) :
    ∃ finish : CapturedAlignedFinish opening.callbacks opening.reads (reboot.selects valid).vacant
      (reboot.noCheckpoint valid), opening.finish = .aligned finish := by
  have measured := opening.finish.usesMeasuredRepair
  have extent : opening.reads.wal.keeper.calls.metadata.byteSize.toNat = 0 :=
    opening.reads.wal.keeper.observesFile.extent
  cases chosen : opening.finish with
  | aligned finish => exact ⟨finish, rfl⟩
  | prunedAligned finish =>
    rw [chosen] at measured
    exact False.elim (measured.2 rfl)
  | longer finish =>
    rw [chosen] at measured
    change 0 < opening.reads.wal.keeper.calls.metadata.byteSize.toNat at measured
    rw [extent] at measured
    exact False.elim (Nat.lt_irrefl _ measured)

variable {nextView : OpenCloseHeapView heap FileImage}
  {nextCalls : RawOpenAdmissionCallbacks heap} {nextInit : OpenSyncCacheCallbacks heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)} {stream : Type}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)} {stage : LongKeeperStageCallbacks heap}
  {rename : FilePath → FilePath → EStateM IO.Error heap Unit}

/-- The first admitted marked open after the effective bootstrap stop
reads those same files and allocates an empty ready table on its reached
heap. Its original phase, cache, lock and fresh token seed the next call. -/
theorem opensEmptyTable (opening : OpenObservation (input := input) reboot valid)
    (same : reboot.SameReboot valid opening)
    (raw : RawHealthyMarkedOpenEffects opening nextView nextCalls nextInit reboot.rebooted
      phaseIdentity tokenIdentity allocatePhase allocateToken stream remove stage rename)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
      IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock cache, DiskTable.OpenReferenceAssembly resolved lock cache (assemble resolved lock cache))
    (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit)
    (phaseEffects : OpenPhaseCellEffects nextView.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    reboot.SelectedReads valid opening ∧
    (∃ finish : CapturedAlignedFinish opening.callbacks opening.reads (reboot.selects valid).vacant
      (reboot.noCheckpoint valid), opening.finish = .aligned finish) ∧
    (nextView.descriptors reboot.rebooted).slots = [] ∧ nextView.files reboot.rebooted = reboot.markedInput valid ∧
    ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      raw.openTable bootstrap assemble makeCache = .ok handle.table start.reached ∧
      nextView.phase start.reached handle.phase = some (.ready ⟨.empty, 0, 0, 0⟩) ∧
      start.current.ready.state.writer.installed = ⟨.empty, 0, 0, 0⟩ ∧
      handle.lock = raw.raw.lock ∧ handle.files.UsesCacheReferences raw.seed.activeRef raw.seed.pendingRef raw.seed.directoryRef ∧
      handle.contents = nextView.phase ∧ handle.get = get ∧ handle.set = set ∧ handle.ptrEq = ptrEq ∧
      nextView.files start.reached = start.current.ready.state.files ∧
      nextView.descriptors start.reached = start.current.ready.state.census ∧
      nextView.cacheAt start.reached raw.seed.directoryRef raw.seed.activeRef raw.seed.pendingRef =
        start.current.ready.state.cache ∧
      start.current.history = [] ∧ start.current.submissions = [] ∧ start.current.ready.reads = [] ∧ start.pins = [] := by
  have selected := reboot.selects valid
  let report := reboot.markedReport valid opening
  obtain ⟨_, installed, cacheOpen, makeCache, cacheAction, cacheSource, returned⟩ :=
    report.opensHealthyFromAdmission raw.raw raw.seed raw.checkpoint raw.listing raw.extents raw.seals raw.keeper
      raw.sameLookup raw.flat raw.marked bootstrap assemble constructs raw.allocations
  have exactPhase := reboot.exactEmptyPhase valid opening installed.nativeReturned
  obtain ⟨handle, start, table, _, lock, files, phase, _, contents, actualGet, actualSet, actualCompare,
    reached, state, history, submissions, reads, pins⟩ :=
    installed.fromOpen get set phaseEffects ptrEq
  have empty : (nextView.descriptors reboot.rebooted).slots = [] := by
    rw [raw.raw.entryCensus]
    exact selected.emptyCensus
  refine ⟨reboot.readsSelectedReboot valid opening same, reboot.choosesAligned valid opening, empty,
    raw.raw.entryFiles, cacheOpen, makeCache, handle, start, cacheAction, cacheSource, ?_, ?_, ?_, lock,
    files.symm ▸ installed.cacheReferences, contents, actualGet, actualSet, actualCompare, ?_, ?_, ?_,
    history, submissions, reads, pins⟩
  · rw [table, reached]
    exact returned
  · rw [phase, reached, installed.phaseStored, exactPhase]
  · rw [state]
    exact Phase.ready.inj (installed.ready.refines.1.phase.symm.trans exactPhase)
  · rw [reached, state]
    exact installed.filesPreserved
  · rw [reached, state]
    exact installed.censusPreserved
  · rw [reached, state]
    exact installed.cachePreserved

end RawBootstrapMarkerDirectoryStop.EffectiveReboot
end Alvoki.Storage.DiskSession
