import Alvoki.Storage.Disk.BatchGroupedWriteError
import Alvoki.Storage.Disk.NativePendingMarkerSync

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentCommit WalSegmentRepair WAL.Boundary

private abbrev GroupFiles := DescriptorInventory × WriteFiles
private abbrev GroupState := CensusDirectoryCache × GroupFiles

private def handleDescription (handle : CheckpointOpenHandle) : Nat := handle.2.1.description
private def handleInode (handle : CheckpointOpenHandle) : Nat := handle.1.inode (handleDescription handle)

/-- Report the failing member of the two-file barrier. The staged
member supplies the diagnostic only after a successful keeper sync. -/
inductive NativeGroupedSyncFailure (keeper marker : EStateM.Result IO.Error WriteFiles Unit) where
  | keeper (cause : IO.Error) (after : WriteFiles) (returned : keeper = .error cause after)
  | marker (cause : IO.Error) (afterKeeper after : WriteFiles)
      (synced : keeper = .ok () afterKeeper) (returned : marker = .error cause after)

/-- Both sync callbacks run on the handles reached by the append and stage.
The staged handle is finalized separately on either returned status. -/
structure NativeGroupedWriteSyncError {before : NativeReadyState} (prepared : NativeReadyWritePreparation before) where
  request : WriteRequest
  rows : request.rows = prepared.rows
  staging : NativeReadyWriteStaging prepared
  openRead : FilePath → EStateM IO.Error WriteFiles CheckpointOpenHandle
  fsync : CheckpointOpenHandle → EStateM IO.Error WriteFiles Unit
  effect : WalSyncEffect
  effective : Bool
  keeperReturned : FsyncResult prepared.staged (prepared.staged.syncWal effect) effective
    (fsync staging.keeperHandle prepared.staged)
  complete : ∀ after, fsync staging.keeperHandle prepared.staged = .ok () after → effect = .complete
  markerEffective : Bool
  markerReturned : FsyncResult
    (reachedState (fsync staging.keeperHandle prepared.staged))
    (((reachedState (fsync staging.keeperHandle prepared.staged)).stepMarker prepared.marker .syncStaged).getD
      (reachedState (fsync staging.keeperHandle prepared.staged)))
    markerEffective (fsync staging.stageHandle (reachedState (fsync staging.keeperHandle prepared.staged)))
  finalize : CheckpointOpenHandle → EStateM IO.Error GroupFiles Unit
  finalized :
    let files := reachedState (fsync staging.stageHandle (reachedState (fsync staging.keeperHandle prepared.staged)))
    reachedState (finalize staging.stageHandle (staging.afterMarkerOpen, files)) =
      (staging.afterMarkerOpen.afterDrops [staging.markerSlot.closeEvent], files)
  failure : NativeGroupedSyncFailure (fsync staging.keeperHandle prepared.staged)
    (fsync staging.stageHandle (reachedState (fsync staging.keeperHandle prepared.staged)))

namespace NativeGroupedWriteSyncError

variable {before : NativeReadyState} {prepared : NativeReadyWritePreparation before}

def keeperFiles (seen : NativeGroupedWriteSyncError prepared) : WriteFiles :=
  reachedState (seen.fsync seen.staging.keeperHandle prepared.staged)

def markerFiles (seen : NativeGroupedWriteSyncError prepared) : WriteFiles :=
  reachedState (seen.fsync seen.staging.stageHandle seen.keeperFiles)

def census (seen : NativeGroupedWriteSyncError prepared) : DescriptorInventory :=
  seen.staging.afterMarkerOpen.afterDrops [seen.staging.markerSlot.closeEvent]

def diagnostic (seen : NativeGroupedWriteSyncError prepared) : IO.Error :=
  match seen.failure with
  | .keeper cause _ _ => IO.userError s!"sync failed for '{prepared.keeperPath}': {cause}"
  | .marker cause _ _ _ _ => IO.userError s!"sync failed for '{prepared.stagedPath}': {cause}"

private def liftFiles {α : Type} (operation : EStateM IO.Error WriteFiles α) : EStateM IO.Error GroupFiles α :=
  fun (inventory, files) => match operation files with
  | .ok value after => .ok value (inventory, after)
  | .error cause after => .error cause (inventory, after)

private def finalizeSync (seen : NativeGroupedWriteSyncError prepared) (handle : CheckpointOpenHandle) :
    EStateM IO.Error GroupFiles Unit := fun before =>
  match liftFiles (seen.fsync handle) before with
  | .ok value after => .ok value (reachedState (seen.finalize handle after))
  | .error cause after => .error cause (reachedState (seen.finalize handle after))

def syncPath (seen : NativeGroupedWriteSyncError prepared) (path : FilePath) : EStateM IO.Error GroupState Unit :=
  let effect := if path = prepared.stagedPath then seen.finalizeSync else fun handle => liftFiles (seen.fsync handle)
  SyncHandleRouting.sync before.session.directory.path (fun name => liftFiles (seen.openRead name)) effect path

private theorem pendingHit (seen : NativeGroupedWriteSyncError prepared) :
    seen.staging.groupCache.pending.find? (fun entry => entry.1 == prepared.stagedPath) =
      some (prepared.stagedPath, seen.staging.stageHandle) := by
  simp [Cache.remember, pushPending]

private theorem consumed (seen : NativeGroupedWriteSyncError prepared) :
    seen.staging.groupCache.consume prepared.stagedPath = seen.staging.appendCache := by
  simp [Cache.remember, Cache.consume, pushPending, NativeReadyWriteStaging.appendCache, seen.staging.pendingEmpty]

private theorem keeperPathNeStage : prepared.keeperPath ≠ prepared.stagedPath := by
  intro same
  obtain ⟨_, impossible⟩ := DiskDirectory.walSegment_exclusive same.symm
  cases impossible

private theorem keeperCall (seen : NativeGroupedWriteSyncError prepared) :
    seen.syncPath prepared.keeperPath (seen.staging.groupCache, seen.staging.afterMarkerOpen, prepared.staged) =
      match seen.fsync seen.staging.keeperHandle prepared.staged with
      | .ok () _ => .ok () (seen.staging.groupCache, seen.staging.afterMarkerOpen, seen.keeperFiles)
      | .error cause _ => .error cause (seen.staging.groupCache, seen.staging.afterMarkerOpen, seen.keeperFiles) := by
  cases report : seen.fsync seen.staging.keeperHandle prepared.staged with
  | ok value files =>
    cases value
    simp only [syncPath, ite_eq_right keeperPathNeStage, SyncHandleRouting.sync,
      seen.staging.selectsKeeperSync, liftFiles, report, withCache, keeperFiles, reachedState]
  | error cause files =>
    simp only [syncPath, ite_eq_right keeperPathNeStage, SyncHandleRouting.sync,
      seen.staging.selectsKeeperSync, liftFiles, report, withCache, keeperFiles, reachedState]

private theorem markerCall (seen : NativeGroupedWriteSyncError prepared) :
    seen.syncPath prepared.stagedPath (seen.staging.groupCache, seen.staging.afterMarkerOpen, seen.keeperFiles) =
      match seen.fsync seen.staging.stageHandle seen.keeperFiles with
      | .ok () _ => .ok () (seen.staging.appendCache, seen.census, seen.markerFiles)
      | .error cause _ => .error cause (seen.staging.appendCache, seen.census, seen.markerFiles) := by
  have stage : prepared.stagedPath ≠ before.session.directory.path :=
    file_ne_directory before.session.directory .stagedWalBoundary
  simp only [syncPath, SyncHandleRouting.sync, Cache.resolve, beq_eq_false_iff_ne.mpr stage,
    Bool.false_eq_true, ↓reduceIte, seen.pendingHit, seen.consumed, finalizeSync, liftFiles, withCache]
  cases marker : seen.fsync seen.staging.stageHandle seen.keeperFiles <;> rename_i outcome files
  all_goals
    have same : seen.markerFiles = files := by simp only [markerFiles, marker, reachedState]
    have finalized : reachedState (seen.finalize seen.staging.stageHandle (seen.staging.afterMarkerOpen, files)) =
        (seen.census, files) := same ▸ seen.finalized
    simp only [finalized, same] <;> first | rfl | cases outcome; rfl

/-- Both callbacks run. The group's diagnostic comes from the first
returned error and the group state comes from the finalizer. -/
theorem groupReturns (seen : NativeGroupedWriteSyncError prepared) :
    SyncPathGroup.run seen.syncPath #[prepared.keeperPath, prepared.stagedPath]
      (seen.staging.groupCache, seen.staging.afterMarkerOpen, prepared.staged) =
      .error seen.diagnostic (seen.staging.appendCache, seen.census, seen.markerFiles) := by
  rw [SyncPathGroup.run_pair, seen.keeperCall]
  cases failure : seen.failure with
  | keeper cause after returned =>
    simp only [returned]
    rw [seen.markerCall]
    cases seen.fsync seen.staging.stageHandle seen.keeperFiles with
    | ok value after => cases value; simp only [diagnostic, failure]; rfl
    | error => simp only [diagnostic, failure]; rfl
  | marker cause firstAfter after synced returned =>
    change seen.fsync seen.staging.stageHandle seen.keeperFiles = .error cause after at returned
    simp only [synced]
    rw [seen.markerCall, returned]
    simp only [diagnostic, failure]
    rfl

private def fsyncObservation {inventory : DescriptorInventory} {handle : CheckpointOpenHandle}
    (live : handle.2.1 ∈ inventory.slots) {before : WriteFiles} {persist : Nat → WriteFiles → WriteFiles}
    {effective : Bool} {result : EStateM.Result IO.Error WriteFiles Unit}
    (effect : FsyncResult before (persist (handleInode handle) before) effective result) :
    FsyncObservation handleDescription handleInode handle before persist result := by
  have reference := inventory.mem_references.mpr ⟨handle.2.1, live, rfl, rfl⟩
  let references := inventory.held (handleDescription handle) (List.ne_nil_of_mem reference)
  refine ⟨references, handle.2.1.reference, [], ?_, handleDescription handle, handleInode handle, rfl, rfl, effective, effect⟩
  exact (references.mem_remaining [] _).mpr ⟨reference, by simp⟩

private def bindings (seen : NativeGroupedWriteSyncError prepared) (_ : WriteFiles) (path : FilePath) : Option Nat :=
  let view := seen.staging.stageView
  let root := seen.staging.root
  if path = before.session.directory.path then some (view.modelObject root)
  else if path = prepared.keeperPath then (view.child root prepared.keeperName).map view.modelObject
  else if path = prepared.stagedPath then (view.child root "WAL.commit.next").map view.modelObject
  else none

private theorem boundKeeper (seen : NativeGroupedWriteSyncError prepared) :
    seen.bindings prepared.staged prepared.keeperPath = some (handleInode seen.staging.keeperHandle) := by
  obtain ⟨_, _, _, captured, named⟩ := seen.staging.selectsKeeper.custody
  simp only [bindings, ite_eq_right (file_ne_directory before.session.directory (.walSegment before.writer.installed.activeFirst)),
    ite_true, seen.staging.stageBindings.1, Option.map_some, seen.staging.stageObjects, handleInode, handleDescription]
  exact congrArg some (named.trans captured.symm)

private theorem boundStage (seen : NativeGroupedWriteSyncError prepared) :
    seen.bindings prepared.staged prepared.stagedPath = some (handleInode seen.staging.stageHandle) := by
  have inodes := seen.staging.selectsKeeper.custody.2.1
  simp only [bindings, ite_eq_right (file_ne_directory before.session.directory .stagedWalBoundary),
    ite_eq_right (Ne.symm keeperPathNeStage), ite_true, seen.staging.stageBindings.2.2, Option.map_some]
  exact congrArg some (seen.staging.stageIdentity.trans (congrFun inodes _).symm)

private theorem owned (seen : NativeGroupedWriteSyncError prepared) :
    seen.staging.groupCache.Agrees before.session.directory.path handleInode (seen.bindings prepared.staged) := by
  constructor
  · intro descriptor cached
    have same : descriptor = (seen.staging.directoryCapture, before.directorySlot, 0) := by
      exact Option.some.inj (cached.symm.trans seen.staging.directoryCached)
    subst descriptor
    simp only [bindings, ite_true, seen.staging.stageObjects, handleInode, handleDescription]
    exact congrArg some (seen.staging.directoryIdentity.trans seen.staging.sameDirectoryInode.symm)
  · intro path descriptor found
    simp only [Cache.remember, pushPending, seen.staging.pendingEmpty,
      List.find?_cons, List.find?_nil] at found
    split at found
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
      exact seen.boundStage
    · contradiction
  · intro path descriptor found
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
    exact seen.boundKeeper

private def logicalSync (seen : NativeGroupedWriteSyncError prepared)
    (paths : Array FilePath) : EStateM IO.Error WriteFiles Unit := fun files =>
  withoutWriteGroupCache (SyncPathGroup.run (SyncHandleRouting.sync before.session.directory.path seen.openRead seen.fsync)
    paths (seen.staging.groupCache, files))

private def logicalGroup (seen : NativeGroupedWriteSyncError prepared) :
    ReachedWriteGroup (handle := CheckpointOpenHandle) before.session.directory before.writer.installed.activeFirst
      prepared.marker prepared.staged seen.logicalSync where
  cache := seen.staging.groupCache
  openRead := seen.openRead
  fsync := seen.fsync
  description := handleDescription
  inode := handleInode
  bindings := seen.bindings
  keeperHandle := seen.staging.keeperHandle
  stagedHandle := seen.staging.stageHandle
  keeperNotDirectory := file_ne_directory before.session.directory (.walSegment before.writer.installed.activeFirst)
  stagedNotDirectory := file_ne_directory before.session.directory .stagedWalBoundary
  keeperMiss := by simp [Cache.remember, pushPending, seen.staging.pendingEmpty, Ne.symm keeperPathNeStage]
  active := rfl
  pending := seen.pendingHit
  owned := seen.owned
  distinct := by
    obtain ⟨_, inodes, _, captured, _⟩ := seen.staging.selectsKeeper.custody
    intro same
    exact seen.staging.differentFiles
      ((congrFun inodes _).symm.trans (same.symm.trans (captured.trans (congrFun inodes _))))
  wal := seen.effect
  stableStage := rfl
  keeper := fsyncObservation (inventory := seen.staging.afterMarkerOpen)
    (List.mem_cons_of_mem _ seen.staging.selectsKeeper.custody.2.2.1) seen.keeperReturned
  complete := seen.complete
  staged := fsyncObservation (inventory := seen.staging.afterMarkerOpen) List.mem_cons_self seen.markerReturned
  execution := rfl

/-- Reuse the existing grouped return certificate on the file
projection of these same reached raw effects. -/
noncomputable def logical (seen : NativeGroupedWriteSyncError prepared) (valid : before.Valid)
    (rename : FilePath → FilePath → EStateM IO.Error (CensusDirectoryCache × WriteFiles) Unit) :
    BatchGroupedWriteError before.session.directory before.writer CheckpointOpenHandle where
  rows := prepared.rows
  batch := prepared.batch
  table := prepared.table
  nonempty := prepared.nonempty
  prepared := prepared.prepared
  fits := prepared.fits
  guard := seen.staging.activeGuard
  cache := before.cache
  openAppend := seen.staging.openAppend
  write := seen.staging.appendWrite
  flush := seen.staging.appendFlush
  stage := writeFreshStagedWith seen.staging.tryStage seen.staging.detachStale seen.staging.createStage
    seen.staging.stageWrite seen.staging.stageFlush
  rename := rename
  keeper := seen.staging.keeperHandle
  marker := seen.staging.stageHandle
  opened := prepared.initial
  written := seen.staging.buffered
  appended := prepared.appended
  staged := prepared.staged
  tails := prepared.tails
  selected := by
    rw [← valid.retained.directoryFiles]
    exact seen.staging.selectsKeeper.selects
  wrote := seen.staging.wrote
  flushed := seen.staging.flushed
  appendedFiles := by rw [← valid.retained.directoryFiles]; rfl
  markerWritten := seen.staging.staged
  stagedFiles := rfl
  syncFiles := seen.logicalSync
  group := seen.logicalGroup
  groupCache := rfl
  memberFailed := by
    cases seen.failure with
    | keeper cause after returned => exact .inl ⟨cause, after, returned⟩
    | marker cause _ after _ returned => exact .inr ⟨cause, after, returned⟩

theorem projectedGroup (seen : NativeGroupedWriteSyncError prepared) (valid : before.Valid) (rename) :
    (seen.logical valid rename).calls.sync #[prepared.keeperPath, prepared.stagedPath]
      (seen.staging.groupCache, prepared.staged) =
    .error seen.diagnostic (seen.staging.appendCache, seen.markerFiles) := by
  let group := seen.logicalGroup
  change SyncPathGroup.run (SyncHandleRouting.sync before.session.directory.path seen.openRead seen.fsync)
    #[prepared.keeperPath, prepared.stagedPath] (seen.staging.groupCache, prepared.staged) = _
  have executes := groupedActivePending group.keeperNotDirectory group.stagedNotDirectory group.keeperMiss
    group.active group.pending seen.openRead seen.fsync prepared.staged
  change SyncPathGroup.run (SyncHandleRouting.sync before.session.directory.path seen.openRead seen.fsync)
    #[prepared.keeperPath, prepared.stagedPath] (seen.staging.groupCache, prepared.staged) = _ at executes
  have keeper : group.keeperHandle = seen.staging.keeperHandle := rfl
  have staged : group.stagedHandle = seen.staging.stageHandle := rfl
  have cache : group.cache = seen.staging.groupCache := rfl
  rw [executes, keeper, staged, cache, seen.consumed]
  cases failure : seen.failure with
  | keeper cause after returned =>
    have reached : seen.keeperFiles = after := by simp only [keeperFiles, returned, reachedState]
    rw [returned, ← reached]
    cases marker : seen.fsync seen.staging.stageHandle seen.keeperFiles <;>
      simp only [markerFiles, marker, reachedState, diagnostic, failure]
  | marker cause firstAfter after synced returned =>
    have reached : seen.keeperFiles = firstAfter := by simp only [keeperFiles, synced, reachedState]
    change seen.fsync seen.staging.stageHandle seen.keeperFiles = .error cause after at returned
    simp only [synced]
    rw [← reached, returned]
    simp only [markerFiles, returned, reachedState, diagnostic, failure]

private def liftReturned (inventory : DescriptorInventory)
    (op : EStateM IO.Error (CensusDirectoryCache × WriteFiles) Unit) : EStateM IO.Error GroupState Unit :=
  fun (cache, before, files) => match op (cache, files) with
  | .ok value (next, reached) => .ok value (next, inventory, reached)
  | .error cause (next, reached) => .error cause (next, before, reached)

noncomputable def run (seen : NativeGroupedWriteSyncError prepared)
    (rename : FilePath → FilePath → EStateM IO.Error GroupState Unit) :=
  seen.request.runReported before.session.directory seen.staging.activeGuard.lookup
    (fun path bytes => liftReturned seen.staging.afterSelect (seen.staging.append path bytes))
    (fun path bytes => liftReturned seen.staging.afterMarkerOpen (seen.staging.stage path bytes))
    (SyncPathGroup.run seen.syncPath) rename
    (before.session.phase, ⟨(before.cache, before.census, prepared.initial), before.files.owners⟩)

/-- Neither write interface acknowledges or reaches rename after a
returned error in the group. The returned cache has already consumed the
staged descriptor and its reach includes the observed finalization. -/
theorem returnsUnknown (seen : NativeGroupedWriteSyncError prepared) (valid : before.Valid) (rename) :
    seen.run rename = .error (.commitUnknown seen.diagnostic)
      (.poisoned, ⟨(seen.staging.appendCache, seen.census, seen.markerFiles), before.files.owners⟩) := by
  have failed : commitBytesAt before.session.directory before.writer.installed.activeFirst (WAL.encodeBatch prepared.batch)
      prepared.count (fun path bytes => liftReturned seen.staging.afterSelect (seen.staging.append path bytes))
      (fun path bytes => liftReturned seen.staging.afterMarkerOpen (seen.staging.stage path bytes))
      (SyncPathGroup.run seen.syncPath) rename (before.cache, before.census, prepared.initial) =
      .error seen.diagnostic (seen.staging.appendCache, seen.census, seen.markerFiles) := by
    rw [commitBytesAt_fileEffects]
    simp only [WAL.Boundary.commit, Bind.bind, EStateM.bind, liftReturned, seen.staging.appendReturns,
      show WAL.Boundary.encode prepared.count.toUInt64 = prepared.marker from rfl, seen.staging.stageReturns, seen.groupReturns]
  unfold run
  rw [valid.phase, seen.request.runReported_eq_batch valid.retained, seen.rows]
  exact runBatchWrite_commitUnknown seen.staging.activeGuard prepared.nonempty prepared.prepared prepared.fits failed

private theorem fsyncPreserves {state value : Type} {before persisted : state} {effective : Bool}
    {result : EStateM.Result IO.Error state Unit} (effect : FsyncResult before persisted effective result)
    (project : state → value) {target : value}
    (original : project before = target) (synced : project persisted = target) :
    project (reachedState result) = target := by
  cases effect <;> assumption

theorem markerFrame (seen : NativeGroupedWriteSyncError prepared) :
    seen.markerFiles.marker.active = prepared.initial.marker.active ∧
    seen.markerFiles.marker.crashImages = prepared.initial.marker.crashImages := by
  have kept : seen.keeperFiles.marker = prepared.staged.marker := by
    apply fsyncPreserves seen.keeperReturned (fun files => files.marker) rfl
    cases seen.effect <;> rfl
  let project := fun (files : WriteFiles) => (files.marker.active, files.marker.crashImages)
  have before : project seen.keeperFiles = project prepared.initial := by
    change (seen.keeperFiles.marker.active, seen.keeperFiles.marker.crashImages) = _
    rw [kept]
    rfl
  have after : project ((seen.keeperFiles.stepMarker prepared.marker .syncStaged).getD seen.keeperFiles) =
      project prepared.initial := by
    simp only [project, WriteFiles.stepMarker, Publication.Image.step, kept, NativeReadyWritePreparation.staged,
      NativeReadyWritePreparation.appended]
    rfl
  exact Prod.mk.inj (fsyncPreserves seen.markerReturned project before after)

theorem markerClosed (seen : NativeGroupedWriteSyncError prepared) :
    seen.staging.markerSlot ∉ seen.census.slots := by
  intro stillLive
  have survives := (List.mem_filter.mp stillLive).2
  simp [DescriptorSlot.closeEvent, LockReferenceDrop.removes] at survives

theorem keepsSlot (seen : NativeGroupedWriteSyncError prepared) {slot : DescriptorSlot}
    (live : slot ∈ seen.staging.afterSelect.slots) : slot ∈ seen.census.slots := by
  have distinct := seen.staging.markerFree slot live
  apply List.mem_filter.mpr
  refine ⟨List.mem_cons_of_mem _ live, ?_⟩
  by_cases process : slot.reference.process = seen.staging.markerSlot.reference.process
  · have fd : slot.reference.fd ≠ seen.staging.markerSlot.reference.fd := fun same => distinct (Prod.ext process same)
    simp [DescriptorSlot.closeEvent, LockReferenceDrop.removes, process, fd]
  · simp [DescriptorSlot.closeEvent, LockReferenceDrop.removes, process]

end NativeGroupedWriteSyncError

/-- The terminal native write failure retains the original committed
history and the exact reached poisoned files, cache and descriptors. -/
structure NativeReturnedGroupedWriteSyncError (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} (seen : NativeGroupedWriteSyncError prepared) : Prop where
  returned : ∀ rename, seen.run rename = .error (.commitUnknown seen.diagnostic)
    (.poisoned, ⟨(seen.staging.appendCache, seen.census, seen.markerFiles), current.state.files.owners⟩)
  group : SyncPathGroup.run seen.syncPath #[prepared.keeperPath, prepared.stagedPath]
    (seen.staging.groupCache, seen.staging.afterMarkerOpen, prepared.staged) =
    .error seen.diagnostic (seen.staging.appendCache, seen.census, seen.markerFiles)
  reported : ∀ rename, WriteRequest.ReturnedReports seen.request current.state.session.directory current.state.writer
    CheckpointOpenHandle (seen.logical current.readPrefix.refines.1 rename).calls
  stagedClosed : seen.staging.markerSlot ∉ seen.census.slots
  directoryLive : current.state.directorySlot ∈ seen.census.slots
  ownerLive : current.state.owner ∈ seen.census.slots
  keeperLive : seen.staging.keeperSlot ∈ seen.census.slots
  inodeMap : seen.census.inode = current.state.census.inode
  keeperObject : (seen.staging.stageView.child seen.staging.root prepared.keeperName).map seen.staging.stageView.modelObject =
    some (seen.census.inode seen.staging.keeperSlot.description)
  stagedObject : (seen.staging.stageView.child seen.staging.root "WAL.commit.next").map seen.staging.stageView.modelObject =
    some (seen.census.inode seen.staging.markerSlot.description)
  lockObject : (seen.staging.stageView.child seen.staging.root "LOCK").map seen.staging.stageView.modelObject =
    some (seen.census.inode current.state.owner.description)
  held : current.state.files.owners.Owns current.state.session.directory current.state.session.descriptor
  pendingEmpty : seen.staging.appendCache.pending = []
  marker : seen.markerFiles.marker.active = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64)
  survivors : seen.markerFiles.marker.crashImages = [seen.markerFiles.marker.active]
  replay : PendingClientReplay (log ++ [.uncertainBatch prepared.batch]) current.reads history
  bounded : ∀ read ∈ current.reads, read.BoundedBy history.length

theorem NativeReadPosition.returnsGroupedWriteSyncError (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} (seen : NativeGroupedWriteSyncError prepared) :
    NativeReturnedGroupedWriteSyncError current seen := by
  obtain ⟨valid, sameHistory, previous⟩ := current.readPrefix.refines
  have ordered : WAL.OrdinalsFrom 1 _ := sameHistory ▸ valid.retained.resumed.ordered
  obtain ⟨replay, bounded⟩ := previous.appendUncertain (batch := prepared.batch) current.readPrefix.readsBounded (.inl rfl) ordered
  obtain ⟨old, survivors⟩ := seen.markerFrame
  obtain ⟨retained, inodes, keeper, _, keeperIdentity⟩ := seen.staging.selectsKeeper.custody
  obtain ⟨keeperNamed, lockNamed, stagedNamed⟩ := seen.staging.stageBindings
  have inodeMap : seen.census.inode = current.state.census.inode := inodes
  have original : prepared.initial.marker.active =
      some (WAL.Boundary.encode (WAL.encode current.state.writer.history).size.toUInt64) := rfl
  have marker := congrArg (fun writes => some (WAL.Boundary.encode (WAL.encode writes).size.toUInt64)) sameHistory
  exact ⟨seen.returnsUnknown valid, seen.groupReturns,
    fun rename => (seen.logical valid rename).returnedReports seen.request seen.rows,
    seen.markerClosed, seen.keepsSlot (retained _ valid.directoryLive),
    seen.keepsSlot (retained _ valid.ownerLive), seen.keepsSlot keeper, inodeMap,
    by rw [keeperNamed, Option.map_some, seen.staging.stageObjects]; exact congrArg some keeperIdentity,
    by rw [stagedNamed, Option.map_some, seen.staging.stageIdentity, inodeMap],
    by rw [lockNamed, Option.map_some, seen.staging.stageObjects, inodeMap]; exact congrArg some seen.staging.lockIdentity,
    valid.retained.held, seen.staging.pendingEmpty,
    old.trans (original.trans marker),
    by rw [old, survivors]; rfl, replay, bounded⟩

end Alvoki.Storage.DiskSession
