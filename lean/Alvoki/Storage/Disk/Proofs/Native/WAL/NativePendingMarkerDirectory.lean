import Alvoki.Storage.Disk.Proofs.Native.WAL.NativePendingMarkerRename

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentCommit WalSegmentRepair WAL.Boundary

private abbrev BarrierFiles := DescriptorInventory × WriteFiles
private abbrev BarrierState := CensusDirectoryCache × BarrierFiles
private abbrev BarrierM := ExceptT IO.Error (EStateM FilePath BarrierState)

/-- At the final marker directory barrier the rename has returned and
its synced source inode is live at the marker name. The raw fsync has
no return. Its effect determines which marker bindings can survive. -/
structure NativeWriteMarkerDirectoryStop {before : NativeReadyState} (prepared : NativeReadyWritePreparation before) where
  request : WriteRequest
  rows : request.rows = prepared.rows
  renamed : NativeReadyWriteRenamed prepared
  sourceGone : renamed.publishedView.child renamed.root "WAL.commit.next" = none
  fsync : CheckpointOpenHandle → EStateM FilePath BarrierFiles (Except IO.Error Unit)
  applied : Bool
  stopped : fsync (renamed.directoryCapture, before.directorySlot, 0) (renamed.census, prepared.renamed) =
    .error before.session.directory.path (renamed.census,
      (MarkerInterruption.directorySync applied).interrupt prepared.marker prepared.renamed)

namespace NativeWriteMarkerDirectoryStop

variable {before : NativeReadyState} {prepared : NativeReadyWritePreparation before}

def cut (stop : NativeWriteMarkerDirectoryStop prepared) : MarkerInterruption := .directorySync stop.applied

def reached (stop : NativeWriteMarkerDirectoryStop prepared) : BarrierFiles :=
  (stop.renamed.census, stop.cut.interrupt prepared.marker prepared.renamed)

def session (_stop : NativeWriteMarkerDirectoryStop prepared) : SegmentedSession :=
  { before.session with phase := .poisoned }

private def withInventory {α : Type} (operation : EStateM IO.Error WriteFiles α) : EStateM IO.Error BarrierFiles α :=
  fun (inventory, files) => match operation files with
  | .ok value reached => .ok value (inventory, reached)
  | .error cause reached => .error cause (inventory, reached)

def syncDirectory (stop : NativeWriteMarkerDirectoryStop prepared) (path : FilePath) : BarrierM Unit :=
  fun (cache, files) =>
    match cache.resolve before.session.directory.path path (fun child => withInventory (stop.renamed.openRead child)) files with
    | .error cause reached => .ok (.error cause) reached
    | .ok handle (cache, files) =>
      match stop.fsync handle files with
      | .ok result reached => .ok result (cache, reached)
      | .error path reached => .error path (cache, reached)

theorem stopsDirectory (stop : NativeWriteMarkerDirectoryStop prepared) :
    (SyncPathGroup.run stop.syncDirectory #[before.session.directory.path]).run
      (stop.renamed.appendCache, stop.renamed.census, prepared.renamed) =
    .error before.session.directory.path (stop.renamed.appendCache, stop.reached) := by
  have cached : before.cache.directory = some (stop.renamed.directoryCapture, before.directorySlot, 0) :=
    stop.renamed.directoryCached
  have issued : stop.syncDirectory before.session.directory.path (stop.renamed.appendCache, stop.renamed.census, prepared.renamed) =
      .error before.session.directory.path (stop.renamed.appendCache, stop.reached) := by
    simp only [syncDirectory, Cache.resolve, beq_self_eq_true, ite_true, cached, stop.stopped, cut, reached]
  simp [SyncPathGroup.run, ← Array.forIn_toList, List.forIn_cons, MonadExcept.tryCatch,
    MonadExceptOf.tryCatch, tryCatchThe, ExceptT.tryCatch, Bind.bind, ExceptT.bind, ExceptT.run,
    ExceptT.mk, EStateM.bind, issued]

private def sync (stop : NativeWriteMarkerDirectoryStop prepared) (paths : Array FilePath) : BarrierM Unit :=
  if paths = #[before.session.directory.path] then SyncPathGroup.run stop.syncDirectory paths
  else observeReturnedWriteCall stop.renamed.census (stop.renamed.sync paths)

noncomputable def publication (stop : NativeWriteMarkerDirectoryStop prepared)
    (installed : Installed) (events : List WAL.Write) (bytes : Nat) : BarrierM Unit :=
  let seen := stop.renamed
  commitBytesAt before.session.directory installed.activeFirst (WAL.encodeBatch events) bytes
    (fun path payload => observeReturnedWriteCall seen.afterSelect (seen.append path payload))
    (fun path payload => observeReturnedWriteCall seen.afterMarkerOpen (seen.stage path payload))
    stop.sync (fun source target => observeReturnedWriteCall seen.census (seen.replace source target))

theorem stopsPublication (stop : NativeWriteMarkerDirectoryStop prepared) :
    (stop.publication before.writer.installed prepared.batch prepared.count).run
      (before.cache, before.census, prepared.initial) =
    .error before.session.directory.path (stop.renamed.appendCache, stop.reached) := by
  have groups : #[prepared.keeperPath, prepared.stagedPath] ≠ #[before.session.directory.path] := by
    intro same
    have impossible : (2 : Nat) = 1 := congrArg Array.size same
    omega
  have barrier := stop.stopsDirectory
  change (SyncPathGroup.run stop.syncDirectory #[before.session.directory.path])
    (stop.renamed.appendCache, stop.renamed.census, prepared.renamed) = _ at barrier
  rw [publication, commitBytesAt_fileEffects]
  simp only [WAL.Boundary.commit, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run, EStateM.bind,
    observeReturnedWriteCall, stop.renamed.appendReturns, show WAL.Boundary.encode prepared.count.toUInt64 = prepared.marker from rfl,
    stop.renamed.stageReturns, sync, groups, ite_false, stop.renamed.groupReturns, ite_true, stop.renamed.renameReturns, barrier]

noncomputable def run (stop : NativeWriteMarkerDirectoryStop prepared) :=
  stop.request.runWithInterruption before.session.directory stop.renamed.activeGuard.lookup stop.publication
    (before.session.phase, ⟨(before.cache, before.census, prepared.initial), before.files.owners⟩)

theorem stopsWrite (stop : NativeWriteMarkerDirectoryStop prepared) (valid : before.Valid) :
    stop.run = .error before.session.directory.path
      (.poisoned, ⟨(stop.renamed.appendCache, stop.reached), before.files.owners⟩) := by
  unfold run
  rw [valid.phase]
  exact stop.request.stopsPublication stop.rows prepared.nonempty prepared.prepared prepared.fits
    stop.renamed.activeGuard stop.publication stop.stopsPublication

def files (stop : NativeWriteMarkerDirectoryStop prepared) : FileImage :=
  resumedAppendFiles before.files.image before.writer.history before.writer.wal.active.first stop.reached.2

theorem atCut (stop : NativeWriteMarkerDirectoryStop prepared) :
    stop.reached.2 = if stop.applied then prepared.settled else prepared.renamed := by
  unfold reached cut
  cases stop.applied <;> rfl

def newPair (_stop : NativeWriteMarkerDirectoryStop prepared) : DirectoryPublication.Bindings :=
  ⟨before.files.image.directory.active.manifest, some prepared.marker⟩

/-- The rename has already moved the live marker. A completed directory
sync removes the old crash choice even when its callback never returns. -/
theorem choices (stop : NativeWriteMarkerDirectoryStop prepared) (valid : before.Valid) :
    stop.files.directory.active = stop.newPair ∧
    stop.files.directory.crashImages = (if stop.applied then [stop.newPair] else [stop.newPair, before.writer.target.pair]) ∧
    stop.files.directory.staged .walBoundary = none ∧
    stop.files.keeper.active = some (before.writer.wal.active.bytes ++ WAL.encode prepared.batch) ∧
    stop.files.keeper.crashImages = [stop.files.keeper.active] := by
  have old : before.files.image.directory.active = before.writer.target.pair := valid.retained.resumed.ready.selected
  have marker := (valid.retained.selectPriorKeeper ByteArray.empty).1
  have priorPair :
      (⟨before.files.image.directory.active.manifest, some (WAL.Boundary.encode (WAL.encode before.writer.history).size.toUInt64)⟩ :
        DirectoryPublication.Bindings) = before.writer.target.pair := by
    rw [old, ← marker]
  have bytes := congrArg (fun bytes => some (bytes ++ WAL.encode prepared.batch)) valid.retained.layout.activeBytes.symm
  unfold files
  rw [stop.atCut]
  cases ran : stop.applied with
  | false =>
    change _ = stop.newPair ∧ _ = [stop.newPair, before.writer.target.pair] ∧ _
    exact ⟨rfl, congrArg (fun pair => [stop.newPair, pair]) priorPair, rfl, bytes, rfl⟩
  | true => exact ⟨rfl, rfl, rfl, bytes, rfl⟩

theorem batchCut (stop : NativeWriteMarkerDirectoryStop prepared) (valid : before.Valid) :
    BatchCutProjection stop.files (prepared.modeledMarkerCut stop.cut) := by
  apply prepared.projectMarkerCut valid stop.cut
  simp only [MarkerInterruption.reachedBatch, (prepared.extended valid).1]
  rfl

/-- The final fsync uses the original directory object. The already
renamed marker is the synced staged inode, and its descriptor is gone. -/
structure Custody (stop : NativeWriteMarkerDirectoryStop prepared) : Prop where
  census : stop.reached.1 = stop.renamed.afterSelect
  stageClosed : stop.reached.1.references stop.renamed.markerSlot.description = []
  directoryLive : before.directorySlot ∈ stop.reached.1.slots
  ownerLive : before.owner ∈ stop.reached.1.slots
  keeperLive : stop.renamed.keeperSlot ∈ stop.reached.1.slots
  directoryObject : stop.renamed.publishedView.modelObject stop.renamed.root = stop.reached.1.inode before.directorySlot.description
  directoryCapture : stop.renamed.directoryCapture.inode before.directorySlot.description = stop.reached.1.inode before.directorySlot.description
  lockObject : (stop.renamed.publishedView.child stop.renamed.root "LOCK").map stop.renamed.publishedView.modelObject =
    some (stop.reached.1.inode before.owner.description)
  keeperObject : (stop.renamed.publishedView.child stop.renamed.root prepared.keeperName).map stop.renamed.publishedView.modelObject =
    some (stop.reached.1.inode stop.renamed.keeperSlot.description)
  keeperCapture : stop.renamed.keeperHandle.1.inode stop.renamed.keeperSlot.description =
    stop.reached.1.inode stop.renamed.keeperSlot.description
  markerObject : (stop.renamed.publishedView.child stop.renamed.root "WAL.commit").map stop.renamed.publishedView.modelObject =
    some (stop.reached.1.inode stop.renamed.markerSlot.description)
  stagedAbsent : stop.renamed.publishedView.child stop.renamed.root "WAL.commit.next" = none

theorem custody (stop : NativeWriteMarkerDirectoryStop prepared) (valid : before.Valid) : stop.Custody := by
  let seen := stop.renamed
  obtain ⟨previous, inode, live, captured, checked⟩ := seen.selectsKeeper.custody
  obtain ⟨keeper, lock, marker⟩ := seen.renameBindings
  have atCut : stop.reached.1 = seen.afterSelect := seen.censusAfterClose
  refine ⟨atCut, atCut.symm ▸ seen.markerFresh, atCut.symm ▸ previous _ valid.directoryLive,
    atCut.symm ▸ previous _ valid.ownerLive, atCut.symm ▸ live, ?_, ?_, ?_, ?_, atCut.symm ▸ captured, ?_, stop.sourceGone⟩
  · rw [seen.renameObjects, seen.stageObjects, atCut, inode, seen.directoryIdentity]
  · rw [atCut, inode, seen.sameDirectoryInode]
  · rw [lock, Option.map_some, seen.renameObjects, seen.stageObjects, atCut, inode, seen.lockIdentity]
  · rw [keeper, Option.map_some, seen.renameObjects, seen.stageObjects, atCut, checked]
  · rw [marker, Option.map_some, seen.renameObjects, atCut, inode, seen.stageIdentity]

end NativeWriteMarkerDirectoryStop
/-- Stop in the real final sync with the keeper and original owner still
held. The reached image chooses the replay before a later reopen. -/
structure NativePendingMarkerDirectory (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} (stop : NativeWriteMarkerDirectoryStop prepared) : Prop where
  stopped : stop.run = .error current.state.session.directory.path
    (.poisoned, ⟨(stop.renamed.appendCache, stop.reached), current.state.files.owners⟩)
  phase : stop.session.phase = .poisoned
  held : current.state.files.owners.Owns current.state.session.directory current.state.session.descriptor
  custody : stop.Custody
  pending : stop.renamed.appendCache.pending = []
  active : stop.renamed.appendCache.active = some (prepared.keeperPath, stop.renamed.keeperHandle)
  directory : stop.renamed.appendCache.directory = some (stop.renamed.directoryCapture, current.state.directorySlot, 0)
  livePair : stop.files.directory.active = stop.newPair
  crashPairs : stop.files.directory.crashImages = (if stop.applied then [stop.newPair] else [stop.newPair, current.state.writer.target.pair])
  scratch : stop.files.directory.staged .walBoundary = none
  keeper : stop.files.keeper.active = some (current.state.writer.wal.active.bytes ++ WAL.encode prepared.batch)
  durableKeeper : stop.files.keeper.crashImages = [stop.files.keeper.active]
  seals : stop.files.kept = current.state.files.image.kept
  later : stop.files.later = current.state.files.image.later
  selections : NativeMarkerCutReplay current prepared stop.files
  liveReplay : PendingClientReplay (log ++ [.uncertainBatch prepared.batch]) current.reads (history ++ prepared.batch)
  liveBounds : ∀ read ∈ current.reads, read.BoundedBy (history ++ prepared.batch).length

theorem NativeReadPosition.stopsAtMarkerDirectory (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} (stop : NativeWriteMarkerDirectoryStop prepared) :
    NativePendingMarkerDirectory current stop := by
  let valid := current.readPrefix.refines.1
  obtain ⟨live, crash, scratch, keeper, durable⟩ := stop.choices valid
  have selections := current.replaysMarkerCut prepared stop.cut (stop.batchCut valid) keeper
  obtain ⟨whole, bounded⟩ := selections.wholeAt (List.mem_cons_self .. : stop.files.directory.active ∈ _)
    (congrArg DirectoryPublication.Bindings.walBoundary live)
  exact ⟨stop.stopsWrite valid, rfl, valid.retained.held, stop.custody valid, stop.renamed.pendingEmpty, rfl,
    stop.renamed.directoryCached, live, crash, scratch, keeper, durable, rfl, rfl, selections, whole, bounded⟩

end Alvoki.Storage.DiskSession
