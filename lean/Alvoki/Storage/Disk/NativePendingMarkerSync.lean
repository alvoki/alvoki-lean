import Alvoki.Storage.Disk.BatchInterruptionDispatch
import Alvoki.Storage.Disk.NativeReadRecoveryTrace
import Alvoki.Storage.Disk.WalSegmentAppendPowerLoss

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentCommit WalSegmentRepair WAL.Boundary

private abbrev MarkerFiles := DescriptorInventory × WriteFiles
private abbrev MarkerState := CensusDirectoryCache × MarkerFiles
private abbrev MarkerM := ExceptT IO.Error (EStateM FilePath MarkerState)

/-- An issued keeper fsync after the actual append and stage write. The
raw stop may sync the keeper, while its staged marker has yet to be synced.
The interrupted interval contains no other descriptor or namespace events. -/
structure NativeWriteKeeperSyncStop {before : NativeReadyState} (prepared : NativeReadyWritePreparation before) where
  request : WriteRequest
  rows : request.rows = prepared.rows
  staging : NativeReadyWriteStaging prepared
  oldMarker : RunChildLookup staging.root "WAL.commit" staging.view
  openRead : FilePath → EStateM IO.Error WriteFiles CheckpointOpenHandle
  fsync : CheckpointOpenHandle → EStateM FilePath MarkerFiles (Except IO.Error Unit)
  effect : WalSyncEffect
  stopped : fsync staging.keeperHandle (staging.afterMarkerOpen, prepared.staged) =
    .error prepared.keeperPath (staging.afterMarkerOpen,
      (MarkerInterruption.groupSync effect false).interrupt prepared.marker prepared.staged)

namespace NativeWriteKeeperSyncStop

variable {before : NativeReadyState} {prepared : NativeReadyWritePreparation before}

def cut (stop : NativeWriteKeeperSyncStop prepared) : MarkerInterruption := .groupSync stop.effect false

def reached (stop : NativeWriteKeeperSyncStop prepared) : MarkerFiles :=
  (stop.staging.afterMarkerOpen, stop.cut.interrupt prepared.marker prepared.staged)

def session (_stop : NativeWriteKeeperSyncStop prepared) : SegmentedSession :=
  { before.session with phase := .poisoned }

private def withInventory {α : Type} (op : EStateM IO.Error WriteFiles α) : EStateM IO.Error MarkerFiles α :=
  fun (inventory, files) => match op files with
  | .ok value reached => .ok value (inventory, reached)
  | .error cause reached => .error cause (inventory, reached)

private def returnedWithInventory (census : DescriptorInventory)
    (op : EStateM IO.Error (CensusDirectoryCache × WriteFiles) Unit) : MarkerM Unit :=
  fun (cache, inventory, files) => match op (cache, files) with
  | .ok value (reachedCache, reached) => .ok (.ok value) (reachedCache, census, reached)
  | .error cause (reachedCache, reached) => .ok (.error cause) (reachedCache, inventory, reached)

/-- Use the same cache selector and propagate the raw stop outside the
ordinary IO error that the grouped sync would save and continue past. -/
def syncPath (stop : NativeWriteKeeperSyncStop prepared) (path : FilePath) : MarkerM Unit :=
  fun (cache, files) =>
    match cache.resolve before.session.directory.path path (fun p => withInventory (stop.openRead p)) files with
    | .error cause reached => .ok (.error cause) reached
    | .ok handle (cache, files) =>
      match stop.fsync handle files with
      | .ok result reached => .ok result (cache, reached)
      | .error path reached => .error path (cache, reached)

theorem stopsGroup (stop : NativeWriteKeeperSyncStop prepared) :
    (SyncPathGroup.run stop.syncPath #[prepared.keeperPath, prepared.stagedPath]).run
      (stop.staging.groupCache, stop.staging.afterMarkerOpen, prepared.staged) =
    .error prepared.keeperPath (stop.staging.groupCache, stop.reached) := by
  have stopped : stop.syncPath prepared.keeperPath
      (stop.staging.groupCache, stop.staging.afterMarkerOpen, prepared.staged) =
      .error prepared.keeperPath (stop.staging.groupCache, stop.reached) := by
    simp only [syncPath, stop.staging.selectsKeeperSync, stop.stopped, reached, cut]
  simp [SyncPathGroup.run, ← Array.forIn_toList, List.forIn_cons, MonadExcept.tryCatch,
    MonadExceptOf.tryCatch, tryCatchThe, ExceptT.tryCatch, Bind.bind, ExceptT.bind, ExceptT.run,
    ExceptT.mk, EStateM.bind, stopped]

noncomputable def publication (stop : NativeWriteKeeperSyncStop prepared)
    (rename : FilePath → FilePath → MarkerM Unit) (installed : Installed) (events : List WAL.Write)
    (bytes : Nat) : MarkerM Unit :=
  commitBytesAt before.session.directory installed.activeFirst (WAL.encodeBatch events) bytes
    (fun path payload => returnedWithInventory stop.staging.afterSelect (stop.staging.append path payload))
    (fun path payload => returnedWithInventory stop.staging.afterMarkerOpen (stop.staging.stage path payload))
    (SyncPathGroup.run stop.syncPath) rename

theorem stopsPublication (stop : NativeWriteKeeperSyncStop prepared) (rename : FilePath → FilePath → MarkerM Unit) :
    (stop.publication rename before.writer.installed prepared.batch prepared.count).run
      (before.cache, before.census, prepared.initial) =
    .error prepared.keeperPath (stop.staging.groupCache, stop.reached) := by
  rw [publication, commitBytesAt_fileEffects]
  have keeper := stop.stopsGroup
  change (SyncPathGroup.run stop.syncPath #[prepared.keeperPath, prepared.stagedPath])
    (stop.staging.groupCache, stop.staging.afterMarkerOpen, prepared.staged) = _ at keeper
  simp only [WAL.Boundary.commit, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run, EStateM.bind,
    returnedWithInventory, stop.staging.appendReturns, show WAL.Boundary.encode prepared.count.toUInt64 = prepared.marker from rfl,
    stop.staging.stageReturns, keeper]

noncomputable def run (stop : NativeWriteKeeperSyncStop prepared) (rename : FilePath → FilePath → MarkerM Unit) :=
  stop.request.runWithInterruption before.session.directory stop.staging.activeGuard.lookup (stop.publication rename)
    (before.session.phase, ⟨(before.cache, before.census, prepared.initial), before.files.owners⟩)

theorem stopsWrite (stop : NativeWriteKeeperSyncStop prepared) (valid : before.Valid) (rename) :
    stop.run rename = .error prepared.keeperPath (.poisoned, ⟨(stop.staging.groupCache, stop.reached), before.files.owners⟩) := by
  unfold run
  rw [valid.phase]
  exact stop.request.stopsPublication stop.rows prepared.nonempty prepared.prepared prepared.fits
    stop.staging.activeGuard (stop.publication rename) (stop.stopsPublication rename)

/-- Project the exact held file state. Before rename only the staging
entry can change the directory image. The keeper prefix remains durable. -/
def files (stop : NativeWriteKeeperSyncStop prepared) : FileImage :=
  resumedAppendFiles before.files.image before.writer.history before.writer.wal.active.first stop.reached.2

theorem atCut (stop : NativeWriteKeeperSyncStop prepared) : stop.reached.2 = prepared.staged.syncWal stop.effect := rfl

theorem selectsPrior (stop : NativeWriteKeeperSyncStop prepared) (valid : before.Valid) :
    stop.files.directory.active = before.writer.target.pair ∧
    stop.files.directory.crashImages = [before.writer.target.pair] ∧
    stop.files.directory.staged .walBoundary = some (prepared.marker, false) ∧
    stop.files.kept = before.files.image.kept ∧ stop.files.later = before.files.image.later ∧
    stop.files.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode before.writer.history).size.toUInt64) ∧
    SelectedIntegrityCheckpoint before.writer.published.durable stop.files.directory.active.manifest before.writer.checkpoint ∧
    stop.files.keeper.active = some (before.writer.wal.active.bytes ++ WAL.encode prepared.batch) ∧
    (∀ choice ∈ stop.files.keeper.active :: stop.files.keeper.crashImages, ∃ bytes,
      choice = some bytes ∧
      (stop.files.directory.active.walBoundary.mapM fun marker => do
        let count ← WAL.Boundary.decode marker
        selectRetained before.writer.installed.activeFirst count bytes) = .ok (some before.writer.wal.active.bytes)) := by
  let ready := valid.retained
  have sameMarker : stop.reached.2.marker.active = before.files.image.directory.active.walBoundary ∧
      stop.reached.2.marker.crashImages = (before.files.image.directory.project .walBoundary).crashImages := by
    rw [stop.atCut]
    have marker := ready.resumed.markerImage
    cases stop.effect <;>
      exact ⟨(congrArg Publication.Image.active marker).symm, (congrArg Publication.Image.crashImages marker).symm⟩
  have old : before.files.image.directory.active = before.writer.target.pair := ready.resumed.ready.selected
  have settled : before.files.image.directory.crashImages = [before.writer.target.pair] := ready.resumed.ready.settled
  have pair : stop.files.directory.active = before.writer.target.pair := by
    change DirectoryPublication.Bindings.mk before.files.image.directory.active.manifest stop.reached.2.marker.active = _
    rw [sameMarker.1]
    exact old
  refine ⟨pair, ?_, ?_, rfl, rfl, pair ▸ (ready.selectPriorKeeper ByteArray.empty).1, ?_, ?_, ?_⟩
  · change stop.reached.2.marker.crashImages.map
        (DirectoryPublication.Bindings.mk before.files.image.directory.active.manifest) = _
    rw [sameMarker.2]
    simp [DirectoryPublication.Image.project, DirectoryPublication.Bindings.get, settled, old]
  · change stop.reached.2.marker.staged = _
    rw [stop.atCut]
    cases stop.effect <;> rfl
  · exact pair.symm ▸ ready.resumed.selected
  · change some (WAL.encode (before.writer.history.drop before.writer.wal.active.first) ++ stop.reached.2.visibleTail) = _
    rw [← ready.layout.activeBytes, stop.atCut]
    cases stop.effect <;> rfl
  · let prefixBytes := WAL.encode (before.writer.history.drop before.writer.wal.active.first)
    have readPrefix (tail : ByteArray) :
        (stop.files.directory.active.walBoundary.mapM fun marker => do
          let count ← WAL.Boundary.decode marker
          selectRetained before.writer.installed.activeFirst count (prefixBytes ++ tail)) =
        .ok (some before.writer.wal.active.bytes) := by
      rw [pair, (ready.selectPriorKeeper tail).1, Option.mapM, WAL.Boundary.decode_encode]
      change (some <$> selectRetained before.writer.installed.activeFirst (WAL.encode before.writer.history).size.toUInt64
        (prefixBytes ++ tail)) = _
      rw [(ready.selectPriorKeeper tail).2]
      rfl
    intro choice member
    change choice ∈ some (prefixBytes ++ stop.reached.2.visibleTail) ::
      stop.reached.2.crashTails.map (fun tail => some (prefixBytes ++ tail)) at member
    rcases List.mem_cons.mp member with rfl | survived
    · exact ⟨_, rfl, readPrefix _⟩
    · obtain ⟨tail, _, rfl⟩ := List.mem_map.mp survived
      exact ⟨_, rfl, readPrefix tail⟩

end NativeWriteKeeperSyncStop

namespace NativeReadyWriteStageAllocation

variable {before : NativeReadyState} {prepared : NativeReadyWritePreparation before}

/-- The original held directory and keeper remain live alongside the
staged marker from its observed open until that temporary slot closes. -/
structure Custody (seen : NativeReadyWriteStageAllocation prepared)
    (oldMarker : RunChildLookup seen.root "WAL.commit" seen.view) : Prop where
  inodeMap : seen.afterMarkerOpen.inode = before.census.inode
  keeperLive : seen.keeperSlot ∈ seen.afterMarkerOpen.slots
  stagedLive : seen.markerSlot ∈ seen.afterMarkerOpen.slots
  ownerLive : before.owner ∈ seen.afterMarkerOpen.slots
  directoryLive : before.directorySlot ∈ seen.afterMarkerOpen.slots
  keeperNamed : (seen.stageView.child seen.root prepared.keeperName).map seen.stageView.modelObject =
    some (seen.afterMarkerOpen.inode seen.keeperSlot.description)
  stagedNamed : (seen.stageView.child seen.root "WAL.commit.next").map seen.stageView.modelObject =
    some (seen.afterMarkerOpen.inode seen.markerSlot.description)
  priorMarkerNamed : seen.stageView.child seen.root "WAL.commit" = some oldMarker.child
  lockNamed : (seen.stageView.child seen.root "LOCK").map seen.stageView.modelObject =
    some (seen.afterMarkerOpen.inode before.owner.description)
  directoryNamed : seen.stageView.modelObject seen.root = seen.afterMarkerOpen.inode before.directorySlot.description
  keeperHandle : seen.keeperHandle.1.inode seen.keeperSlot.description =
    seen.afterMarkerOpen.inode seen.keeperSlot.description
  directoryHandle : seen.directoryCapture.inode before.directorySlot.description =
    seen.afterMarkerOpen.inode before.directorySlot.description
  separate : seen.afterMarkerOpen.inode seen.markerSlot.description ≠ seen.afterMarkerOpen.inode seen.keeperSlot.description

theorem custody (seen : NativeReadyWriteStageAllocation prepared) (valid : before.Valid)
    (oldMarker : RunChildLookup seen.root "WAL.commit" seen.view) : seen.Custody oldMarker := by
  obtain ⟨previous, inode, keeperLive, captured, checked⟩ := seen.selectsKeeper.custody
  obtain ⟨keeper, lock, staged⟩ := seen.stageBindings
  have markerLookup : seen.view.child seen.root "WAL.commit" = some oldMarker.child := by
    simpa only [oldMarker.atRoot, oldMarker.atName] using oldMarker.binds
  exact ⟨inode, List.mem_cons_of_mem _ keeperLive, List.mem_cons_self,
    List.mem_cons_of_mem _ (previous _ valid.ownerLive), List.mem_cons_of_mem _ (previous _ valid.directoryLive),
    by rw [keeper, Option.map_some, seen.stageObjects]; exact congrArg some checked,
    by rw [staged, Option.map_some, seen.stageIdentity]; exact congrArg some (congrFun inode _).symm,
    (seen.stageNames _ (by decide)).trans markerLookup,
    by rw [lock, Option.map_some, seen.stageObjects]; exact congrArg some (seen.lockIdentity.trans (congrFun inode _).symm),
    by rw [seen.stageObjects]; exact seen.directoryIdentity.trans (congrFun inode _).symm,
    captured, seen.sameDirectoryInode.trans (congrFun inode _).symm,
    fun same => seen.differentFiles ((congrFun inode _).symm.trans (same.trans (congrFun inode _)))⟩

end NativeReadyWriteStageAllocation

namespace NativeWriteKeeperSyncStop

variable {before : NativeReadyState} {prepared : NativeReadyWritePreparation before}

abbrev Custody (stop : NativeWriteKeeperSyncStop prepared) : Prop := stop.staging.Custody stop.oldMarker

theorem custody (stop : NativeWriteKeeperSyncStop prepared) (valid : before.Valid) : stop.Custody :=
  stop.staging.custody valid stop.oldMarker

end NativeWriteKeeperSyncStop
/-- The issued write keeps its held lock and exact cache. Its one
uncertain batch adds no selected frames before the old marker is replaced. -/
structure NativePendingKeeperSync (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} (stop : NativeWriteKeeperSyncStop prepared) : Prop where
  stopped : ∀ rename, stop.run rename = .error prepared.keeperPath
    (.poisoned, ⟨(stop.staging.groupCache, stop.reached), current.state.files.owners⟩)
  held : current.state.files.owners.Owns current.state.session.directory current.state.session.descriptor
  phase : stop.session.phase = .poisoned
  custody : stop.Custody
  pending : stop.staging.groupCache.pending = [(prepared.stagedPath, stop.staging.stageHandle)]
  active : stop.staging.groupCache.active = some (prepared.keeperPath, stop.staging.keeperHandle)
  directory : stop.staging.groupCache.directory = some (stop.staging.directoryCapture, current.state.directorySlot, 0)
  pair : stop.files.directory.active = current.state.writer.target.pair
  survivors : stop.files.directory.crashImages = [current.state.writer.target.pair]
  scratch : stop.files.directory.staged .walBoundary = some (prepared.marker, false)
  seals : stop.files.kept = current.state.files.image.kept
  later : stop.files.later = current.state.files.image.later
  marker : stop.files.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64)
  checkpoint : SelectedIntegrityCheckpoint current.state.writer.published.durable stop.files.directory.active.manifest
    current.state.writer.checkpoint
  visible : stop.files.keeper.active = some (current.state.writer.wal.active.bytes ++ WAL.encode prepared.batch)
  keeperPrefix : ∀ choice ∈ stop.files.keeper.active :: stop.files.keeper.crashImages, ∃ bytes,
    choice = some bytes ∧
    (stop.files.directory.active.walBoundary.mapM fun marker => do
      let count ← WAL.Boundary.decode marker
      selectRetained current.state.writer.installed.activeFirst count bytes) = .ok (some current.state.writer.wal.active.bytes)
  replay : PendingClientReplay (log ++ [.uncertainBatch prepared.batch]) current.reads history
  bounded : ∀ read ∈ current.reads, read.BoundedBy history.length

theorem NativeReadPosition.stopsAtKeeperSync (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} (stop : NativeWriteKeeperSyncStop prepared) :
    NativePendingKeeperSync current stop := by
  obtain ⟨valid, exactHistory, prior⟩ := current.readPrefix.refines
  have ordered : WAL.OrdinalsFrom 1 history := exactHistory ▸ valid.retained.resumed.ordered
  obtain ⟨replay, bounded⟩ := prior.appendUncertain (batch := prepared.batch) current.readPrefix.readsBounded (.inl rfl) ordered
  obtain ⟨pair, survivors, scratch, seals, later, marker, checkpoint, visible, keeperPrefix⟩ := stop.selectsPrior valid
  exact ⟨stop.stopsWrite valid, valid.retained.held, rfl, stop.custody valid,
    by simp [Cache.remember, pushPending, stop.staging.pendingEmpty],
    rfl, stop.staging.directoryCached, pair, survivors, scratch, seals, later, by simpa only [exactHistory] using marker,
    checkpoint, visible, keeperPrefix, replay, bounded⟩

end Alvoki.Storage.DiskSession
