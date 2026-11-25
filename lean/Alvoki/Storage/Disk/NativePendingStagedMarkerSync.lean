import Alvoki.Storage.Disk.NativePendingMarkerSync
import Alvoki.Storage.Disk.NativePendingMarkerRename

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentCommit WalSegmentRepair WAL.Boundary

private abbrev StagedFiles := DescriptorInventory × WriteFiles
private abbrev StagedState := CensusDirectoryCache × StagedFiles
private abbrev StagedM := ExceptT IO.Error (EStateM FilePath StagedState)

/-- The first file fsync has returned successfully. The second consumes
its pending cache entry and stops with the same temporary slot still live.
Its local release has yet to run. -/
structure NativeWriteStagedMarkerSyncStop {before : NativeReadyState} (prepared : NativeReadyWritePreparation before) where
  request : WriteRequest
  rows : request.rows = prepared.rows
  staging : NativeReadyWriteStaging prepared
  oldMarker : RunChildLookup staging.root "WAL.commit" staging.view
  freshInode : staging.stageView.modelObject staging.openedMarker.child ≠ staging.view.modelObject oldMarker.child
  openRead : FilePath → EStateM IO.Error StagedFiles CheckpointOpenHandle
  fsync : CheckpointOpenHandle → EStateM FilePath StagedFiles (Except IO.Error Unit)
  kept : fsync staging.keeperHandle (staging.afterMarkerOpen, prepared.staged) =
    .ok (.ok ()) (staging.afterMarkerOpen, prepared.keeperSynced)
  applied : Bool
  stopped : fsync staging.stageHandle (staging.afterMarkerOpen, prepared.keeperSynced) =
    .error prepared.stagedPath (staging.afterMarkerOpen,
      (MarkerInterruption.groupSync .complete applied).interrupt prepared.marker prepared.staged)

namespace NativeWriteStagedMarkerSyncStop

variable {before : NativeReadyState} {prepared : NativeReadyWritePreparation before}

def cut (stop : NativeWriteStagedMarkerSyncStop prepared) : MarkerInterruption := .groupSync .complete stop.applied

def reached (stop : NativeWriteStagedMarkerSyncStop prepared) : StagedFiles :=
  (stop.staging.afterMarkerOpen, stop.cut.interrupt prepared.marker prepared.staged)

def session (_stop : NativeWriteStagedMarkerSyncStop prepared) : SegmentedSession :=
  { before.session with phase := .poisoned }

def syncPath (stop : NativeWriteStagedMarkerSyncStop prepared) (path : FilePath) : StagedM Unit :=
  fun (cache, files) =>
    match cache.resolve before.session.directory.path path stop.openRead files with
    | .error cause reached => .ok (.error cause) reached
    | .ok handle (cache, files) =>
      match stop.fsync handle files with
      | .ok result reached => .ok result (cache, reached)
      | .error path reached => .error path (cache, reached)

theorem stopsGroup (stop : NativeWriteStagedMarkerSyncStop prepared) :
    (SyncPathGroup.run stop.syncPath #[prepared.keeperPath, prepared.stagedPath]).run
      (stop.staging.groupCache, stop.staging.afterMarkerOpen, prepared.staged) =
    .error prepared.stagedPath (stop.staging.appendCache, stop.reached) := by
  have keeper : stop.syncPath prepared.keeperPath (stop.staging.groupCache, stop.staging.afterMarkerOpen, prepared.staged) =
      .ok (.ok ()) (stop.staging.groupCache, stop.staging.afterMarkerOpen, prepared.keeperSynced) := by
    simp only [syncPath, stop.staging.selectsKeeperSync, stop.kept]
  have staged : stop.syncPath prepared.stagedPath (stop.staging.groupCache, stop.staging.afterMarkerOpen, prepared.keeperSynced) =
      .error prepared.stagedPath (stop.staging.appendCache, stop.reached) := by
    simp only [syncPath, stop.staging.selectsStageSync, stop.stopped, cut, reached]
  simp [SyncPathGroup.run, ← Array.forIn_toList, List.forIn_cons, MonadExcept.tryCatch,
    MonadExceptOf.tryCatch, tryCatchThe, ExceptT.tryCatch, Bind.bind, ExceptT.bind, ExceptT.bindCont,
    ExceptT.run, ExceptT.mk, EStateM.bind, StateT.pure, Pure.pure, ExceptT.pure, EStateM.pure, keeper, staged]

noncomputable def publication (stop : NativeWriteStagedMarkerSyncStop prepared)
    (rename : FilePath → FilePath → StagedM Unit) (installed : Installed) (events : List WAL.Write) (bytes : Nat) : StagedM Unit :=
  let seen := stop.staging
  commitBytesAt before.session.directory installed.activeFirst (WAL.encodeBatch events) bytes
    (fun path payload => observeReturnedWriteCall seen.afterSelect (seen.append path payload))
    (fun path payload => observeReturnedWriteCall seen.afterMarkerOpen (seen.stage path payload))
    (SyncPathGroup.run stop.syncPath) rename

theorem stopsPublication (stop : NativeWriteStagedMarkerSyncStop prepared) (rename : FilePath → FilePath → StagedM Unit) :
    (stop.publication rename before.writer.installed prepared.batch prepared.count).run
      (before.cache, before.census, prepared.initial) =
    .error prepared.stagedPath (stop.staging.appendCache, stop.reached) := by
  have group := stop.stopsGroup
  change (SyncPathGroup.run stop.syncPath #[prepared.keeperPath, prepared.stagedPath])
    (stop.staging.groupCache, stop.staging.afterMarkerOpen, prepared.staged) = _ at group
  rw [publication, commitBytesAt_fileEffects]
  simp only [WAL.Boundary.commit, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run, EStateM.bind,
    observeReturnedWriteCall, stop.staging.appendReturns, show WAL.Boundary.encode prepared.count.toUInt64 = prepared.marker from rfl,
    stop.staging.stageReturns, group]

noncomputable def run (stop : NativeWriteStagedMarkerSyncStop prepared) (rename : FilePath → FilePath → StagedM Unit) :=
  stop.request.runWithInterruption before.session.directory stop.staging.activeGuard.lookup (stop.publication rename)
    (before.session.phase, ⟨(before.cache, before.census, prepared.initial), before.files.owners⟩)

theorem stopsWrite (stop : NativeWriteStagedMarkerSyncStop prepared) (valid : before.Valid) (rename) :
    stop.run rename = .error prepared.stagedPath (.poisoned, ⟨(stop.staging.appendCache, stop.reached), before.files.owners⟩) := by
  unfold run
  rw [valid.phase]
  exact stop.request.stopsPublication stop.rows prepared.nonempty prepared.prepared prepared.fits
    stop.staging.activeGuard (stop.publication rename) (stop.stopsPublication rename)

def files (stop : NativeWriteStagedMarkerSyncStop prepared) : FileImage :=
  resumedAppendFiles before.files.image before.writer.history before.writer.wal.active.first stop.reached.2

theorem atCut (stop : NativeWriteStagedMarkerSyncStop prepared) :
    stop.reached.2 = if stop.applied then prepared.bothSynced else prepared.keeperSynced := by
  unfold reached cut
  cases stop.applied <;> rfl

theorem batchCut (stop : NativeWriteStagedMarkerSyncStop prepared) (valid : before.Valid) :
    BatchCutProjection stop.files (prepared.modeledMarkerCut stop.cut) := by
  apply prepared.projectMarkerCut valid stop.cut
  simp only [MarkerInterruption.reachedBatch, (prepared.extended valid).1]
  rfl

/-- Both scratch sync effects leave the old marker authoritative. The
keeper file was synced in full by the first callback. -/
theorem choices (stop : NativeWriteStagedMarkerSyncStop prepared) (valid : before.Valid) :
    stop.files.directory.active = before.writer.target.pair ∧
    stop.files.directory.crashImages = [before.writer.target.pair] ∧
    stop.files.directory.staged .walBoundary = some (prepared.marker, stop.applied) ∧
    stop.files.keeper.active = some (before.writer.wal.active.bytes ++ WAL.encode prepared.batch) ∧
    stop.files.keeper.crashImages = [stop.files.keeper.active] := by
  have old : before.files.image.directory.active = before.writer.target.pair := valid.retained.resumed.ready.selected
  have marker := (valid.retained.selectPriorKeeper ByteArray.empty).1
  have pair :
      (⟨before.files.image.directory.active.manifest, some (WAL.Boundary.encode (WAL.encode before.writer.history).size.toUInt64)⟩ :
        DirectoryPublication.Bindings) = before.writer.target.pair := by
    rw [old, ← marker]
  have bytes := congrArg (fun bytes => some (bytes ++ WAL.encode prepared.batch)) valid.retained.layout.activeBytes.symm
  unfold files
  rw [stop.atCut]
  cases ran : stop.applied <;> exact ⟨pair, congrArg (fun pair => [pair]) pair, rfl, bytes, rfl⟩

end NativeWriteStagedMarkerSyncStop
/-- At the second file fsync the pending entry has been consumed, and
no marker rename or return is needed to know the selected history. -/
structure NativePendingStagedMarkerSync (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} (stop : NativeWriteStagedMarkerSyncStop prepared) : Prop where
  stopped : ∀ rename, stop.run rename = .error prepared.stagedPath
    (.poisoned, ⟨(stop.staging.appendCache, stop.reached), current.state.files.owners⟩)
  phase : stop.session.phase = .poisoned
  held : current.state.files.owners.Owns current.state.session.directory current.state.session.descriptor
  custody : stop.staging.Custody stop.oldMarker
  separateMarker : stop.reached.1.inode stop.staging.markerSlot.description ≠ stop.staging.view.modelObject stop.oldMarker.child
  pending : stop.staging.appendCache.pending = []
  active : stop.staging.appendCache.active = some (prepared.keeperPath, stop.staging.keeperHandle)
  directory : stop.staging.appendCache.directory = some (stop.staging.directoryCapture, current.state.directorySlot, 0)
  pair : stop.files.directory.active = current.state.writer.target.pair
  crashPairs : stop.files.directory.crashImages = [current.state.writer.target.pair]
  scratch : stop.files.directory.staged .walBoundary = some (prepared.marker, stop.applied)
  keeper : stop.files.keeper.active = some (current.state.writer.wal.active.bytes ++ WAL.encode prepared.batch)
  durableKeeper : stop.files.keeper.crashImages = [stop.files.keeper.active]
  seals : stop.files.kept = current.state.files.image.kept
  later : stop.files.later = current.state.files.image.later
  marker : stop.files.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64)
  checkpoint : SelectedIntegrityCheckpoint current.state.writer.published.durable stop.files.directory.active.manifest
    current.state.writer.checkpoint
  selected : selectRetained current.state.writer.installed.activeFirst (WAL.encode history).size.toUInt64
    (current.state.writer.wal.active.bytes ++ WAL.encode prepared.batch) = .ok current.state.writer.wal.active.bytes
  replay : PendingClientReplay (log ++ [.uncertainBatch prepared.batch]) current.reads history
  bounded : ∀ read ∈ current.reads, read.BoundedBy history.length

theorem NativeReadPosition.stopsAtStagedMarkerSync (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} (stop : NativeWriteStagedMarkerSyncStop prepared) :
    NativePendingStagedMarkerSync current stop := by
  obtain ⟨valid, exactHistory, earlier⟩ := current.readPrefix.refines
  let ready := valid.retained
  obtain ⟨pair, crash, scratch, keeper, durable⟩ := stop.choices valid
  obtain ⟨marker, selected⟩ := ready.selectPriorKeeper (WAL.encode prepared.batch)
  have ordered : WAL.OrdinalsFrom 1 history := exactHistory ▸ ready.resumed.ordered
  obtain ⟨pending, bounded⟩ := earlier.appendUncertain (batch := prepared.batch) current.readPrefix.readsBounded (.inl rfl) ordered
  have custody := stop.staging.custody valid stop.oldMarker
  refine ⟨stop.stopsWrite valid, rfl, ready.held, custody, ?_, stop.staging.pendingEmpty,
    rfl, stop.staging.directoryCached, pair, crash, scratch, keeper, durable, rfl, rfl, ?_,
    pair.symm ▸ ready.resumed.selected, ?_, pending, bounded⟩
  · intro alias
    obtain ⟨_, _, stage⟩ := stop.staging.stageBindings
    have stageInode := custody.stagedNamed
    rw [stage, Option.map_some] at stageInode
    exact stop.freshInode ((Option.some.inj stageInode).trans alias)
  · rw [pair, marker, exactHistory]
  · rw [← ready.layout.activeBytes, exactHistory] at selected
    exact selected

end Alvoki.Storage.DiskSession
