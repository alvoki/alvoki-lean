import Alvoki.Storage.Disk.NativePendingStagedMarkerSync
import Alvoki.Storage.Disk.NativePendingMarkerRenameOpenPhase

namespace Alvoki.Storage.DiskSession

open System WalSegmentCommit WAL.Boundary

variable {heap : Type} {state : NativeReadyState} {prepared : NativeReadyWritePreparation state}

abbrev PublicationSyncInterrupted := ExceptT IO.Error (EStateM FilePath (CensusDirectoryCache × DescriptorInventory × WriteFiles))

private noncomputable def WriteRequest.runWithPublicationSyncOnOpenPhase (request : WriteRequest)
    (staging : NativeReadyWriteStaging prepared) (syncPath : FilePath → PublicationSyncInterrupted Unit)
    (opened : NativeOpenedHandle heap) (rename : FilePath → FilePath → PublicationSyncInterrupted Unit) :=
  request.runWithInterruptionOnOpenPhase state.session.directory staging.activeGuard.lookup
    (fun installed bytes count => commitBytesAt state.session.directory installed.activeFirst bytes count
      (fun path payload => observeReturnedWriteCall staging.afterSelect (staging.append path payload))
      (fun path payload => observeReturnedWriteCall staging.afterMarkerOpen (staging.stage path payload))
      (SyncPathGroup.run syncPath) rename)
    opened.phase opened.get opened.set

noncomputable def NativeWriteKeeperSyncStop.onOpenPhase (seen : NativeWriteKeeperSyncStop prepared)
    (opened : NativeOpenedHandle heap) (rename : FilePath → FilePath → PublicationSyncInterrupted Unit) :=
  seen.request.runWithPublicationSyncOnOpenPhase seen.staging seen.syncPath opened rename

noncomputable def NativeWriteStagedMarkerSyncStop.onOpenPhase (seen : NativeWriteStagedMarkerSyncStop prepared)
    (opened : NativeOpenedHandle heap) (rename : FilePath → FilePath → PublicationSyncInterrupted Unit) :=
  seen.request.runWithPublicationSyncOnOpenPhase seen.staging seen.syncPath opened rename

variable {opened : NativeOpenedHandle heap}

private theorem NativeOpenedPosition.stopsDuringPublicationSync (current : NativeOpenedPosition opened)
    {prepared : NativeReadyWritePreparation current.current.ready.state} (staging : NativeReadyWriteStaging prepared)
    (request : WriteRequest) (rows : request.rows = prepared.rows) (syncPath : FilePath → PublicationSyncInterrupted Unit)
    {issued : FilePath} {cache : CensusDirectoryCache} {files : DescriptorInventory × WriteFiles}
    (stopped : (SyncPathGroup.run syncPath #[prepared.keeperPath, prepared.stagedPath]).run
      (staging.groupCache, staging.afterMarkerOpen, prepared.staged) = .error issued (cache, files)) :
    let state := current.current.ready.state
    ∃ poisoned : heap,
      opened.get opened.phase current.reached = .ok state.session.phase current.reached ∧
      opened.set opened.phase .poisoned current.reached = .ok () poisoned ∧
      opened.contents poisoned opened.phase = some .poisoned ∧
      ∀ rename, request.runWithPublicationSyncOnOpenPhase staging syncPath opened rename
        (current.reached, state.cache, state.census, prepared.initial) = .error issued (poisoned, cache, files) := by
  intro state
  have valid := current.current.ready.readPrefix.refines.1
  have loaded := opened.phaseEffects.reads current.reached opened.phase state.session.phase current.stored
  obtain ⟨poisoned, excluded, poison⟩ := opened.phaseEffects.writes current.reached opened.phase state.session.phase
    .poisoned current.stored
  let guard := staging.activeGuard
  have checked : (checkActiveSegmentWith state.session.directory state.writer.installed guard.lookup : Except IO.Error Unit) =
      .ok () := by
    dsimp only [state]
    have regular : (IO.FS.FileType.file == .file) = true := rfl
    simp [checkActiveSegmentWith, checkPrivateRegularWith, guard.reached, guard.regular, guard.privateFile,
      guard.extent, regular, Except.bind, Bind.bind, Except.pure, Pure.pure]
  refine ⟨poisoned, loaded, excluded, poison, ?_⟩
  intro rename
  unfold WriteRequest.runWithPublicationSyncOnOpenPhase
  apply request.stopsPublicationOnOpenPhase state.session.directory rows prepared.nonempty prepared.prepared
    prepared.fits checked _ (valid.phase ▸ loaded) excluded
  change (SyncPathGroup.run syncPath #[prepared.keeperPath, prepared.stagedPath])
    (staging.groupCache, staging.afterMarkerOpen, prepared.staged) = _ at stopped
  change (commitBytesAt state.session.directory state.writer.installed.activeFirst (WAL.encodeBatch prepared.batch) prepared.count
    (fun path payload => observeReturnedWriteCall staging.afterSelect (staging.append path payload))
    (fun path payload => observeReturnedWriteCall staging.afterMarkerOpen (staging.stage path payload))
    (SyncPathGroup.run syncPath) rename).run (state.cache, state.census, prepared.initial) = _
  dsimp only [state]
  rw [commitBytesAt_fileEffects]
  simp only [WAL.Boundary.commit, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run, EStateM.bind,
    observeReturnedWriteCall, staging.appendReturns, show WAL.Boundary.encode prepared.count.toUInt64 = prepared.marker from rfl,
    staging.stageReturns, stopped]

/-- The original opened write reaches the first grouped fsync on its
keeper handle. The staged marker remains pending when this call stops. -/
theorem NativeOpenedPosition.stopsWriteAtKeeperSync (current : NativeOpenedPosition opened)
    {prepared : NativeReadyWritePreparation current.current.ready.state} (seen : NativeWriteKeeperSyncStop prepared) :
    let state := current.current.ready.state
    opened.table.UsesOpenWriteSchedules state.session.directory opened.files opened.phase ∧
    NativePendingKeeperSync current.current.ready seen ∧
    ∃ poisoned : heap,
      opened.get opened.phase current.reached = .ok state.session.phase current.reached ∧
      opened.set opened.phase .poisoned current.reached = .ok () poisoned ∧
      opened.contents poisoned opened.phase = some .poisoned ∧
      (SyncPathGroup.run seen.syncPath #[prepared.keeperPath, prepared.stagedPath]).run
        (seen.staging.groupCache, seen.staging.afterMarkerOpen, prepared.staged) =
        .error prepared.keeperPath (seen.staging.groupCache, seen.reached) ∧
      ∀ rename, seen.onOpenPhase opened rename (current.reached, state.cache, state.census, prepared.initial) =
        .error prepared.keeperPath (poisoned, seen.staging.groupCache, seen.reached) := by
  intro state
  obtain ⟨poisoned, loaded, excluded, poison, issue⟩ :=
    current.stopsDuringPublicationSync seen.staging seen.request seen.rows seen.syncPath seen.stopsGroup
  exact ⟨current.uses.writeSchedules, current.current.ready.stopsAtKeeperSync seen, poisoned,
    loaded, excluded, poison, seen.stopsGroup, issue⟩

/-- On the original opened phase cell the append and marker staging
have returned. The keeper fsync returns first. The staged marker fsync
consumes the pending cache entry and stops with its descriptor live. -/
theorem NativeOpenedPosition.stopsWriteAtStagedMarkerSync (current : NativeOpenedPosition opened)
    {prepared : NativeReadyWritePreparation current.current.ready.state} (seen : NativeWriteStagedMarkerSyncStop prepared) :
    let state := current.current.ready.state
    opened.table.UsesOpenWriteSchedules state.session.directory opened.files opened.phase ∧
    NativePendingStagedMarkerSync current.current.ready seen ∧
    ∃ poisoned : heap,
      opened.get opened.phase current.reached = .ok state.session.phase current.reached ∧
      opened.set opened.phase .poisoned current.reached = .ok () poisoned ∧
      opened.contents poisoned opened.phase = some .poisoned ∧
      (SyncPathGroup.run seen.syncPath #[prepared.keeperPath, prepared.stagedPath]).run
        (seen.staging.groupCache, seen.staging.afterMarkerOpen, prepared.staged) =
        .error prepared.stagedPath (seen.staging.appendCache, seen.reached) ∧
      ∀ rename, seen.onOpenPhase opened rename (current.reached, state.cache, state.census, prepared.initial) =
        .error prepared.stagedPath (poisoned, seen.staging.appendCache, seen.reached) := by
  intro state
  obtain ⟨poisoned, loaded, excluded, poison, issue⟩ :=
    current.stopsDuringPublicationSync seen.staging seen.request seen.rows seen.syncPath seen.stopsGroup
  exact ⟨current.uses.writeSchedules, current.current.ready.stopsAtStagedMarkerSync seen, poisoned,
    loaded, excluded, poison, seen.stopsGroup, issue⟩

end Alvoki.Storage.DiskSession
