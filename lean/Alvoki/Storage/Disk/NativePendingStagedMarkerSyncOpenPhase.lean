import Alvoki.Storage.Disk.NativePendingStagedMarkerSync
import Alvoki.Storage.Disk.NativePendingMarkerRenameOpenPhase

namespace Alvoki.Storage.DiskSession

open System WalSegmentCommit WAL.Boundary

variable {heap : Type} {state : NativeReadyState} {prepared : NativeReadyWritePreparation state}

abbrev StagedMarkerSyncInterrupted := ExceptT IO.Error (EStateM FilePath (CensusDirectoryCache × DescriptorInventory × WriteFiles))

noncomputable def NativeWriteStagedMarkerSyncStop.onOpenPhase (seen : NativeWriteStagedMarkerSyncStop prepared)
    (opened : NativeOpenedHandle heap) (rename : FilePath → FilePath → StagedMarkerSyncInterrupted Unit) :=
  let staging := seen.staging
  seen.request.runWithInterruptionOnOpenPhase state.session.directory staging.activeGuard.lookup
    (fun installed bytes count => commitBytesAt state.session.directory installed.activeFirst bytes count
      (fun path payload => observeReturnedWriteCall staging.afterSelect (staging.append path payload))
      (fun path payload => observeReturnedWriteCall staging.afterMarkerOpen (staging.stage path payload))
      (SyncPathGroup.run seen.syncPath) rename)
    opened.phase opened.get opened.set

variable {opened : NativeOpenedHandle heap}

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
  have valid := current.current.ready.readPrefix.refines.1
  have loaded := opened.phaseEffects.reads current.reached opened.phase state.session.phase current.stored
  obtain ⟨poisoned, excluded, poison⟩ := opened.phaseEffects.writes current.reached opened.phase state.session.phase
    .poisoned current.stored
  let guard := seen.staging.activeGuard
  have checked : (checkActiveSegmentWith state.session.directory state.writer.installed guard.lookup : Except IO.Error Unit) =
      .ok () := by
    dsimp only [state]
    have regular : (IO.FS.FileType.file == .file) = true := rfl
    simp [checkActiveSegmentWith, checkPrivateRegularWith, guard.reached, guard.regular, guard.privateFile,
      guard.extent, regular, Except.bind, Bind.bind, Except.pure, Pure.pure]
  refine ⟨current.uses.writeSchedules, current.current.ready.stopsAtStagedMarkerSync seen, poisoned, loaded,
    excluded, poison, seen.stopsGroup, ?_⟩
  intro rename
  unfold NativeWriteStagedMarkerSyncStop.onOpenPhase
  apply seen.request.stopsPublicationOnOpenPhase state.session.directory seen.rows prepared.nonempty prepared.prepared
    prepared.fits checked _ (valid.phase ▸ loaded) excluded
  exact seen.stopsPublication rename

end Alvoki.Storage.DiskSession
