import Alvoki.Storage.Disk.NativePendingMarkerDirectory
import Alvoki.Storage.Disk.NativePendingMarkerRenameOpenPhase

namespace Alvoki.Storage.DiskSession

open System WalSegmentCommit

variable {heap stop : Type} {state : NativeReadyState} {prepared : NativeReadyWritePreparation state}

/-- After both file syncs, the returned rename moves the same staged
inode to the canonical marker. The directory sync is the next call. -/
noncomputable def NativeReadyWriteRenamed.beforeMarkerDirectory (seen : NativeReadyWriteRenamed prepared) :=
  seen.toNativeReadyWriteFileSyncs.beforeMarkerRename (stop := stop) >>= fun _ =>
  observeReturnedWriteCall (stop := stop) seen.census (seen.replace prepared.stagedPath prepared.markerPath)

theorem NativeReadyWriteRenamed.reachesMarkerDirectory (seen : NativeReadyWriteRenamed prepared) :
    (seen.beforeMarkerDirectory (stop := stop)).run (state.cache, state.census, prepared.initial) =
      .ok (.ok ()) (seen.appendCache, seen.census, prepared.renamed) := by
  have fileSyncs := seen.toNativeReadyWriteFileSyncs.reachesMarkerRename (stop := stop)
  change seen.toNativeReadyWriteFileSyncs.beforeMarkerRename (stop := stop) (state.cache, state.census, prepared.initial) = _ at fileSyncs
  simp only [beforeMarkerDirectory, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run, EStateM.bind,
    fileSyncs, observeReturnedWriteCall, seen.renameReturns]

noncomputable def NativeWriteMarkerDirectoryStop.onOpenPhase (seen : NativeWriteMarkerDirectoryStop prepared)
    (opened : NativeOpenedHandle heap) :=
  let renamed := seen.renamed
  seen.request.runWithInterruptionOnOpenPhase state.session.directory renamed.activeGuard.lookup
    (fun installed bytes count => commitBytesAt state.session.directory installed.activeFirst bytes count
      (fun path payload => observeReturnedWriteCall renamed.afterSelect (renamed.append path payload))
      (fun path payload => observeReturnedWriteCall renamed.afterMarkerOpen (renamed.stage path payload))
      (fun paths => if paths = #[state.session.directory.path] then SyncPathGroup.run seen.syncDirectory paths
        else observeReturnedWriteCall renamed.census (renamed.sync paths))
      (fun source target => observeReturnedWriteCall renamed.census (renamed.replace source target)))
    opened.phase opened.get opened.set

variable {opened : NativeOpenedHandle heap}

/-- The original opened phase remains poisoned after the returned
marker rename. The final directory callback issues on that same cache
and never returns to the write schedule. -/
theorem NativeOpenedPosition.stopsWriteAtMarkerDirectory (current : NativeOpenedPosition opened)
    {prepared : NativeReadyWritePreparation current.current.ready.state}
    (seen : NativeWriteMarkerDirectoryStop prepared) :
    let state := current.current.ready.state
    opened.table.UsesOpenWriteSchedules state.session.directory opened.files opened.phase ∧
    NativePendingMarkerDirectory current.current.ready seen ∧
    ∃ poisoned : heap,
      opened.get opened.phase current.reached = .ok state.session.phase current.reached ∧
      opened.set opened.phase .poisoned current.reached = .ok () poisoned ∧
      opened.contents poisoned opened.phase = some .poisoned ∧
      (seen.renamed.beforeMarkerDirectory (stop := FilePath)).run (state.cache, state.census, prepared.initial) =
        .ok (.ok ()) (seen.renamed.appendCache, seen.renamed.census, prepared.renamed) ∧
      (SyncPathGroup.run seen.syncDirectory #[state.session.directory.path]).run
        (seen.renamed.appendCache, seen.renamed.census, prepared.renamed) =
        .error state.session.directory.path (seen.renamed.appendCache, seen.reached) ∧
      seen.onOpenPhase opened (current.reached, state.cache, state.census, prepared.initial) =
        .error state.session.directory.path (poisoned, seen.renamed.appendCache, seen.reached) := by
  intro state
  have valid := current.current.ready.readPrefix.refines.1
  have loaded := opened.phaseEffects.reads current.reached opened.phase state.session.phase current.stored
  obtain ⟨poisoned, excluded, poison⟩ := opened.phaseEffects.writes current.reached opened.phase state.session.phase
    .poisoned current.stored
  let guard := seen.renamed.activeGuard
  have checked : (checkActiveSegmentWith state.session.directory state.writer.installed guard.lookup : Except IO.Error Unit) =
      .ok () := by
    dsimp only [state]
    have regular : (IO.FS.FileType.file == .file) = true := rfl
    simp [checkActiveSegmentWith, checkPrivateRegularWith, guard.reached, guard.regular, guard.privateFile,
      guard.extent, regular, Except.bind, Bind.bind, Except.pure, Pure.pure]
  refine ⟨current.uses.writeSchedules, current.current.ready.stopsAtMarkerDirectory seen, poisoned, loaded,
    excluded, poison, seen.renamed.reachesMarkerDirectory, seen.stopsDirectory, ?_⟩
  unfold NativeWriteMarkerDirectoryStop.onOpenPhase
  apply seen.request.stopsPublicationOnOpenPhase state.session.directory seen.rows prepared.nonempty prepared.prepared
    prepared.fits checked _ (valid.phase ▸ loaded) excluded
  exact seen.stopsPublication

end Alvoki.Storage.DiskSession
