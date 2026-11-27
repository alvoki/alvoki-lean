import Alvoki.Storage.Disk.Proofs.Write.NativePendingMarkerStageWrite
import Alvoki.Storage.Disk.Proofs.Native.WAL.NativePendingMarkerRenameOpenPhase

namespace Alvoki.Storage.DiskSession

open System WalSegmentCommit WAL.Boundary

private abbrev StageWriteInterrupted := ExceptT IO.Error
  (EStateM (FilePath × ByteArray) (CensusDirectoryCache × DescriptorInventory × WriteFiles))

variable {heap : Type} {state : NativeReadyState} {prepared : NativeReadyWritePreparation state}

noncomputable def NativeMarkerStageWriteStop.onOpenPhase (seen : NativeMarkerStageWriteStop prepared)
    (opened : NativeOpenedHandle heap) (flush : CheckpointOpenHandle → StageWriteInterrupted Unit)
    (sync : Array FilePath → StageWriteInterrupted Unit) (rename : FilePath → FilePath → StageWriteInterrupted Unit) :=
  seen.request.runWithInterruptionOnOpenPhase state.session.directory seen.allocated.activeGuard.lookup
    (fun installed bytes count => commitBytesAt state.session.directory installed.activeFirst bytes count
      (fun path payload => observeReturnedWriteCall seen.allocated.afterSelect (seen.allocated.append path payload))
      (seen.stage flush) sync rename)
    opened.phase opened.get opened.set

variable {opened : NativeOpenedHandle heap}

/-- The opened write leaves its phase poisoned at the staged data
write. The successful exclusive create supplied this descriptor,
and the outer stop carries the full submitted marker bytes. -/
theorem NativeOpenedPosition.stopsWriteAtMarkerStageWrite (current : NativeOpenedPosition opened)
    {prepared : NativeReadyWritePreparation current.current.ready.state} (seen : NativeMarkerStageWriteStop prepared) :
    let state := current.current.ready.state
    opened.table.UsesOpenWriteSchedules state.session.directory opened.files opened.phase ∧
    NativePendingMarkerStageWrite current.current.ready seen ∧
    ∃ poisoned : heap,
      opened.get opened.phase current.reached = .ok state.session.phase current.reached ∧
      opened.set opened.phase .poisoned current.reached = .ok () poisoned ∧
      opened.contents poisoned opened.phase = some .poisoned ∧
      ∀ flush sync rename,
        seen.onOpenPhase opened flush sync rename (current.reached, state.cache, state.census, prepared.initial) =
          .error (prepared.stagedPath, prepared.marker) (poisoned, seen.allocated.appendCache, seen.reached) := by
  intro state
  have valid := current.current.ready.readPrefix.refines.1
  have loaded := opened.phaseEffects.reads current.reached opened.phase state.session.phase current.stored
  obtain ⟨poisoned, excluded, poison⟩ := opened.phaseEffects.writes current.reached opened.phase state.session.phase
    .poisoned current.stored
  let guard := seen.allocated.activeGuard
  have checked : (checkActiveSegmentWith state.session.directory state.writer.installed guard.lookup : Except IO.Error Unit) =
      .ok () := by
    dsimp only [state]
    have regular : (IO.FS.FileType.file == .file) = true := rfl
    simp [checkActiveSegmentWith, checkPrivateRegularWith, guard.reached, guard.regular, guard.privateFile,
      guard.extent, regular, Except.bind, Bind.bind, Except.pure, Pure.pure]
  refine ⟨current.uses.writeSchedules, current.current.ready.stopsAtMarkerStageWrite seen,
    poisoned, loaded, excluded, poison, ?_⟩
  intro flush sync rename
  unfold NativeMarkerStageWriteStop.onOpenPhase
  apply seen.request.stopsPublicationOnOpenPhase state.session.directory seen.rows prepared.nonempty prepared.prepared
    prepared.fits checked _ (valid.phase ▸ loaded) excluded
  exact seen.stopsPublication flush sync rename

end Alvoki.Storage.DiskSession
