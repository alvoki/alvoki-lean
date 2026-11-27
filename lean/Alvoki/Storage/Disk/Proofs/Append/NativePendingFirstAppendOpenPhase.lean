import Alvoki.Storage.Disk.Proofs.Append.NativePendingFirstAppend
import Alvoki.Storage.Disk.NativePendingMarkerRenameOpenPhase

namespace Alvoki.Storage.DiskSession

open System WalSegmentCommit WAL.Boundary

abbrev FirstAppendInterrupted := ExceptT IO.Error
  (EStateM (FilePath × ByteArray) (CensusDirectoryCache × DescriptorInventory × WriteFiles))

variable {heap : Type} {state : NativeReadyState} {prepared : NativeReadyWritePreparation state}

def NativeFirstAppendStop.onOpenPhase (seen : NativeFirstAppendStop prepared) (opened : NativeOpenedHandle heap)
    (flush : CheckpointOpenHandle → FirstAppendInterrupted Unit)
    (stage : FilePath → ByteArray → FirstAppendInterrupted Unit)
    (sync : Array FilePath → FirstAppendInterrupted Unit) (rename : FilePath → FilePath → FirstAppendInterrupted Unit) :=
  seen.request.runWithInterruptionOnOpenPhase state.session.directory seen.lookup
    (fun installed bytes count => commitBytesAt state.session.directory installed.activeFirst bytes count
      (seen.append flush) stage sync rename)
    opened.phase opened.get opened.set

variable {opened : NativeOpenedHandle heap}

/-- The source preflight reads and poisons the original opened cell.
The first data write stops on the selected keeper handle, before its
flush or a marker operation can run. -/
theorem NativeOpenedPosition.stopsWriteAtFirstAppend (current : NativeOpenedPosition opened)
    {prepared : NativeReadyWritePreparation current.current.ready.state} (seen : NativeFirstAppendStop prepared)
    (flush : CheckpointOpenHandle → FirstAppendInterrupted Unit)
    (stage : FilePath → ByteArray → FirstAppendInterrupted Unit)
    (sync : Array FilePath → FirstAppendInterrupted Unit) (rename : FilePath → FilePath → FirstAppendInterrupted Unit) :
    let state := current.current.ready.state
    opened.table.UsesOpenWriteSchedules state.session.directory opened.files opened.phase ∧
    NativePendingFirstAppend current.current.ready seen ∧
    ∃ poisoned : heap,
      opened.get opened.phase current.reached = .ok state.session.phase current.reached ∧
      opened.set opened.phase .poisoned current.reached = .ok () poisoned ∧
      opened.contents poisoned opened.phase = some .poisoned ∧
      seen.rawWrite seen.handle (WAL.encodeBatch prepared.batch) (seen.selectedCensus, prepared.initial) =
        .error seen.logical.appendCall seen.cutFiles ∧
      seen.onOpenPhase opened flush stage sync rename (current.reached, state.cache, state.census, prepared.initial) =
        .error seen.logical.appendCall (poisoned, state.cache, seen.cutFiles) := by
  intro state
  have valid := current.current.ready.readPrefix.refines.1
  have loaded := opened.phaseEffects.reads current.reached opened.phase state.session.phase current.stored
  obtain ⟨poisoned, excluded, poison⟩ := opened.phaseEffects.writes current.reached opened.phase state.session.phase
    .poisoned current.stored
  have checked : (checkActiveSegmentWith state.session.directory state.writer.installed seen.lookup : Except IO.Error Unit) =
      .ok () := by
    dsimp only [state]
    obtain ⟨metadata, found, regular, privateFile, extent⟩ := seen.valid.activeGuard
    change seen.lookup prepared.keeperPath = .ok metadata at found
    have kind : (IO.FS.FileType.file == .file) = true := rfl
    simp [checkActiveSegmentWith, checkPrivateRegularWith, found, regular, privateFile, extent, kind,
      Except.bind, Bind.bind, Except.pure, Pure.pure]
  refine ⟨current.uses.writeSchedules, current.current.ready.stopsAtFirstAppend seen, poisoned, loaded,
    excluded, poison, seen.stopped, ?_⟩
  unfold NativeFirstAppendStop.onOpenPhase
  apply seen.request.stopsPublicationOnOpenPhase state.session.directory seen.rows prepared.nonempty prepared.prepared
    prepared.fits checked _ (valid.phase ▸ loaded) excluded
  dsimp only [state]
  simp [commitBytesAt, WAL.Boundary.commit, Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk,
    EStateM.bind, seen.stopsAppend, NativeFirstAppendStop.logical]

end Alvoki.Storage.DiskSession
