import Alvoki.Storage.Disk.NativeOpenedPosition
import Alvoki.Storage.Disk.NativeReadyWalCollection

namespace Alvoki.Storage.DiskSession

private abbrev CollectionFiles := CensusDirectoryCache × WalSealedUnlinkImage

private def onPhase {heap result : Type} (action : EStateM IO.Error heap result) :
    EStateM IO.Error (heap × CollectionFiles) result := fun (before, files) =>
  match action before with
  | .ok returned after => .ok returned (after, files)
  | .error cause after => .error cause (after, files)

private def onFiles {heap result : Type} (action : EStateM IO.Error CollectionFiles result) :
    EStateM IO.Error (heap × CollectionFiles) result := fun (phase, before) =>
  match action before with
  | .ok returned after => .ok returned (phase, after)
  | .error cause after => .error cause (phase, after)

/-- The public collection order reads the phase and selects the offsets
before poisoning the original cell. The observed collection unlinks and
cached directory sync finish before the ready phase is stored again. -/
def WalCollectionReads.collectOnOpenPhase {heap : Type}
    (calls : WalCollectionReads) (opened : NativeOpenedHandle heap)
    (publication : List Nat → EStateM IO.Error CollectionFiles Unit) :
    EStateM IO.Error (heap × CollectionFiles) Unit := do
  let installed ← (← onPhase (opened.get opened.phase)).installed
  let offsets ← liftExcept (calls.plan opened.directory installed)
  publishPrepared (fun phase => onPhase (opened.set opened.phase phase))
    (onFiles (publication offsets))
    (onPhase (opened.set opened.phase (.ready installed)))

def NativeReadyWalCollection.runOnOpenPhase {heap : Type} {state : NativeReadyState}
    (reported : NativeReadyWalCollection state) (opened : NativeOpenedHandle heap) :
    EStateM IO.Error (heap × CollectionFiles) Unit :=
  reported.calls.collectOnOpenPhase opened reported.publicationFiles

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- A successful public collection continues on its original handle.
The exact returned checkpoint, keeper, retained reads and history follow
from the unlink prefix and reported directory fsync. -/
theorem NativeOpenedPosition.collectsCoveredWal
    (start : NativeOpenedPosition opened)
    (observed : NativeReadyWalCollection start.current.ready.state)
    (completed : observed.barrier.outcome = .completed) :
    ∃ next : NativeOpenedPosition opened,
      opened.table.UsesOpenWalCollectionSchedule start.current.ready.state.session.directory opened.files opened.phase ∧
      observed.runOnOpenPhase opened
        (start.reached, start.current.ready.state.cache, .start start.current.ready.state.writer.wal) =
        .ok () (next.reached, next.current.ready.state.cache, observed.barrier.after) ∧
      next.current.ready.state = observed.next completed ∧ next.pins = start.pins ∧
      NativeExecutionStep start.current .collectCoveredWal next.current := by
  let state := start.current.ready.state
  have valid := start.current.ready.readPrefix.refines.1
  have completion := start.current.ready.readPrefix.collectsCoveredWal observed completed
  have readPhase := opened.phaseEffects.reads start.reached opened.phase _ start.stored
  obtain ⟨poisoned, poison, poisonedStored⟩ :=
    opened.phaseEffects.writes start.reached opened.phase _ .poisoned start.stored
  obtain ⟨reached, stored, reachedStored⟩ :=
    opened.phaseEffects.writes poisoned opened.phase _ state.session.phase poisonedStored
  have restored : opened.set opened.phase (.ready start.current.ready.state.writer.installed) poisoned =
      .ok () reached := by
    rw [← valid.phase]
    exact stored
  let nextReady := start.current.ready.afterMaintenance (observed.next completed) completion.valid completion.historyEq
  let next : NativeOpenedPosition opened :=
    ⟨⟨start.current.history, start.current.submissions, nextReady⟩, reached, start.directory, reachedStored, start.pins⟩
  refine ⟨next, start.uses.collectCoveredWal, ?_, rfl, rfl, .collectCoveredWal start.current observed completed completion⟩
  have plan := valid.retained.completeObservedWalPlan
    observed.calls observed.inventory observed.manifest observed.marker
  rw [start.directory] at plan
  have physical := observed.publicationFiles_returns valid completed
  simp only [NativeReadyWalCollection.runOnOpenPhase, WalCollectionReads.collectOnOpenPhase, onPhase, onFiles, Bind.bind, EStateM.bind, readPhase,
    valid.phase, Phase.installed, Pure.pure, EStateM.pure, liftExcept, plan, publishPrepared,
    poison, restored, physical, next, nextReady, NativeReadPosition.afterMaintenance,
    NativeReadyWalCollection.next]

/-- An extent rejection in the original collector returns before any
phase store or mutation callback. The same table and ready position can
take later operations using all existing pins and client replay. -/
theorem NativeOpenedPosition.rejectsCoveredWalPlan
    (start : NativeOpenedPosition opened)
    (observed : NativeWalPlanningObservation start.current.ready.state) {cause : IO.Error}
    (failed : observed.extents.result = .error cause) :
    opened.table.UsesOpenWalCollectionSchedule start.current.ready.state.session.directory opened.files opened.phase ∧
    (∀ publication,
      let entry := (start.reached, start.current.ready.state.cache, WalSealedUnlinkImage.start start.current.ready.state.writer.wal)
      observed.calls.collectOnOpenPhase opened publication entry = .error cause entry) ∧
    NativeExecutionStep start.current (.coveredWalCollectionRejected cause) start.current := by
  have valid := start.current.ready.readPrefix.refines.1
  have readPhase := opened.phaseEffects.reads start.reached opened.phase _ start.stored
  have plan := (observed.extents.plans valid).trans failed
  rw [start.directory] at plan
  have returned := (start.current.ready.plansWalCollection observed).1
  simp only [failed] at returned
  refine ⟨start.uses.collectCoveredWal, ?_, .rejectsCoveredWalPlan start.current observed cause failed returned⟩
  intro publication
  simp only [WalCollectionReads.collectOnOpenPhase, onPhase, Bind.bind, EStateM.bind, readPhase, valid.phase,
    Phase.installed, Pure.pure, EStateM.pure, liftExcept, plan, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

end Alvoki.Storage.DiskSession
