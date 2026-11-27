import Alvoki.Storage.Disk.Proofs.Session.DiskCleanReopenAdmission
import Alvoki.Storage.Disk.Proofs.Session.PoisonedBatchClose

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

/-- A second explicit close succeeds without calling unlock or touching
any cache reference. Only the read of the closed phase is reached. -/
theorem closeSchedule_alreadyClosed {state : Type} {before : state}
    {getPhase : EStateM IO.Error state (Phase Installed)}
    (phase : getPhase before = .ok .closed before)
    (unlock : Unit → EStateM IO.Error state Unit)
    (active pending directory closed : EStateM IO.Error state Unit) :
    closeSchedule getPhase unlock active pending directory closed before = .ok () before := by
  simp [closeSchedule, Bind.bind, EStateM.bind, phase, Phase.close, Pure.pure, EStateM.pure]

/-- The clean handoff uses the very unlock observed by cached close. -/
def CachedCloseReports.cleanUnlock {handle image : Type} {directory : DiskDirectory} {descriptor : Nat}
    {before : CachedCloseState handle image} (close : CachedCloseReports directory descriptor before)
    (unlocked : close.result = .ok ()) : CleanUnlockReports directory descriptor where
  descriptors := before.descriptors
  slot := close.slot
  live := close.live
  description := close.description
  bindings := close.bindings
  lockObject := close.lockObject
  unlock := fun _ => close.result
  returned := unlocked

/-- The reported native close clears the ready writer's exact cache. Its
file and owner projection supplies the admitted reopen, using the reported
unchanged namespace between explicit unlock and reacquisition. -/
theorem SegmentedWriterState.RetainedReady.closeCachedWithAdmission
    {handle files : Type} {input : FilePath} {directory : DiskDirectory} {oldDescriptor : Nat}
    {before : SegmentedWriterState} (ready : before.RetainedReady directory oldDescriptor)
    (cache : Cache handle) (descriptors : DescriptorInventory)
    (close : CachedCloseReports directory oldDescriptor
      ⟨.ready before.installed, ⟨(cache, before.files), before.owners⟩, descriptors⟩)
    (unlocked : close.result = .ok ())
    (observes : (close.cleanUnlock unlocked).ReopenObservations files input before) :
    close.run = .ok () close.finished ∧
    close.finished.phase = .closed ∧ close.finished.files.image.1 = ⟨none, none, []⟩ ∧
    (⟨close.finished.files.image.2, close.finished.files.owners⟩ : LockedFileState FileImage) =
      SegmentedCleanReopenReport.released directory before ∧
    ∃ (layout : CanonicalKeeperLayout (SegmentedCleanReopenReport.released directory before).image before.history)
      (observed : MarkedRetryChunkReports files directory layout before.published)
      (admission : OpenAdmissionReports input directory observed.slot) (after : SegmentedWriterState),
      AdmittedCleanReopen (close.cleanUnlock unlocked) observed admission after := by
  have outcome := close.outcome_open (by simp)
  rw [unlocked] at outcome
  have files := close.finishedFiles ready.held
  refine ⟨outcome, rfl, ?_, ?_, ready.closeWithAdmission (close.cleanUnlock unlocked) observes⟩
  · rw [files]
  · rw [files]
    rfl

end Alvoki.Storage.DiskSession
