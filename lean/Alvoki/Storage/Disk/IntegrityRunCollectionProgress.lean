import Alvoki.Storage.Disk.IntegrityDatabaseTrace

namespace Alvoki.WAL.Boundary
open Storage CheckpointPublication

/-- The older, unheld addresses returned by the pass's canonical inventory. -/
def IntegrityRunCollectionReports.selected {directory : DiskDirectory} {state : ObservedMarkedState}
    {before : RunUnlinkImage} (reports : IntegrityRunCollectionReports directory state before) : List RunAddress :=
  selectRunFiles directory (reports.observed.map (fun _ => state.generation))
    (retainRunGeneration state.generation reports.held) reports.inventory.kindAt reports.inventory.names

/-- Given a complete inventory of visible eligible regular runs and
successful callbacks, one same-session pass durably removes all eligible
addresses. An address already hidden by a previous unlink is settled by
the final sync, even if no address remains to unlink. Current and newer
generations and explicit holds keep their known bytes in the exact result. -/
theorem IntegrityRunCollectionReports.completePass {directory : DiskDirectory} {state : ObservedMarkedState}
    {before : RunUnlinkImage} (reports : IntegrityRunCollectionReports directory state before)
    (valid : state.VersionedReady) (integrity : state.HasIntegrityManifest)
    (complete : ∀ generation index bytes, before.visible generation index = some bytes →
      generation < state.generation → generation ∉ reports.held →
      renderRunFileName generation index ∈ reports.inventory.names ∧
        reports.inventory.kindAt (directory.file (.run generation index)) = .ok .file)
    (healthy : RunUnlinkScheduleHealthy before (RunCollection.steps reports.selected) reports.perform) :
    let after := before.finishPass reports.selected
    reports.run = .ok () after ∧
      (∀ generation index, generation < state.generation → generation ∉ reports.held →
        after.DurablyAbsent (generation, index)) ∧
      ∀ generation index bytes, state.generation ≤ generation ∨ generation ∈ reports.held →
        before.guaranteed generation index = some bytes → after.guaranteed generation index = some bytes := by
  have observed := reports.manifest.resultVisible (directory.file .manifest) reports.manifestRead
  have checked : validateIntegrityRunCollectionGeneration state.generation reports.observed =
      .ok (reports.observed.map (fun _ => state.generation)) := by
    rw [← observed]
    exact valid.collectionPreflight integrity
  have matching := (validateObservedRunGeneration_ok_iff.mp checked).2
  have ran : reports.run = RunCollection.run reports.selected reports.perform before := by
    unfold run LockedRunInventory.runIntegrityCollection
    rw [checked]
    simp only [pure_bind, selectRunFilesWith_pure, selected]
  refine ⟨ran.trans (runUnlinkSchedule_success _ before reports.perform reports.effects healthy), ?_, ?_⟩
  · intro generation index older unheld
    cases visible : before.visible generation index with
    | none =>
      simpa [RunUnlinkImage.DurablyAbsent, visible] using
        before.finishPass_binding reports.selected (generation, index)
    | some bytes =>
      obtain ⟨listed, regular⟩ := complete generation index bytes visible older unheld
      exact RunUnlinkImage.finishPass_absent
        ((reports.inventory.selectOlderRunsAt_iff reports.held matching).mpr ⟨listed, older, unheld, regular⟩)
  · intro generation index bytes retained known
    apply (RunUnlinkRetry.start (approved := reports.selected) before).finishPass.keepsKnown
      (name := (generation, index)) known
    intro chosen
    obtain ⟨_, older, unheld, _⟩ :=
      (reports.inventory.selectOlderRunsAt_iff reports.held matching).mp chosen
    exact retained.elim (fun newer => UInt64.not_lt.mpr newer older) unheld

end Alvoki.WAL.Boundary
