import Alvoki.Storage.Disk.Proofs.Collection.IntegrityRunCollectionProgress

namespace Alvoki.Storage.CheckpointPublication

/-- Account for the present bindings in a finite run-name catalog. Use
`ByteArray.size` for logical payload bytes and `fun _ => 1` for name count. -/
noncomputable def RunFiles.namedRunTotal (files : RunFiles) (measure : ByteArray → Nat)
    (catalog : List RunAddress) : Nat :=
  (catalog.map (fun (generation, index) => ((files generation index).map measure).getD 0)).sum

theorem RunFiles.namedRunTotal_partition {before after : RunFiles} (keep : RunAddress → Bool)
    (binding : ∀ generation index, after generation index =
      if keep (generation, index) then before generation index else none)
    (measure : ByteArray → Nat) (catalog : List RunAddress) :
    after.namedRunTotal measure catalog +
      before.namedRunTotal measure (catalog.filter (fun address => !keep address)) =
      before.namedRunTotal measure catalog := by
  induction catalog with
  | nil => rfl
  | cons address rest ih =>
    obtain ⟨generation, index⟩ := address
    cases kept : keep (generation, index) <;>
      simp [namedRunTotal, binding, kept] at ih ⊢ <;> omega

end Alvoki.Storage.CheckpointPublication

namespace Alvoki.WAL.Boundary

open Storage CheckpointPublication

/-- Count the named run space after an observed successful obsolete-run
collection. The locked inventory contains every initial run name and each
eligible name has a successful regular-file lookup. The resulting visible
map and its sole crash image retain exactly the current, newer, and held
bindings. Counts and payload totals refer to names, including separate
names for hard links. Inode lifetime and filesystem block use are outside
this namespace model. -/
theorem IntegrityRunCollectionReports.completePass_namedRunSpace
    {directory : DiskDirectory} {state : ObservedMarkedState} {before after : RunUnlinkImage}
    (reports : IntegrityRunCollectionReports directory state before)
    (valid : state.VersionedReady) (integrity : state.HasIntegrityManifest)
    (ran : reports.run = .ok () after)
    (unique : reports.inventory.names.Nodup)
    (complete : ∀ generation index bytes, before.visible generation index = some bytes →
      renderRunFileName generation index ∈ reports.inventory.names)
    (regular : ∀ generation index bytes, before.visible generation index = some bytes →
      generation < state.generation → generation ∉ reports.held →
      reports.inventory.kindAt (directory.file (.run generation index)) = .ok .file) :
    let catalog := reports.inventory.names.filterMap parseRunFileName
    let keep := retainRunGeneration state.generation reports.held
    catalog.Nodup ∧
      (∀ generation index bytes, before.visible generation index = some bytes → (generation, index) ∈ catalog) ∧
      after.crashImages = [after.visible] ∧
      (∀ generation index, after.visible generation index =
        if keep generation then before.visible generation index else none) ∧
      ∀ measure, after.visible.namedRunTotal measure catalog +
        before.visible.namedRunTotal measure (catalog.filter (fun address => !keep address.1)) =
        before.visible.namedRunTotal measure catalog := by
  let catalog := reports.inventory.names.filterMap parseRunFileName
  let keep := retainRunGeneration state.generation reports.held
  have uniqueNames : catalog.Nodup := by
    apply unique.filterMap parseRunFileName
    intro left right different address parsed next other same
    obtain ⟨generation, index⟩ := address
    subst next
    exact different ((parseRunFileName_eq_some_iff.mp parsed).trans (parseRunFileName_eq_some_iff.mp other).symm)
  have covers generation index bytes (present : before.visible generation index = some bytes) :
      (generation, index) ∈ catalog :=
    List.mem_filterMap.mpr ⟨_, complete generation index bytes present, parseRunFileName_render ..⟩
  have observed := reports.manifest.resultVisible (directory.file .manifest) reports.manifestRead
  have checked : validateIntegrityRunCollectionGeneration state.generation reports.observed =
      .ok (reports.observed.map (fun _ => state.generation)) := by
    rw [← observed]
    exact valid.collectionPreflight integrity
  have matching := (validateObservedRunGeneration_ok_iff.mp checked).2
  have dispatched : RunCollection.run reports.selected reports.perform before = .ok () after := by
    unfold IntegrityRunCollectionReports.run LockedRunInventory.runIntegrityCollection at ran
    rw [checked] at ran
    simpa only [pure_bind, selectRunFilesWith_pure, IntegrityRunCollectionReports.selected] using ran
  have finished := runUnlinkSchedule_outcome reports.selected before reports.perform reports.effects
  rw [dispatched] at finished
  subst after
  have binding generation index : (before.finishPass reports.selected).visible generation index =
      if keep generation then before.visible generation index else none := by
    have final := (before.finishPass_binding reports.selected (generation, index)).1
    rw [final]
    cases eligible : keep generation with
    | true =>
      have unselected : (generation, index) ∉ reports.selected := by
        intro member
        obtain ⟨_, older, unheld, _⟩ := (reports.inventory.selectOlderRunsAt_iff reports.held matching).mp member
        have removed := retainRunGeneration_false_iff.mpr ⟨older, unheld⟩
        rw [show retainRunGeneration state.generation reports.held generation = true from eligible] at removed
        contradiction
      simp [unselected]
    | false =>
      rcases initial : before.visible generation index with _ | bytes
      · split <;> rfl
      · obtain ⟨older, unheld⟩ := retainRunGeneration_false_iff.mp eligible
        have selected : (generation, index) ∈ reports.selected :=
          (reports.inventory.selectOlderRunsAt_iff reports.held matching).mpr
            ⟨complete generation index bytes initial, older, unheld, regular generation index bytes initial older unheld⟩
        simp [selected]
  exact ⟨uniqueNames, covers, rfl, binding, fun measure =>
    RunFiles.namedRunTotal_partition (fun address => keep address.1) binding measure catalog⟩

end Alvoki.WAL.Boundary
