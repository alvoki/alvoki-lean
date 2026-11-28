import Alvoki.Experiments.WAL.Segmented.Proofs.SuccessorIO
import Alvoki.Experiments.WAL.Segmented.Proofs.AppendDiskIO

namespace WalRecoverySlice.Segmented.Native.PrepareIO
open Model System Alvoki.NativePost
variable {id : Nat}

/-- A fully initialized child remains byte-for-byte identical through an
arbitrary sequence of background file writebacks, before it is selectable. -/
theorem PreparedFile.writebacks (file : PreparedFile disk id w) (wb : Writebacks (disk w) (disk t)) :
    PreparedFile disk id t := by
  have stable : ∀ {reached}, Writebacks (disk w) reached →
      id ∈ reached.liveNames ∧ reached.segment id = Persistence.freshImage ∧ reached.cursor id = {} := by
    intro reached steps
    induction steps with
    | nil => exact ⟨file.named, file.image, file.cursor⟩
    | next prior i target ih =>
      refine ⟨ih.1, ?_, ih.2.2⟩
      by_cases eq : id = i
      · simp only [Disk.writeback, eq, ite_true]
        subst i
        rw [ih.2.1]
        cases target <;> rfl
      · simpa [Disk.writeback, eq] using ih.2.1
  obtain ⟨n, f, c⟩ := stable wb
  exact ⟨n, f, c⟩

/-- Local persistence of the parent-directory name makes the prepared
empty child an admissible new active segment. -/
theorem PreparedFile.namedChild (file : PreparedFile disk id w) (barrier : id ∈ (disk w).durableNames) (p : Policy) :
    (id ∈ (disk w).liveNames ∧ id ∈ (disk w).durableNames) ∧
      Child.Installed p ((disk w).segment id) ((disk w).cursor id) [] := by
  refine ⟨⟨file.named, barrier⟩, ?_⟩
  rw [file.image, file.cursor]
  exact ⟨⟨Persistence.fresh_ready p, rfl⟩, rfl⟩

theorem Successor.healthy (steps : Successor s p id removal Model.healthy {} origin initial R disk mem)
    (root : HealthyRoot removal) (linux : Platform.isWindows = false) :
    ∃ h t phase u, s.prepareChild p id origin = .ok h t ∧
      (prepareNativeChild s.root removal (fun step => Model.healthy.prepare step id) {} p id).run initial =
        .ok (.ok phase) u ∧ CreatedChild mem s id p h phase t ∧ R t u ∧ PreparedFile disk id t := by
  obtain ⟨phase, u, model⟩ := prepareNativeChild_healthy s.root removal root p id initial linux
  have result := steps.prepare linux
  unfold AppendIO.At at result
  change (prepareNativeChild s.root removal (fun step => Model.healthy.prepare step id) {} p id).run initial = _ at model
  rw [model] at result
  cases run : s.prepareChild p id origin <;> rw [run] at result
  case error => contradiction
  case ok h t => exact ⟨h, t, phase, u, rfl, model, result⟩

private theorem writebacks_data (wb : Writebacks d saved) (i : Nat) :
    (saved.segment i).data.live = (d.segment i).data.live := by
  induction wb with
  | nil => rfl
  | next prior j f ih =>
    by_cases hit : i = j
    · subst j
      cases f <;> simpa [Disk.writeback, Persistence.WalFile.settle] using ih
    · simpa [Disk.writeback, hit] using ih

/-- A selected-only precondition admits changes to an unpublished child,
even when its directory name exists and the cursor is identical. Atomic
rename exposes the discrepancy in the actual payload bytes. -/
theorem selectedOnly_counterexample :
    ∃ old newControl : Control, ∃ model actual : Disk,
      model.liveControl = some old ∧ model.durableControl = some old ∧
      newControl.active = old.active + 1 ∧ newControl.active ∈ actual.liveNames ∧
      actual.cursor newControl.active = model.cursor newControl.active ∧
      AppendIO.SelectedDisk model actual ∧
      ¬ AppendIO.SelectedDisk (model.rename newControl false) (actual.rename newControl false) := by
  let old : Control := ⟨.boundary, 1, 0, 0⟩
  let newControl : Control := {old with active := 1}
  let model : Disk := {liveControl := some old, durableControl := some old, liveNames := [0, 1], durableNames := [0, 1]}
  let altered : Persistence.Image := {Persistence.freshImage with data := ⟨[17], [17]⟩}
  let actual := model.setSegment 1 altered {}
  refine ⟨old, newControl, model, actual, rfl, rfl, rfl, by decide, rfl, ?_, ?_⟩
  · refine ⟨model, .nil, rfl, rfl, ?_⟩
    rintro c (h | h) <;> cases h <;> refine ⟨?_, rfl⟩ <;>
      intro i selected <;> have le : i ≤ 0 := selected.2 <;> have zero : i = 0 := by omega
    all_goals subst i; exact ⟨_root_.id, _root_.id, rfl⟩
  · rintro ⟨saved, wb, _, _, rep⟩
    have selected := (rep newControl (.inl wb.live)).1 1 newControl.selectsActive
    have raw := congrArg (fun image : Persistence.Image => image.data.live) selected.2.2
    have bad := raw.trans (writebacks_data wb 1)
    change ([17] : Bytes) = [] at bad
    contradiction

end WalRecoverySlice.Segmented.Native.PrepareIO
