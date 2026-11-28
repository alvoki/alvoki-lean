import Alvoki.Experiments.WAL.Segmented.Proofs.Writeback
import Alvoki.Experiments.WAL.Segmented.Proofs.NativeAppend

namespace WalRecoverySlice.Segmented.Native.AppendIO
open Model (Disk)

/-- Projection from the modeled disk to its concrete image. An unselected
segment (including a partially prepared successor) has no content obligation.
A settled background writeback is observed before selected files are compared. -/
def SelectedDisk (model actual : Disk) : Prop :=
  ∃ saved, Writebacks model saved ∧ actual.liveControl = saved.liveControl ∧
    actual.durableControl = saved.durableControl ∧
    ∀ c, saved.liveControl = some c ∨ saved.durableControl = some c →
      (∀ id, c.selects id →
        (id ∈ saved.liveNames → id ∈ actual.liveNames) ∧
        (id ∈ saved.durableNames → id ∈ actual.durableNames) ∧
        actual.segment id = saved.segment id) ∧ actual.cursor c.active = saved.cursor c.active

theorem SelectedDisk.refl (d : Disk) : SelectedDisk d d :=
  ⟨d, .nil, rfl, rfl, fun _ _ => ⟨fun _ _ => ⟨id, id, rfl⟩, rfl⟩⟩

/-- The history named by the returned model stage is preserved exactly
when projecting it onto the files selected by either physical CONTROL. -/
theorem SelectedDisk.readyLayout {control : Control} (rep : SelectedDisk model actual) (layout : ReadyLayout control history model)
    (left : model.liveControl = some control) (right : model.durableControl = some control) :
    ReadyLayout control history actual ∧ actual.liveControl = some control ∧ actual.durableControl = some control ∧
      actual.cursor control.active = model.cursor control.active := by
  obtain ⟨saved, steps, live, durable, get⟩ := rep
  have sameSource (i : Nat) (selected : control.selects i) :
      saved.segment i = model.segment i := by
    rcases Nat.eq_or_lt_of_le selected.2 with eq | lt
    · rw [eq]
      exact steps.settled layout.active.toSettled
    · exact steps.settled (layout.layout.sealed i selected lt)
  have cursor (i : Nat) : saved.cursor i = model.cursor i := by
    clear live durable get sameSource
    induction steps <;> first | rfl | assumption
  have usedLive := steps.live.trans left
  obtain ⟨files, pos⟩ := get control (.inl usedLive)
  have names (i : Nat) (sel : control.selects i) :
      i ∈ saved.liveNames ∧ i ∈ saved.durableNames := by
    have old := layout.layout.names i sel
    clear live durable usedLive files pos sameSource cursor get
    induction steps <;> first | exact old | assumption
  have valid := layout.frame (after := actual) (fun i sel =>
      ⟨(files i sel).1 (names i sel).1, (files i sel).2.1 (names i sel).2⟩)
    (fun i sel => (files i sel).2.2.trans (sameSource i sel)) (pos.trans (cursor _))
  exact ⟨valid,live.trans usedLive,durable.trans (steps.durable.trans right),pos.trans (cursor _)⟩

theorem SelectedDisk.installed (rep : SelectedDisk model actual) (installed : Installed next model) :
    Installed next actual := by
  obtain ⟨history,shape,layout,l,d⟩ := installed
  obtain ⟨valid,left,right,_⟩ := rep.readyLayout layout l d
  exact ⟨history,shape,valid,left,right⟩

/-- The exact same stored child phase is usable with the physical disk,
including after writebacks to previously retired segments. -/
theorem SelectedDisk.appendReady (rep : SelectedDisk state.1.disk actual)
    (ready : Model.AppendReady session state) :
    Model.AppendReady session ({state.1 with disk := actual}, state.2) := by
  obtain ⟨history,shape,layout,l,d,phase⟩ := ready
  obtain ⟨valid,left,right,cursor⟩ := rep.readyLayout layout l d
  exact ⟨history,shape,valid,left,right,cursor ▸ phase⟩

theorem SelectedDisk.recoverable (rep : SelectedDisk model actual)
    (prior : Recoverable known request model) : Recoverable known request actual := by
  obtain ⟨saved, steps, live, durable, get⟩ := rep
  have prior := steps.recoverable prior
  have transfer (c) (selected : saved.liveControl = some c ∨ saved.durableControl = some c)
      (choice : RecoveryChoice known request c saved) : RecoveryChoice known request c actual := by
    obtain ⟨files, _⟩ := get c selected
    obtain ⟨history, pending, readable, permitted⟩ := choice
    refine ⟨history, pending, readable.frame ?_ (fun i h => (files i h).2.2), permitted⟩
    intro i chosen
    have names := readable.layout.names i chosen
    exact ⟨(files i chosen).1 names.1, (files i chosen).2.1 names.2⟩
  obtain ⟨c, l, x⟩ := prior.live
  obtain ⟨d, r, y⟩ := prior.durable
  exact ⟨⟨c, live.trans l, transfer c (.inl l) x⟩, ⟨d, durable.trans r, transfer d (.inr r) y⟩⟩

end WalRecoverySlice.Segmented.Native.AppendIO
