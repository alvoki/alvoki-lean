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

theorem SelectedDisk.installed (rep : SelectedDisk model actual) (installed : Installed next model) :
    Installed next actual := by
  obtain ⟨saved, steps, live, durable, get⟩ := rep
  obtain ⟨history, shape, ready, left, right⟩ := steps.installed installed
  have ⟨files, cursor⟩ := get next.control (.inl left)
  refine ⟨history, shape, ready.frame ?_ (fun i h => (files i h).2.2) cursor,
    live.trans left, durable.trans right⟩
  intro i chosen
  have names := ready.layout.names i chosen
  exact ⟨(files i chosen).1 names.1, (files i chosen).2.1 names.2⟩

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
