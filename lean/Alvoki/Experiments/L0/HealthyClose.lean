import Alvoki.Experiments.L0.NativeCleanup

namespace ExperimentalL0.HealthyRootAcquisition

open NativeScope WalRecoverySlice

/-- Healthy reports for the actual input of close. The registered child's
phase read under its mutex returns a live or poisoned description. Each
descriptor unlock that is actually issued reports success. -/
structure Unlocks (wal : Segmented.Native.Handle)
    (reg : Segmented.Native.Registration) (w : W) : Prop where
  live : ∀ ref mutex, reg.child.Binds ref mutex →
    ((ref.get : BaseIO _) (mutex.lock (Segmented.Native.detachedWorld wal reg w)).state).val ≠ .closed
  unlock : ∀ fd t, Segmented.Native.CloseSites NativeCleanup.ChildIssued wal reg w fd t →
    ∃ end_, fd.unlock t = .ok () end_

private theorem childClose (h : SingleFile.Handle)
    (live : ∀ ref mutex, h.Binds ref mutex → ((ref.get : BaseIO _) (mutex.lock w).state).val ≠ .closed)
    (unlock : ∀ fd t, NativeCleanup.ChildIssued h w fd t → ∃ end_, fd.unlock t = .ok () end_) :
    ∃ t, SingleFile.close h w = .ok () t := by
  obtain ⟨cell, mutex, binds⟩ := h.bindings
  have nonempty := live cell mutex binds
  rw [SingleFile.close_run binds]
  dsimp only
  generalize hp : ((cell.get : BaseIO _) (mutex.lock w).state).val = phase
  cases phase with
  | closed => exact False.elim (nonempty hp)
  | active fd _ _ _ | poisoned fd =>
    let got := (cell.get : BaseIO _) (mutex.lock w).state
    let after := ((cell.set .closed : BaseIO Unit) got.state).state
    have site : NativeCleanup.ChildIssued h w fd after := by
      refine ⟨cell, mutex, binds, rfl, ?_⟩
      rw [hp]
    obtain ⟨t, ran⟩ := unlock fd after site
    dsimp only [after, got] at ran
    simp only [ran]
    exact ⟨_, rfl⟩

/-- A healthy close uses precisely the registration installed by the WAL
open, from taking its active child through the store lock unlock. -/
theorem walClose {heap : Segmented.Native.PhaseMemory} {reg : Segmented.Native.Registration}
    (held : heap.Registered wal reg w) (healthy : Unlocks wal reg w) :
    ∃ t, Segmented.Native.close wal w = .ok () t := by
  obtain ⟨_, _, ran⟩ := Segmented.Native.close_registered heap held
  rw [ran]
  obtain ⟨after, closed⟩ := childClose reg.child
    healthy.live
    (fun fd t site => healthy.unlock fd t (.inl site))
  have storeSite := healthy.unlock reg.store.lock _ (.inr ⟨rfl, rfl⟩)
  simp only [EIO.toBaseIO, closed] at storeSite
  obtain ⟨end_, reset⟩ := storeSite
  dsimp only [Segmented.Native.detachedWorld] at closed reset
  simp only [Segmented.Native.closeResult, closed, reset]
  exact ⟨_, rfl⟩

end ExperimentalL0.HealthyRootAcquisition
