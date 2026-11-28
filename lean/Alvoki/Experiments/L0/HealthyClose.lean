import Alvoki.Experiments.L0.NativeCleanup

namespace ExperimentalL0.HealthyRootAcquisition

open NativeScope WalRecoverySlice

/-- Healthy reports for the actual input of close. The registered child's
phase read under its mutex returns a live or poisoned description. Each
descriptor unlock that is actually issued reports success. -/
structure Unlocks (heap : Segmented.Native.PhaseMemory) (wal : Segmented.Native.Handle)
    (session : Segmented.Session) (w : W) : Prop where
  live : ∀ h u, Segmented.Native.CloseChildAt heap wal session w h u →
    ∀ ref mutex, h.Binds ref mutex → ((ref.get : BaseIO _) (mutex.lock u).state).val ≠ .closed
  unlock : ∀ fd t, Segmented.Native.CloseSites NativeCleanup.ChildIssued heap wal session w fd t →
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

private theorem finishClose (healthy : Unlocks heap wal session w) {mutex : Std.BaseMutex}
    (entered : Segmented.Native.CloseChildAt heap wal session w child start)
    (childSite : ∀ fd t, NativeCleanup.ChildIssued child start fd t →
      Segmented.Native.CloseSites NativeCleanup.ChildIssued heap wal session w fd t)
    (storeSite : Segmented.Native.CloseSites NativeCleanup.ChildIssued heap wal session w
      rootLock ((SingleFile.close child).toBaseIO start).state) :
    ∃ t, Segmented.Native.closeResult child rootLock mutex start = .ok () t := by
  obtain ⟨after, closed⟩ := childClose child (healthy.live child start entered)
    (fun fd t site => healthy.unlock fd t (childSite fd t site))
  obtain ⟨end_, reset⟩ := healthy.unlock _ _ (by simpa only [EIO.toBaseIO, closed] using storeSite)
  exact ⟨(mutex.unlock end_).state, by simp only [Segmented.Native.closeResult, closed, reset]⟩

/-- A healthy close follows the registered slot down to its concrete
single-file descriptor before releasing the segmented directory lock. -/
theorem walClose (ready : heap.Ready wal session w) (healthy : Unlocks heap wal session w) :
    ∃ t, Segmented.Native.close wal w = .ok () t := by
  obtain ⟨store, child, phase, slot, _, _, ran⟩ := Segmented.Native.close_ready_releases heap ready
  rw [ran]
  apply finishClose healthy
  · exact ⟨store, phase, slot, rfl⟩
  · exact fun fd t site => ⟨store, child, phase, slot, .inl site⟩
  · exact ⟨store, child, phase, slot, .inr ⟨rfl, rfl⟩⟩

end ExperimentalL0.HealthyRootAcquisition
