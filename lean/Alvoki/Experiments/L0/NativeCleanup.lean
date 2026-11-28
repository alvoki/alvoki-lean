import Alvoki.Experiments.L0.NativeScope

namespace ExperimentalL0.NativeCleanup
open NativeScope Lifecycle
open WalRecoverySlice

/-- The non-L0 primitives reached while closing the attached WAL. A frame
for data observations can cover these operations even when unlock reports
an error. This relation makes no physical claim about releasing a lock
after a failed unlock. -/
inductive Leaf (issued : IO.FS.Handle → W → Prop) : W → W → Prop where
  | mutexLock (m : Std.BaseMutex) (w) : Leaf issued w (m.lock w).state
  | mutexUnlock (m : Std.BaseMutex) (w) : Leaf issued w (m.unlock w).state
  | walClosed (cell : IO.Ref (Segmented.Native.Phase Segmented.Native.Store)) (w) :
      Leaf issued w ((cell.swap .closed : BaseIO _) w).state
  | takeChild (slot : IO.Ref (Option (Nat × SingleFile.Handle))) (w) :
      Leaf issued w ((slot.swap none : BaseIO _) w).state
  | childPhase (cell : IO.Ref (SingleFile.Phase IO.FS.Handle (SingleFile.AppendFiles IO.FS.Handle))) (w) :
      Leaf issued w ((cell.get : BaseIO _) w).state
  | childClosed (cell : IO.Ref (SingleFile.Phase IO.FS.Handle (SingleFile.AppendFiles IO.FS.Handle))) (w) :
      Leaf issued w ((cell.set .closed : BaseIO _) w).state
  | fileUnlock (fd : IO.FS.Handle) (w) (site : issued fd w) : Leaf issued w (fd.unlock.toBaseIO w).state

def Frame (issued : IO.FS.Handle → W → Prop) (P : W → Prop) : Prop := ∀ {w t}, Leaf issued w t → P w → P t

theorem Leaf.map (h : ∀ fd w, issued fd w → allowed fd w) (step : Leaf issued s t) :
    Leaf allowed s t := by
  cases step with
  | mutexLock m w => exact .mutexLock m _
  | mutexUnlock m w => exact .mutexUnlock m _
  | walClosed cell w => exact .walClosed cell _
  | takeChild slot w => exact .takeChild slot _
  | childPhase cell w => exact .childPhase cell _
  | childClosed cell w => exact .childClosed cell _
  | fileUnlock fd w site => exact .fileUnlock fd _ (h fd _ site)

/-- A child unlock is issued only for the lock actually read from its
registered phase, immediately after changing that cell to closed. -/
def ChildIssued (h : SingleFile.Handle) (w : W) (fd : IO.FS.Handle) (t : W) : Prop :=
  ∃ cell mutex, h.Binds cell mutex ∧
    let got := (cell.get : BaseIO _) (mutex.lock w).state
    t = ((cell.set .closed : BaseIO Unit) got.state).state ∧
      match got.val with
      | .closed => False
      | .active held _ _ _ | .poisoned held => fd = held

theorem child_close (frame : Frame issued P) (h : SingleFile.Handle)
    (childSite : ∀ fd t, ChildIssued h w fd t → issued fd t) (start : P w) :
    P ((SingleFile.close h).toBaseIO w).state := by
  obtain ⟨cell, mutex, binds⟩ := h.bindings
  rw [EIO.toBaseIO, SingleFile.close_run binds]
  let locked := (mutex.lock w).state
  let got := (cell.get : BaseIO _) locked
  have framed := frame (.childPhase cell locked) (frame (.mutexLock mutex w) start)
  change P got.state at framed
  dsimp only
  generalize hp : ((cell.get : BaseIO _) (mutex.lock w).state).val = phase
  cases phase with
  | closed => exact frame (.mutexUnlock mutex got.state) framed
  | active fd _ _ _ | poisoned fd =>
    let after := ((cell.set .closed : BaseIO Unit) got.state).state
    have site : ChildIssued h w fd after := by
      refine ⟨cell, mutex, binds, rfl, ?_⟩
      rw [hp]
    have freed := frame (.fileUnlock fd after (childSite fd after site)) (frame (.childClosed cell got.state) framed)
    cases unlock : fd.unlock after with
    | error e t | ok x t =>
      have preserved : P t := by simpa only [EIO.toBaseIO, unlock] using freed
      dsimp only [after, got, locked] at unlock
      simp only [unlock]
      exact frame (.mutexUnlock mutex t) preserved

private theorem closeResult_frame (frame : Frame issued P) (child : SingleFile.Handle)
    (fd : IO.FS.Handle) (mutex : Std.BaseMutex)
    (childSite : ∀ f t, ChildIssued child w f t → issued f t)
    (storeSite : issued fd ((SingleFile.close child).toBaseIO w).state) (start : P w) :
    P (Segmented.Native.returnedWorld (Segmented.Native.closeResult child fd mutex w)) := by
  have afterChild := child_close frame child childSite start
  unfold Segmented.Native.closeResult
  cases ran : SingleFile.close child w with
  | error e t | ok x t =>
    have atUnlock : P t := by simpa only [EIO.toBaseIO, ran] using afterChild
    have freed := frame (.fileUnlock fd t (by simpa only [EIO.toBaseIO, ran] using storeSite)) atUnlock
    cases unlock : fd.unlock t with
    | error err v | ok val v =>
      have preserved : P v := by simpa only [EIO.toBaseIO, unlock] using freed
      simpa only [unlock, Segmented.Native.returnedWorld] using frame (.mutexUnlock mutex v) preserved

/-- Frame the actual close using the registered child's identity from the
reached ready store. No callback-wide close frame is a premise. -/
theorem wal_close (heap : Segmented.Native.PhaseMemory) (frame : Frame (Segmented.Native.CloseSites ChildIssued heap wal session w) P)
    (ready : heap.Ready wal session w) (start : P w) :
    Post (Segmented.Native.close wal) w (fun _ t => P t) (fun _ t => P t) := by
  obtain ⟨store, child, phase, slot, _, _, ran⟩ := Segmented.Native.close_ready_releases heap ready
  have body : P (Segmented.Native.returnedWorld (Segmented.Native.close wal w)) := by
    rw [ran]
    apply closeResult_frame frame
    · exact fun f t site => ⟨store, child, phase, slot, .inl site⟩
    · exact ⟨store, child, phase, slot, .inr ⟨rfl, rfl⟩⟩
    apply frame (.takeChild store.active _)
    apply frame (.walClosed _ _)
    exact frame (.mutexLock _ w) start
  unfold Post
  cases outcome : Segmented.Native.close wal w <;> simpa only [outcome, Segmented.Native.returnedWorld] using body

end ExperimentalL0.NativeCleanup
