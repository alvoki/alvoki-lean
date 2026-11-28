import Alvoki.Experiments.L0.NativeScope

namespace ExperimentalL0.NativeCleanup
open NativeScope Lifecycle
open WalRecoverySlice

/-- The non-L0 primitives reached while closing the attached WAL. A frame
for data observations can cover these operations even when unlock reports
an error. This relation makes no physical claim about releasing a lock
after a failed unlock. -/
inductive Leaf : W → W → Prop where
  | mutexLock (m : Std.BaseMutex) (w) : Leaf w (m.lock w).state
  | mutexUnlock (m : Std.BaseMutex) (w) : Leaf w (m.unlock w).state
  | walClosed (cell : IO.Ref (Segmented.Native.Phase Segmented.Native.Store)) (w) :
      Leaf w ((cell.swap .closed : BaseIO _) w).state
  | takeChild (slot : IO.Ref (Option (Nat × SingleFile.Handle))) (w) :
      Leaf w ((slot.swap none : BaseIO _) w).state
  | childPhase (cell : IO.Ref (SingleFile.Phase IO.FS.Handle (SingleFile.AppendFiles IO.FS.Handle))) (w) :
      Leaf w ((cell.get : BaseIO _) w).state
  | childClosed (cell : IO.Ref (SingleFile.Phase IO.FS.Handle (SingleFile.AppendFiles IO.FS.Handle))) (w) :
      Leaf w ((cell.set .closed : BaseIO _) w).state
  | fileUnlock (fd : IO.FS.Handle) (w) : Leaf w (fd.unlock.toBaseIO w).state

def Frame (P : W → Prop) : Prop := ∀ {w t}, Leaf w t → P w → P t

theorem child_close (frame : Frame P) (h : SingleFile.Handle) (start : P w) :
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
    have freed := frame (.fileUnlock fd after) (frame (.childClosed cell got.state) framed)
    cases unlock : fd.unlock after with
    | error e t | ok x t =>
      have preserved : P t := by simpa only [EIO.toBaseIO, unlock] using freed
      dsimp only [after, got, locked] at unlock
      simp only [unlock]
      exact frame (.mutexUnlock mutex t) preserved

private theorem closeResult_frame (frame : Frame P) (child : SingleFile.Handle)
    (fd : IO.FS.Handle) (mutex : Std.BaseMutex) (start : P w) :
    P (Segmented.Native.returnedWorld (Segmented.Native.closeResult child fd mutex w)) := by
  have afterChild := child_close frame child start
  unfold Segmented.Native.closeResult
  cases ran : SingleFile.close child w with
  | error e t | ok x t =>
    have atUnlock : P t := by simpa only [EIO.toBaseIO, ran] using afterChild
    have freed := frame (.fileUnlock fd t) atUnlock
    cases unlock : fd.unlock t with
    | error err v | ok val v =>
      have preserved : P v := by simpa only [EIO.toBaseIO, unlock] using freed
      simpa only [unlock, Segmented.Native.returnedWorld] using frame (.mutexUnlock mutex v) preserved

/-- Frame the actual close using the registered child's identity from the
reached ready store. No callback-wide close frame is a premise. -/
theorem wal_close (heap : Segmented.Native.PhaseMemory) (frame : Frame P)
    (ready : heap.Ready wal session w) (start : P w) :
    Post (Segmented.Native.close wal) w (fun _ t => P t) (fun _ t => P t) := by
  obtain ⟨store, child, _, _, _, _, ran⟩ := Segmented.Native.close_ready_releases heap ready
  have body : P (Segmented.Native.returnedWorld (Segmented.Native.close wal w)) := by
    rw [ran]
    apply closeResult_frame frame
    apply frame (.takeChild store.active _)
    apply frame (.walClosed _ _)
    exact frame (.mutexLock _ w) start
  unfold Post
  cases outcome : Segmented.Native.close wal w <;> simpa only [outcome, Segmented.Native.returnedWorld] using body

/-- The outer descriptor has reached its actual unlock primitive. Success
and failure remain distinguishable after a child close error takes priority.
Further physical conclusions use the primitive report or a justified scoped
last-reference contract on this descriptor. -/
structure RootUnlock (P : W → Prop) (lock : IO.FS.Handle) (t : W) : Prop where
  observed : ∃ u, P u ∧ (lock.unlock.toBaseIO u).state = t
  kept : P t

/-- The recovery/callback producer supplies either the exact attached WAL
authority after the phase swap, or an empty phase. P describes the data and
trace observations to keep after custody is consumed. -/
theorem release_of_swap (heap : Segmented.Native.PhaseMemory) (frame : Frame P) (ref : Ref) (lock : IO.FS.Handle)
    (value : ((ref.swap .offline : BaseIO _) w).val = old)
    (swapped : P ((ref.swap .offline : BaseIO _) w).state)
    (registered : ∀ wal, old.wal = some wal →
      ∃ session, heap.Ready wal session ((ref.swap .offline : BaseIO _) w).state)
    (unlock : ∀ u, P u → Post lock.unlock u (fun _ t => ok t) err)
    (primary : ∀ e u, P u → Post lock.unlock u (fun _ t => err e t) (fun _ t => err e t)) :
    NativeScope.Release ref lock w ok err := by
  let taken := (ref.swap .offline : BaseIO _) w
  unfold NativeScope.Release
  dsimp only
  rw [value]
  cases attached : old.wal with
  | none => exact unlock taken.state swapped
  | some wal =>
    obtain ⟨session, ready⟩ := registered wal attached
    exact (wal_close heap frame ready swapped).weaken
      (fun _ t kept => unlock t kept) (fun e t kept => primary e t kept)

/-- The recovery/callback producer supplies either the exact attached WAL
authority after the phase swap, or an empty phase. P describes the data and
trace observations to keep after custody is consumed. -/
theorem release_rule (heap : Segmented.Native.PhaseMemory) (frame : Frame P) (ref : Ref) (lock : IO.FS.Handle)
    (owner : heap.holds ref old w)
    (swapped : P ((ref.swap .offline : BaseIO _) w).state)
    (registered : ∀ wal, old.wal = some wal →
      ∃ session, heap.Ready wal session ((ref.swap .offline : BaseIO _) w).state)
    (unlock : ∀ u, P u → Post lock.unlock u (fun _ t => ok t) err)
    (primary : ∀ e u, P u → Post lock.unlock u (fun _ t => err e t) (fun _ t => err e t)) :
    NativeScope.Release ref lock w ok err := by
  exact release_of_swap heap frame ref lock (heap.swap .offline owner) swapped registered unlock primary

/-- The recovery/callback producer supplies either the exact attached WAL
authority after the phase swap, or an empty phase. P describes the data and
trace observations to keep after custody is consumed. -/
theorem release (heap : Segmented.Native.PhaseMemory) (frame : Frame P) (ref : Ref) (lock : IO.FS.Handle)
    (owner : heap.holds ref old w)
    (swapped : P ((ref.swap .offline : BaseIO _) w).state)
    (registered : ∀ wal, old.wal = some wal →
      ∃ session, heap.Ready wal session ((ref.swap .offline : BaseIO _) w).state) :
    NativeScope.Release ref lock w (RootUnlock P lock) (fun _ => RootUnlock P lock) := by
  have unlock (u) (keeps : P u) :
      Post lock.unlock u (fun _ t => RootUnlock P lock t) (fun _ t => RootUnlock P lock t) := by
    have kept := frame (.fileUnlock lock u) keeps
    unfold Post
    cases ran : lock.unlock u with
    | ok x t | error e t =>
      exact ⟨⟨u, keeps, by simp only [EIO.toBaseIO, ran]⟩, by simpa only [EIO.toBaseIO, ran] using kept⟩
  exact release_rule heap frame ref lock owner swapped registered unlock (fun _ => unlock)

end ExperimentalL0.NativeCleanup
