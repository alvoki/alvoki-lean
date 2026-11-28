import Alvoki.Experiments.WAL.Segmented.Native

namespace WalRecoverySlice.Segmented.Native.AppendIO
open System

/-- An open or a rotation create owns the lock acquired by that same call. -/
def OpenedChild (dir : FilePath) (h : SingleFile.Handle) (fd : IO.FS.Handle) : Prop :=
  ∃ start finish, RootLockFrom dir fd start ∧
    (SingleFile.openExisting dir start = .ok h finish ∨
      ∃ policy, SingleFile.create dir policy start = .ok h finish)

def SlotLocks (store : Store) (slot : Option (Nat × SingleFile.Handle)) : Prop :=
  match slot with
  | none => True
  | some (id, h) => ∃ fd, OpenedChild (segmentPath store.root id) h fd

/-- The failure may have poisoned the phase and taken the old child already.
The slot records the precise handle left for cleanup, if any. -/
def Custody (heap : PhaseMemory) (wal : Handle) (store : Store)
    (slot : Option (Nat × SingleFile.Handle)) (w : Void IO.RealWorld) : Prop :=
  RootLockAt store.root store.lock ∧ SlotLocks store slot ∧
    ∃ cell mutex, wal.Parts cell mutex ∧ heap.separate cell store.active ∧
      (heap.holds cell (.poisoned store) w ∨ ∃ s, heap.holds cell (.ready store s) w) ∧
      heap.holds store.active slot w

theorem Custody.ofRegistered {heap : PhaseMemory} {reg : Registration}
    (ready : heap.Registered wal reg w) (locks : LocksFrom reg) :
    Custody heap wal reg.store (some (reg.session.control.active, reg.child)) w := by
  obtain ⟨cell, mutex, parts⟩ := wal.parts
  obtain ⟨fd, a, b, opened, granted⟩ := locks.2
  have slot : SlotLocks reg.store (some (reg.session.control.active, reg.child)) :=
    ⟨fd, a, b, granted, .inl opened⟩
  refine ⟨locks.1, slot, cell, mutex, parts, ?_, .inr ⟨reg.session, ?_⟩, ready.2.2⟩
  all_goals obtain ⟨rfl, rfl⟩ := parts
  · exact ready.1
  · exact ready.2.1

end WalRecoverySlice.Segmented.Native.AppendIO
