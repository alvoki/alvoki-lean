import Alvoki.Experiments.WAL.Segmented.Proofs.ChildAuthority
import Alvoki.Experiments.WAL.Segmented.Proofs.AppendCustody
import Alvoki.Experiments.WAL.Segmented.Proofs.AppendDiskIO
import Alvoki.Experiments.WAL.Segmented.Proofs.AppendSchedule

namespace WalRecoverySlice.Segmented.Native.AppendIO
open Alvoki.NativePost (W)
open Model (Disk AppendReady)

theorem ChildSource.openedChild (s : ChildSource dir p h fd) : OpenedChild dir h fd := by
  cases s with
  | reopened orig =>
    obtain ⟨a, b, opened, lock⟩ := orig
    exact ⟨a, b, lock, .inl opened⟩
  | created lock ran => exact ⟨_, _, lock, .inr ⟨_, ran⟩⟩

/-- Authority for another public operation. Store and root lock survive
rotation; the session, slot and owned description come from the last
installation. The physical disk is the image at the caller's own world. -/
def Active {disk : W → Disk} (mem : ChildMemory disk) (heap : PhaseMemory) (wal : Handle)
    (reg : Registration) (w : W) : Prop :=
  RootLockAt reg.store.root reg.store.lock ∧ heap.Registered wal reg w ∧
    ∃ (a : ChildAuthority mem (segmentPath reg.store.root reg.session.control.active)
        reg.session.control.active reg.session.control.policy reg.child) (phase : SingleFile.AppendPhase),
      a.Live w phase ∧ AppendReady reg.session (⟨disk w, 0, some reg.session.control.active⟩, phase)

theorem Active.custody {disk : W → Disk} {mem : ChildMemory disk} {reg : Registration}
    (entry : Active mem heap wal reg w) :
    Custody heap wal reg.store (some (reg.session.control.active, reg.child)) w := by
  obtain ⟨root, held, a, phase, live, ready⟩ := entry
  obtain ⟨cell, mutex, parts⟩ := wal.parts
  obtain ⟨rfl, rfl⟩ := parts
  exact ⟨root, ⟨a.fd, a.source.openedChild⟩, _, _, ⟨rfl,rfl⟩, held.1, .inr ⟨_, held.2.1⟩, held.2.2⟩

theorem Active.ofRecovered {disk : W → Disk} {mem : ChildMemory disk} {reg : Registration}
    (held : heap.Registered wal reg w) (lock : RootLockAt reg.store.root reg.store.lock)
    (recovered : RecoveredChild disk (mem.Owns reg.store.root) reg.session reg.child w) :
    Active mem heap wal reg w := by
  obtain ⟨history, shape, owned, layout, left, right⟩ := recovered
  obtain ⟨a, live⟩ := ChildAuthority.opened owned layout.active
  refine ⟨lock, held, a, _, live, history, shape, layout, left, right, ?_⟩
  rw [layout.active.position]

end WalRecoverySlice.Segmented.Native.AppendIO
