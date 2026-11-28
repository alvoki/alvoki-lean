import Alvoki.Experiments.L0.NativeScope
import Alvoki.Experiments.L0.NativeRead

namespace ExperimentalL0.NativeRead
open System Lifecycle

/-- The swap consumes the known owner of this cell. Other selected files
may write back while the reference is updated. -/
def RefSwap (physical : W → Footprint inode) (root : FilePath) (lock : IO.FS.Handle)
    (ref : IO.Ref (Phase Wal)) (wal : Wal) (tables : Catalog) : Prop :=
  ∀ w, Owned (physical w) root lock ref → ∀ next,
    let changed := (ref.swap next : BaseIO (Phase Wal)) w
    changed.val = (physical w).phase ∧ FrameTo physical root wal tables w changed.state next

/-- Replay the phase read and swap of concrete publication. The callback
receives the installed session on the world returned by that swap. -/
theorem publishOnline (prepared : SessionAt physical root lock ref wal session image history start (.recovering wal))
    (read : RefRead physical root lock ref wal image.tables)
    (swap : RefSwap physical root lock ref wal image.tables)
    (use : IO α)
    (callback : ∀ entered, Online physical root lock ref wal session image history entered →
      NativeScope.Callback ref lock use entered ok err) :
    NativeScope.Publish ref lock use session start ok err := by
  obtain ⟨t, readAt, frame⟩ := read start prepared.owned (by rw [prepared.phase]; rfl)
  rw [NativeScope.read_io] at readAt
  obtain ⟨value, reached⟩ := EST.Out.ok.inj readAt
  subst t
  have recovered := prepared.advance frame
  let middle := ((ref.get : BaseIO (Phase Wal)) start).state
  have changed := swap middle recovered.owned (.online wal session)
  unfold NativeScope.Publish
  dsimp only
  rw [value, prepared.phase]
  exact callback _ (recovered.advance changed.2)

end ExperimentalL0.NativeRead
