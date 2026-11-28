import Alvoki.Experiments.L0.NativeReadScope
import Alvoki.Experiments.L0.NativeCleanup

namespace ExperimentalL0.NativeReadRelease
open System Lifecycle NativeScope NativeRead NativeReadScope
open NativeRecoverAt (Cached Child Failed Opening)
open WalRecoverySlice.Segmented.Native (PhaseMemory)

variable {inode : Type} {physical : NativeScope.W → Footprint inode} {root : FilePath}
  {lock : IO.FS.Handle} {ref : NativeScope.Ref} {image : Selected} {heap : PhaseMemory}

/-- The phase cell survives as offline even when a public handle was
retained. These are the persistent files consumed by the next open. -/
structure Offline (physical : NativeScope.W → Footprint inode) (root : FilePath)
    (ref : NativeScope.Ref) (image : Selected) (w : NativeScope.W) : Prop where
  files : Files physical root image w
  phaseRef : (physical w).phaseRef = some ref
  offline : (physical w).phase = .offline

/-- An unlock error can be masked by a primary failure. The report retains
the actual descriptor outcome independently of what withOpen returns. -/
def Report (physical : NativeScope.W → Footprint inode) (root : FilePath) (lock : IO.FS.Handle)
    (ref : NativeScope.Ref) (image : Selected) (t : NativeScope.W) : Prop :=
  ∃ u, Offline physical root ref image u ∧
    ((lock.unlock u = .ok () t ∧ (physical t).rootLock = none) ∨ ∃ e, lock.unlock u = .error e t)

structure Closed (physical : NativeScope.W → Footprint inode) (root : FilePath) (lock : IO.FS.Handle)
    (ref : NativeScope.Ref) (image : Selected) (t : NativeScope.W) : Prop extends Offline physical root ref image t where
  report : Report physical root lock ref image t

structure Laws (heap : PhaseMemory) (physical : NativeScope.W → Footprint inode) (root : FilePath)
    (lock : IO.FS.Handle) (ref : NativeScope.Ref) (image : Selected) : Prop where
  cached : Cached heap physical root lock ref
  swap : ∀ wal, RefSwap physical root lock ref wal image.tables
  emptySwap : ∀ w, Opening physical root lock ref image w → Files physical root image w →
    let t := (ref.swap .offline : BaseIO _) w
    t.val = .opening ∧ Offline physical root ref image t.state
  frame : NativeCleanup.Frame (Offline physical root ref image)
  unlocked : ∀ u t, Offline physical root ref image u → lock.unlock u = .ok () t →
    (physical t).rootLock = none

private theorem observed (laws : Laws heap physical root lock ref image)
    (off : Offline physical root ref image u) :
    Post lock.unlock u (fun _ t => Closed physical root lock ref image t)
      (fun _ t => Closed physical root lock ref image t) := by
  have kept := laws.frame (.fileUnlock lock u) off
  unfold Post
  cases ran : lock.unlock u with
  | error e t => exact ⟨by simpa only [EIO.toBaseIO, ran] using kept, u, off, .inr ⟨e, ran⟩⟩
  | ok val t => cases val; exact ⟨by simpa only [EIO.toBaseIO, ran] using kept, u, off, .inl ⟨ran, laws.unlocked _ _ off ran⟩⟩

private theorem releaseTo (laws : Laws heap physical root lock ref image)
    (oldValue : ((ref.swap .offline : BaseIO _) w).val = old)
    (off : Offline physical root ref image ((ref.swap .offline : BaseIO _) w).state)
    (ready : ∀ h, old.wal = some h → ∃ c, heap.Ready h c ((ref.swap .offline : BaseIO _) w).state)
    (succeed : ∀ t, Closed physical root lock ref image t → ok t)
    (fail : ∀ e t, Closed physical root lock ref image t → err e t) :
    Release ref lock w ok err :=
  NativeCleanup.release_of_swap heap laws.frame ref lock oldValue off ready
    (fun _ offline => (observed laws offline).weaken (fun _ => succeed) fail)
    (fun e _ offline => (observed laws offline).weaken (fun _ => fail e) (fun _ => fail e))

private theorem childTo (laws : Laws heap physical root lock ref image)
    (owned : Owned (physical w) root lock ref) (attached : (physical w).phase.wal = some wal)
    (child : Child physical image wal w)
    (catalog : (tableNamespace physical root).Represents w image.tables)
    (manifest : (physical w).manifest.active = L0Manifest.encode image.version)
    (succeed : ∀ t, Closed physical root lock ref image t → ok t)
    (fail : ∀ e t, Closed physical root lock ref image t → err e t) :
    Release ref lock w ok err := by
  obtain ⟨value, step⟩ := laws.swap wal w owned .offline
  obtain ⟨c, cache, installed, view⟩ := child
  have finalOwned := And.intro (step.lock.trans owned.1) (step.ref.trans owned.2)
  have finalChild : Child physical image wal _ :=
    ⟨c, step.child.trans cache, step.disk.installed installed, view⟩
  have files := filesOfChild finalChild (catalog.frame step.tablesKept) (step.manifest.trans manifest)
  refine releaseTo laws value ⟨files, finalOwned.2, step.phase⟩ ?_ succeed fail
  intro h eq
  have same := Option.some.inj (eq.symm.trans attached)
  subst h
  exact ⟨c, (laws.cached _ finalOwned wal c).mp (step.child.trans cache)⟩

theorem onlineTo (laws : Laws heap physical root lock ref image)
    (ready : Online physical root lock ref wal session image history w)
    (succeed : ∀ t, Closed physical root lock ref image t → ok t)
    (fail : ∀ e t, Closed physical root lock ref image t → err e t) :
    Release ref lock w ok err :=
  childTo laws ready.owned (by rw [ready.phase]; rfl) ready.child ready.catalog ready.manifest.1 succeed fail

theorem failedTo (laws : Laws heap physical root lock ref image)
    (failed : Failed physical root lock ref image w)
    (succeed : ∀ t, Closed physical root lock ref image t → ok t)
    (fail : ∀ e t, Closed physical root lock ref image t → err e t) :
    Release ref lock w ok err := by
  rcases failed with ⟨opening, bytes⟩ | ⟨wal, held, child⟩
  · obtain ⟨value, off⟩ := laws.emptySwap w opening ⟨opening.catalog, bytes, opening.disk⟩
    exact releaseTo laws value off (fun _ impossible => by cases impossible) succeed fail
  · exact childTo laws held.owned (by rw [held.phaseEq]; rfl) child held.catalog held.manifest.1 succeed fail

theorem online (laws : Laws heap physical root lock ref image)
    (ready : Online physical root lock ref wal session image history w) :
    Release ref lock w (Closed physical root lock ref image) (fun _ => Closed physical root lock ref image) :=
  onlineTo laws ready (fun _ h => h) (fun _ _ h => h)

theorem failed (laws : Laws heap physical root lock ref image)
    (failure : Failed physical root lock ref image w) :
    Release ref lock w (Closed physical root lock ref image) (fun _ => Closed physical root lock ref image) :=
  failedTo laws failure (fun _ h => h) (fun _ _ h => h)

end ExperimentalL0.NativeReadRelease
