import Alvoki.Experiments.L0.NativeWrite
import Alvoki.Experiments.L0.NativeReadRelease
import Alvoki.Experiments.WAL.Segmented.Proofs.AppendCustody

namespace ExperimentalL0.NativeWriteRelease
open System Lifecycle NativeScope
open NativeRead (Footprint Owned FrameTo)
open NativeReadScope (RestartFiles Grant)
open NativeReadRelease (Custody Closed RootUnlock)
open WalRecoverySlice.Segmented.Native (Store PhaseMemory Registration RootLockAt segmentPath)
open WalRecoverySlice.Segmented.Native.AppendIO (SlotLocks OpenedChild)
abbrev WalCustody := WalRecoverySlice.Segmented.Native.AppendIO.Custody
abbrev Slot := Option (Nat × WalRecoverySlice.SingleFile.Handle)
abbrev Request := WalRecoverySlice.Segmented.Contract.Request

variable {inode : Type} {physical : W → Footprint inode} {root : FilePath}
  {lock : IO.FS.Handle} {ref : Ref} {image : Selected} {heap : PhaseMemory}
  {pending : Option Request}

structure Held (pending : Option Request) (physical : W → Footprint inode) (root : FilePath)
    (lock : IO.FS.Handle) (ref : Ref) (image : Selected) (stage : Phase Wal) (w : W) : Prop where
  owned : Owned (physical w) root lock ref
  phase : (physical w).phase = stage
  files : RestartFiles pending physical root image w

theorem Held.ofRecover (held : NativeRecoverAt.Held physical root lock ref image stage w)
    (disk : WalRecoverySlice.Segmented.Recoverable image.view pending (physical w).disk) :
    Held pending physical root lock ref image stage w :=
  ⟨held.owned, held.phaseEq, held.catalog, held.manifest.1, disk⟩

theorem Held.advance (held : Held pending physical root lock ref image stage w)
    (step : FrameTo physical root wal image.tables w t next) :
    Held pending physical root lock ref image next t :=
  ⟨⟨step.lock.trans held.owned.1, step.ref.trans held.owned.2⟩, step.phase,
    held.files.catalog.frame step.tablesKept, step.manifest.trans held.files.manifest,
    step.disk.recoverable held.files.disk⟩

private theorem Held.detached (held : Held pending physical root lock ref image .offline w) :
    Custody physical root lock ref image w pending := ⟨⟨held.files, held.owned.2, held.phase⟩, held.owned.1⟩

/-- The actual child-close input after the WAL phase and the active slot
have both been taken. The empty slot goes directly to the store unlock. -/
def childWorld (cell : IO.Ref (WalRecoverySlice.Segmented.Native.Phase Store)) (mutex : Std.BaseMutex)
    (store : Store) (w : W) : W :=
  let closed := (cell.swap .closed : BaseIO _) (mutex.lock w).state
  ((store.active.swap none : BaseIO _) closed.state).state

def Issued (store : Store) (slot : Slot) (u : W) (fd : IO.FS.Handle) (t : W) : Prop :=
  match slot with
  | none => fd = store.lock ∧ t = u
  | some (_, h) => NativeCleanup.ChildIssued h u fd t ∨
      (fd = store.lock ∧ t = ((WalRecoverySlice.SingleFile.close h).toBaseIO u).state)

def Bound (store : Store) (slot : Slot) (dir : FilePath) (fd : IO.FS.Handle) : Prop :=
  (dir = store.root ∧ fd = store.lock) ∨
    ∃ id h, slot = some (id,h) ∧ dir = segmentPath store.root id ∧ OpenedChild dir h fd

structure Laws (heap : PhaseMemory) (pending : Option Request) (physical : W → Footprint inode)
    (root : FilePath) (lock : IO.FS.Handle) (ref : Ref) (image : Selected) : Prop
    extends RootUnlock physical root lock ref image pending where
  separateRefs : ∀ wal store slot w, Owned (physical w) root lock ref → WalCustody heap wal store slot w →
    ∀ cell mutex, wal.Parts cell mutex → heap.separate ref cell ∧ heap.separate ref store.active
  freshOpen : ∀ wal store slot w, Grant root lock ref → Custody physical root lock ref image w pending →
    WalCustody heap wal store slot w → ∀ dir fd start entered, Bound store slot dir fd →
    IO.FS.Handle.mk (dir / "lock") .append start = .ok fd entered → fd ≠ lock
  childRead : ∀ wal store id h w fd, Custody physical root lock ref image w pending →
    WalCustody heap wal store (some (id,h)) w → OpenedChild (segmentPath store.root id) h fd →
    ∀ cell mutex, wal.Parts cell mutex → ∀ field guard, h.Binds field guard →
      match ((field.get : BaseIO _) (guard.lock (childWorld cell mutex store w)).state).val with
      | .active held _ _ _ | .poisoned held => held = fd
      | .closed => True
  nested : ∀ wal store slot w, WalCustody heap wal store slot w → ∀ cell mutex, wal.Parts cell mutex →
    NativeCleanup.Frame (fun fd t => Issued store slot (childWorld cell mutex store w) fd t ∧ fd ≠ lock)
      (Custody physical root lock ref image · pending)

private theorem separate (laws : Laws heap pending physical root lock ref image)
    (grant : Grant root lock ref) (held : Custody physical root lock ref image w pending)
    (walHeld : WalCustody heap wal store slot w) (parts : wal.Parts cell mutex)
    (site : Issued store slot (childWorld cell mutex store w) fd t) : fd ≠ lock := by
  have fresh dir f (bound : Bound store slot dir f) (opened : RootLockAt dir f) : f ≠ lock := by
    obtain ⟨a,b,_,made,_⟩ := opened
    exact laws.freshOpen wal store slot w grant held walHeld dir f a b bound made
  have outer := fresh store.root store.lock (.inl ⟨rfl,rfl⟩) walHeld.1
  cases slot with
  | none => exact site.1 ▸ outer
  | some pair =>
    obtain ⟨id,h⟩ := pair
    rcases site with inner | ⟨rfl, _⟩
    · obtain ⟨f, opened⟩ := walHeld.2.1
      obtain ⟨field, guard, binds, _, actual⟩ := inner
      have got := laws.childRead wal store id h w f held walHeld opened cell mutex parts field guard binds
      let read := (field.get : BaseIO _) (guard.lock (childWorld cell mutex store w)).state
      change (match read.val with | .closed => False | .active g _ _ _ | .poisoned g => fd = g) at actual
      change (match read.val with | .active g _ _ _ | .poisoned g => g = f | .closed => True) at got
      have same : fd = f := by
        cases p : read.val <;> simp only [p] at actual got <;> first | contradiction | exact actual.trans got
      have witness := opened
      obtain ⟨a,b,made,_⟩ := witness
      exact same ▸ fresh _ f (.inr ⟨id,h,rfl,rfl,opened⟩) ⟨a,made⟩
    · exact outer

theorem walClose (laws : Laws heap pending physical root lock ref image) (grant : Grant root lock ref)
    (held : Custody physical root lock ref image w pending) (walHeld : WalCustody heap wal store slot w) :
    Custody physical root lock ref image ((WalRecoverySlice.Segmented.Native.close wal).toBaseIO w).state pending := by
  obtain ⟨cell, mutex, parts, distinct, prior, registered⟩ := walHeld.2.2
  let closed := (cell.swap .closed : BaseIO _) (mutex.lock w).state
  let taken := (store.active.swap none : BaseIO _) closed.state
  let P := (Custody physical root lock ref image · pending)
  have frame : NativeCleanup.Frame (Issued store slot (childWorld cell mutex store w)) P :=
    fun step => laws.nested wal store slot w walHeld cell mutex parts
      (step.map (fun _ _ site => ⟨site, separate laws grant held walHeld parts site⟩))
  have empty : P taken.state := frame (.takeChild store.active _) (frame (.walClosed cell _) (frame (.mutexLock mutex w) held))
  have run : WalRecoverySlice.Segmented.Native.close wal w =
      WalRecoverySlice.Segmented.Native.slotCloseResult slot store.lock mutex taken.state := by
    rcases prior with p | ⟨s,p⟩
    · exact (WalRecoverySlice.Segmented.Native.close_owned_slot heap parts distinct p (.inl rfl) registered).2.2
    · exact (WalRecoverySlice.Segmented.Native.close_owned_slot heap parts distinct p (.inr ⟨s,rfl⟩) registered).2.2
  have final : P (WalRecoverySlice.Segmented.Native.returnedWorld (WalRecoverySlice.Segmented.Native.close wal w)) := by
    rw [run]
    cases slot with
    | none =>
      have root := frame (.fileUnlock store.lock taken.state ⟨rfl,rfl⟩) empty
      cases r : store.lock.unlock taken.state with
      | ok x t | error e t =>
        have after : P t := by simpa only [EIO.toBaseIO, r] using root
        simpa only [WalRecoverySlice.Segmented.Native.slotCloseResult, r,
          WalRecoverySlice.Segmented.Native.returnedWorld] using frame (.mutexUnlock mutex t) after
    | some pair =>
      obtain ⟨id,h⟩ := pair
      exact NativeCleanup.closeResult_frame frame h store.lock mutex (fun _ _ s => .inl s)
        (.inr ⟨rfl,rfl⟩) empty
  cases r : WalRecoverySlice.Segmented.Native.close wal w <;>
    simpa only [P, EIO.toBaseIO, r, WalRecoverySlice.Segmented.Native.returnedWorld] using final

private theorem take (laws : Laws heap pending physical root lock ref image)
    (phase : NativeRecoverAt.PhasePrimitives physical root lock ref image)
    (entry : Held pending physical root lock ref image stage w) (walHeld : WalCustody heap wal store slot w) :
    let taken := (ref.swap .offline : BaseIO _) w
    taken.val = stage ∧ Custody physical root lock ref image taken.state pending ∧
      WalCustody heap wal store slot taken.state := by
  intro taken
  obtain ⟨value, effects⟩ := phase.refSwap wal w entry.owned .offline
  obtain ⟨rootBound, slotBound, cell, mutex, parts, distinct, prior, registered⟩ := walHeld
  obtain ⟨separateCell, separateSlot⟩ := laws.separateRefs wal store slot w entry.owned
    ⟨rootBound, slotBound, cell, mutex, parts, distinct, prior, registered⟩ cell mutex parts
  refine ⟨value.trans entry.phase, (entry.advance effects).detached, rootBound, slotBound, cell, mutex, parts,
    distinct, ?_, heap.swapFrame .offline separateSlot registered⟩
  rcases prior with poisoned | ⟨s, ready⟩
  · exact .inl (heap.swapFrame .offline separateCell poisoned)
  · exact .inr ⟨s, heap.swapFrame .offline separateCell ready⟩

/-- The write error closes its own WAL, then returns that original exception
at the reached world even when either the child close or the store unlock fails. -/
theorem afterError (laws : Laws heap pending physical root lock ref image) (grant : Grant root lock ref)
    (phase : NativeRecoverAt.PhasePrimitives physical root lock ref image)
    (entry : Held pending physical root lock ref image (.updating wal) w)
    (walHeld : WalCustody heap wal store slot w) (err : IO.Error) :
    let taken := (ref.swap .offline : BaseIO _) w
    let endWal := ((WalRecoverySlice.Segmented.Native.close wal).toBaseIO taken.state).state
    taken.val = .updating wal ∧ NativeWrite.afterWrite ref (.error err w) = .error err endWal ∧
      Custody physical root lock ref image endWal pending := by
  intro taken endWal
  obtain ⟨value, detached, owned⟩ := take laws phase entry walHeld
  refine ⟨value, ?_, walClose laws grant detached owned⟩
  unfold NativeWrite.afterWrite
  simp only [EIO.toBaseIO, close_run, value, Phase.wal]
  rfl

/-- After inner error cleanup the outer release swaps an already-offline
cell. Its next operation is the outer root unlock on that exact swap world. -/
theorem outerOffline (wal : Wal) (rootIO : RootUnlock physical root lock ref image pending) (grant : Grant root lock ref)
    (phase : NativeRecoverAt.PhasePrimitives physical root lock ref image)
    (held : Custody physical root lock ref image w pending)
    (succeed : ∀ t, Closed physical root lock ref image t pending → ok t)
    (fail : ∀ e t, Closed physical root lock ref image t pending → err e t) :
    Release ref lock w ok err := by
  have entry : Held pending physical root lock ref image .offline w := ⟨⟨held.owner, held.phaseRef⟩, held.offline, held.files⟩
  obtain ⟨old, step⟩ := phase.refSwap wal w entry.owned .offline
  unfold Release
  dsimp only
  rw [old, entry.phase]
  exact (rootIO.observed grant (entry.advance step).detached).weaken (fun _ => succeed) fail

/-- Success publishes the new session and preserves the exact new
registration, including a successor produced by rotation. -/
theorem afterSuccess (phase : NativeRecoverAt.PhasePrimitives physical root lock ref image)
    (cached : NativeRecoverAt.Cached heap physical root lock ref)
    (held : NativeRecoverAt.Held physical root lock ref image (.updating wal) w)
    (disk : WalRecoverySlice.Segmented.Recoverable image.view pending (physical w).disk)
    (ready : heap.Registered wal reg w)
    (owned : WalCustody heap wal reg.store (some (reg.session.control.active, reg.child)) w)
    (next : Session) :
    ∃ u, NativeWrite.afterWrite ref (.ok next w) = .ok () u ∧
      Held pending physical root lock ref image (.online wal next) u ∧
      heap.Registered wal reg u ∧ WalCustody heap wal reg.store (some (reg.session.control.active, reg.child)) u := by
  obtain ⟨t,u,read,swapped,published,returned⟩ := NativeWrite.afterWrite_publish held phase next
  have pinned := (cached _ held.owned wal reg).mpr ready
  have final := (cached u published.owned wal reg).mp (swapped.child.trans (read.child.trans pinned))
  exact ⟨u, returned, Held.ofRecover published (swapped.disk.recoverable (read.disk.recoverable disk)), final,
    WalRecoverySlice.Segmented.Native.AppendIO.Custody.fromSlot final owned.1 owned.2.1⟩

/-- With an attached WAL the outer release takes the registered slot
before unlocking the L0 root. The first reported cleanup error wins. -/
theorem outerAttached (laws : Laws heap pending physical root lock ref image) (grant : Grant root lock ref)
    (phase : NativeRecoverAt.PhasePrimitives physical root lock ref image)
    (entry : Held pending physical root lock ref image (.online wal session) w)
    (walHeld : WalCustody heap wal store slot w)
    (succeed : ∀ t, Closed physical root lock ref image t pending → ok t)
    (fail : ∀ e t, Closed physical root lock ref image t pending → err e t) :
    Release ref lock w ok err := by
  let taken := (ref.swap .offline : BaseIO _) w
  obtain ⟨value, detached, owned⟩ := take laws phase entry walHeld
  have kept := walClose laws grant detached owned
  change Custody physical root lock ref image ((WalRecoverySlice.Segmented.Native.close wal).toBaseIO taken.state).state pending at kept
  unfold Release
  dsimp only
  rw [value]
  change Post (WalRecoverySlice.Segmented.Native.close wal) taken.state _ _
  unfold Post
  cases ran : WalRecoverySlice.Segmented.Native.close wal taken.state with
  | ok x t =>
    have here : Custody physical root lock ref image t pending := by simpa only [EIO.toBaseIO, ran] using kept
    exact (laws.toRootUnlock.observed grant here).weaken (fun _ => succeed) fail
  | error e t =>
    have here : Custody physical root lock ref image t pending := by simpa only [EIO.toBaseIO, ran] using kept
    exact (laws.toRootUnlock.observed grant here).weaken (fun _ => fail e) (fun _ => fail e)

end ExperimentalL0.NativeWriteRelease
