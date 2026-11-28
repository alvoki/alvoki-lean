import Alvoki.Experiments.L0.NativeReadScope
import Alvoki.Experiments.L0.NativeCleanup

namespace ExperimentalL0.NativeReadRelease
open System Lifecycle NativeScope NativeRead NativeReadScope
open NativeRecoverAt (Cached Child Failed Opening)
open WalRecoverySlice.Segmented.Native (PhaseMemory RootLockAt ChildLockAt segmentPath detachedWorld)

variable {inode : Type} {physical : NativeScope.W → Footprint inode} {root : FilePath}
  {lock : IO.FS.Handle} {ref : NativeScope.Ref} {image : Selected} {heap : PhaseMemory}

/-- The phase cell survives as offline even when a public handle was
retained. These are the persistent files consumed by the next open. -/
structure Offline (physical : NativeScope.W → Footprint inode) (root : FilePath)
    (ref : NativeScope.Ref) (image : Selected) (w : NativeScope.W) : Prop where
  files : Files physical root image w
  phaseRef : (physical w).phaseRef = some ref
  offline : (physical w).phase = .offline

/-- Root ownership remains live through the registered WAL and child closes.
Only the outer unlock may consume this grant. -/
structure Custody (physical : NativeScope.W → Footprint inode) (root : FilePath) (lock : IO.FS.Handle)
    (ref : NativeScope.Ref) (image : Selected) (w : NativeScope.W) : Prop extends Offline physical root ref image w where
  owner : (physical w).rootLock = some (root, lock)

abbrev Nested := WalRecoverySlice.Segmented.Native.CloseSites NativeCleanup.ChildIssued

/-- An unlock error can be masked by a primary failure. The report retains
the actual descriptor outcome independently of what withOpen returns. -/
def Report (physical : NativeScope.W → Footprint inode) (root : FilePath) (lock : IO.FS.Handle)
    (ref : NativeScope.Ref) (image : Selected) (t : NativeScope.W) : Prop :=
  Grant root lock ref ∧ ∃ u, Custody physical root lock ref image u ∧
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
    t.val = .opening ∧ Custody physical root lock ref image t.state
  /-- Live separately opened file descriptions have distinct identities.
  The inner operand is tied to the original registered store or its child
  open, and comes from the indicated concrete lock-file constructor. -/
  freshOpen : ∀ wal reg w, Grant root lock ref → Custody physical root lock ref image w →
    heap.Registered wal reg w → Original root wal reg → ∀ dir fd start entered,
    ((fd = reg.store.lock ∧ dir = reg.store.root) ∨
      (dir = segmentPath reg.store.root reg.session.control.active ∧ ChildLockAt dir reg.child fd)) →
    IO.FS.Handle.mk (dir / "lock") .append start = .ok fd entered → fd ≠ lock
  /-- Read the particular phase of the originally registered child under
  its mutex. Active and poisoned phases retain that child's opened lock.
  A closed phase contains no descriptor. -/
  childRead : ∀ wal reg w fd, Custody physical root lock ref image w → heap.Registered wal reg w →
    Original root wal reg → ChildLockAt (segmentPath reg.store.root reg.session.control.active) reg.child fd →
    ∀ cell mutex, reg.child.Binds cell mutex →
      match ((cell.get : BaseIO _) (mutex.lock (detachedWorld wal reg w)).state).val with
      | .active held _ _ _ | .poisoned held => held = fd
      | .closed => True
  /-- Only a separately owned descriptor at an actual child or WAL unlock
  site is eligible. Mutex and typed cell operations preserve the root. -/
  nested : ∀ wal c w, NativeCleanup.Frame (fun fd u => Nested wal c w fd u ∧ fd ≠ lock)
    (Custody physical root lock ref image)
  rootFrame : ∀ u, Grant root lock ref → Custody physical root lock ref image u →
    Offline physical root ref image (lock.unlock.toBaseIO u).state
  unlocked : ∀ u t, Grant root lock ref → Custody physical root lock ref image u →
    lock.unlock u = .ok () t → (physical t).rootLock = none

/-- Descriptor separation follows from the originally bound successful opens
and the local phase read. No unlock operand is postulated for a completed
child close. -/
theorem Laws.separate (laws : Laws heap physical root lock ref image) (grant : Grant root lock ref)
    (held : Custody physical root lock ref image w) (origin : Original root wal reg)
    (ready : heap.Registered wal reg w) (site : Nested wal reg w fd u) : fd ≠ lock := by
  obtain ⟨outer, child, opened⟩ := origin.2
  have fresh (dir : FilePath) f (bound : (f = reg.store.lock ∧ dir = reg.store.root) ∨
      (dir = segmentPath reg.store.root reg.session.control.active ∧ ChildLockAt dir reg.child f))
      (openedAt : RootLockAt dir f) : f ≠ lock := by
    obtain ⟨a, b, _, made, _⟩ := openedAt
    exact laws.freshOpen wal reg w grant held ready origin dir f a b bound made
  rcases site with inner | ⟨rfl, _⟩
  · obtain ⟨cell, mutex, binds, _, fromPhase⟩ := inner
    have got := laws.childRead wal reg w child held ready origin opened cell mutex binds
    let read := (cell.get : BaseIO _) (mutex.lock (detachedWorld wal reg w)).state
    change (match read.val with | .closed => False | .active f _ _ _ | .poisoned f => fd = f) at fromPhase
    change (match read.val with | .active f _ _ _ | .poisoned f => f = child | .closed => True) at got
    have same : fd = child := by
      cases phase : read.val <;> simp only [phase] at fromPhase got <;>
        first | contradiction | exact fromPhase.trans got
    exact same ▸ fresh _ child (.inr ⟨rfl, opened⟩) opened.root
  · exact fresh _ reg.store.lock (.inl ⟨rfl, rfl⟩) outer

private theorem observed (laws : Laws heap physical root lock ref image) (grant : Grant root lock ref)
    (held : Custody physical root lock ref image u) :
    Post lock.unlock u (fun _ t => Closed physical root lock ref image t)
      (fun _ t => Closed physical root lock ref image t) := by
  have kept := laws.rootFrame u grant held
  unfold Post
  cases ran : lock.unlock u with
  | error e t => exact ⟨by simpa only [EIO.toBaseIO, ran] using kept, grant, u, held, .inr ⟨e, ran⟩⟩
  | ok val t => cases val; exact ⟨by simpa only [EIO.toBaseIO, ran] using kept, grant, u, held,
      .inl ⟨ran, laws.unlocked _ _ grant held ran⟩⟩

private theorem releaseTo (laws : Laws heap physical root lock ref image) (grant : Grant root lock ref)
    (oldValue : ((ref.swap .offline : BaseIO _) w).val = old)
    (held : Custody physical root lock ref image ((ref.swap .offline : BaseIO _) w).state)
    (registered : ∀ h, old.wal = some h → ∃ c, Original root h c ∧ heap.Registered h c ((ref.swap .offline : BaseIO _) w).state)
    (succeed : ∀ t, Closed physical root lock ref image t → ok t)
    (fail : ∀ e t, Closed physical root lock ref image t → err e t) :
    Release ref lock w ok err := by
  let taken := (ref.swap .offline : BaseIO _) w
  have finish u (h : Custody physical root lock ref image u) := (observed laws grant h).weaken (fun _ => succeed) fail
  unfold Release
  dsimp only
  rw [oldValue]
  cases attached : old.wal with
  | none => exact finish taken.state held
  | some wal =>
    obtain ⟨c, origin, ready⟩ := registered wal attached
    have frame : NativeCleanup.Frame (Nested wal c taken.state) (Custody physical root lock ref image) :=
      fun step => laws.nested wal c taken.state
        (step.map (fun fd u site => ⟨site, laws.separate grant held origin ready site⟩))
    exact (NativeCleanup.wal_close heap frame ready held).weaken (fun _ => finish)
      (fun e _ h => (observed laws grant h).weaken (fun _ => fail e) (fun _ => fail e))

private theorem childTo (laws : Laws heap physical root lock ref image) (grant : Grant root lock ref)
    (owned : Owned (physical w) root lock ref) (attached : (physical w).phase.wal = some wal)
    (child : Child physical root image wal w)
    (catalog : (tableNamespace physical root).Represents w image.tables)
    (manifest : (physical w).manifest.active = L0Manifest.encode image.version)
    (succeed : ∀ t, Closed physical root lock ref image t → ok t)
    (fail : ∀ e t, Closed physical root lock ref image t → err e t) :
    Release ref lock w ok err := by
  obtain ⟨value, step⟩ := laws.swap wal w owned .offline
  obtain ⟨c, cache, origin, installed, view⟩ := child
  have finalOwned := And.intro (step.lock.trans owned.1) (step.ref.trans owned.2)
  have finalChild : Child physical root image wal _ :=
    ⟨c, step.child.trans cache, origin, WalRecoverySlice.Segmented.Writebacks.installed step.disk installed, view⟩
  have files := filesOfChild finalChild (catalog.frame step.tablesKept) (step.manifest.trans manifest)
  refine releaseTo laws grant value ⟨⟨files, finalOwned.2, step.phase⟩, finalOwned.1⟩ ?_ succeed fail
  intro h eq
  have same := Option.some.inj (eq.symm.trans attached)
  subst h
  exact ⟨c, origin, (laws.cached _ finalOwned wal c).mp (step.child.trans cache)⟩

theorem onlineTo (laws : Laws heap physical root lock ref image) (grant : Grant root lock ref)
    (ready : Online physical root lock ref wal session image history w)
    (succeed : ∀ t, Closed physical root lock ref image t → ok t)
    (fail : ∀ e t, Closed physical root lock ref image t → err e t) :
    Release ref lock w ok err :=
  childTo laws grant ready.owned (by rw [ready.phase]; rfl) ready.child ready.catalog ready.manifest.1 succeed fail

theorem failedTo (laws : Laws heap physical root lock ref image) (grant : Grant root lock ref)
    (failed : Failed physical root lock ref image w)
    (succeed : ∀ t, Closed physical root lock ref image t → ok t)
    (fail : ∀ e t, Closed physical root lock ref image t → err e t) :
    Release ref lock w ok err := by
  rcases failed with ⟨opening, bytes⟩ | ⟨wal, held, child⟩
  · obtain ⟨value, off⟩ := laws.emptySwap w opening ⟨opening.catalog, bytes, opening.disk⟩
    exact releaseTo laws grant value off (fun _ impossible => by cases impossible) succeed fail
  · exact childTo laws grant held.owned (by rw [held.phaseEq]; rfl) child held.catalog held.manifest.1 succeed fail

theorem online (laws : Laws heap physical root lock ref image) (grant : Grant root lock ref)
    (ready : Online physical root lock ref wal session image history w) :
    Release ref lock w (Closed physical root lock ref image) (fun _ => Closed physical root lock ref image) :=
  onlineTo laws grant ready (fun _ h => h) (fun _ _ h => h)

theorem failed (laws : Laws heap physical root lock ref image) (grant : Grant root lock ref)
    (failure : Failed physical root lock ref image w) :
    Release ref lock w (Closed physical root lock ref image) (fun _ => Closed physical root lock ref image) :=
  failedTo laws grant failure (fun _ h => h) (fun _ _ h => h)

/-- The public read callback returns a list of closed data/error values. The
root descriptor appears only in tryLock and in the cleanup continuation.
Record the actual withFile return independently of lock release status. -/
structure RootCall where
  path : FilePath
  keys : List UInt64
  start : NativeScope.W

def RootCall.run (c : RootCall) : IO (List Reply) :=
  Native.withOpen c.path (fun h => (readMany h c.keys : IO (List Reply)))

structure RootExit (c : RootCall) where
  root : FilePath
  checked : NativeScope.W
  lock : IO.FS.Handle
  entered : NativeScope.W
  resolved : Native.validatedRoot c.path c.start = .ok root checked
  opened : IO.FS.Handle.mk (root / "l0.lock") .append checked = .ok lock entered
  /-- Reached scope body with the exact acquired descriptor. On a grant,
  the assembled callback gets the phase reference and the unlock is the
  release continuation of the concrete scope. -/
  body : match lock.tryLock true entered with
    | .error e t => c.run c.start = .error e t
    | .ok false t => c.run c.start = .error (IO.userError "L0 already open") t
    | .ok true t =>
        let fresh := IO.mkRef (.opening : Phase NativeScope.Wal) t
        ∃ h, h.AtRoot root fresh.val ∧ c.run c.start =
          (Native.phaseCell fresh.val).withSession (IO.userError "L0 cannot publish a session")
            (Native.recoverAt root fresh.val) (readMany h c.keys : IO (List Reply))
            WalRecoverySlice.Segmented.Native.close lock.unlock fresh.state

def RootCall.exit (c : RootCall)
    (resolved : Native.validatedRoot c.path c.start = .ok root checked)
    (opened : IO.FS.Handle.mk (root / "l0.lock") .append checked = .ok lock entered) : RootExit c :=
  ⟨root, checked, lock, entered, resolved, opened, by
    have reached := Native.withOpen_reached c.path (fun h => (readMany h c.keys : IO (List Reply))) c.start
    cases taken : lock.tryLock true entered with
    | error e t => simpa only [resolved, opened, taken, RootCall.run] using reached
    | ok yes t =>
      cases yes <;> simpa only [resolved, opened, taken, RootCall.run] using reached⟩

/-- The runtime gives a private descriptor on a successful lock-file open.
At return from its labelled withFile scope, destruction of its last Lean
reference closes it, including after a tryLock or unlock error. This
contract excludes aliases retained by FFI. Failure during fdopen on Lean
4.36 precedes creation of the labelled exit and lies outside this law. -/
structure RootLifetime where
  privateBorrow : IO.FS.Handle → NativeScope.W → Prop
  liveAtReturn : {c : RootCall} → RootExit c → IO.FS.Handle → Prop
  acquire : ∀ (root : FilePath) w h t, IO.FS.Handle.mk (root / "l0.lock") .append w = .ok h t →
    privateBorrow h t
  lastDrop : ∀ {c : RootCall} (exit : RootExit c), privateBorrow exit.lock exit.entered →
    ¬ liveAtReturn exit exit.lock

theorem root_released (c : RootCall) (life : RootLifetime)
    (resolved : Native.validatedRoot c.path c.start = .ok root checked)
    (opened : IO.FS.Handle.mk (root / "l0.lock") .append checked = .ok lock entered) :
    ¬ life.liveAtReturn (c.exit resolved opened) lock :=
  life.lastDrop (c.exit resolved opened) (life.acquire _ _ _ _ opened)

end ExperimentalL0.NativeReadRelease
