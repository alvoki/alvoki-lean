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
    (ref : NativeScope.Ref) (image : Selected) (w : NativeScope.W)
    (pending : Option WalRecoverySlice.Segmented.Contract.Request := none) : Prop where
  files : RestartFiles pending physical root image w
  phaseRef : (physical w).phaseRef = some ref
  offline : (physical w).phase = .offline

/-- Root ownership remains live through the registered WAL and child closes.
Only the outer unlock may consume this grant. -/
structure Custody (physical : NativeScope.W → Footprint inode) (root : FilePath) (lock : IO.FS.Handle)
    (ref : NativeScope.Ref) (image : Selected) (w : NativeScope.W)
    (pending : Option WalRecoverySlice.Segmented.Contract.Request := none) : Prop extends Offline physical root ref image w pending where
  owner : (physical w).rootLock = some (root, lock)

abbrev Nested := WalRecoverySlice.Segmented.Native.CloseSites NativeCleanup.ChildIssued

/-- An unlock error can be masked by a primary failure. The report retains
the actual descriptor outcome independently of what withOpen returns. -/
def Report (physical : NativeScope.W → Footprint inode) (root : FilePath) (lock : IO.FS.Handle)
    (ref : NativeScope.Ref) (image : Selected) (t : NativeScope.W)
    (pending : Option WalRecoverySlice.Segmented.Contract.Request := none) : Prop :=
  Grant root lock ref ∧ ∃ u, Custody physical root lock ref image u pending ∧
    ((lock.unlock u = .ok () t ∧ (physical t).rootLock = none) ∨ ∃ e, lock.unlock u = .error e t)

structure Closed (physical : NativeScope.W → Footprint inode) (root : FilePath) (lock : IO.FS.Handle)
    (ref : NativeScope.Ref) (image : Selected) (t : NativeScope.W)
    (pending : Option WalRecoverySlice.Segmented.Contract.Request := none) : Prop extends Offline physical root ref image t pending where
  report : Report physical root lock ref image t pending

structure RootUnlock (physical : NativeScope.W → Footprint inode) (root : FilePath)
    (lock : IO.FS.Handle) (ref : NativeScope.Ref) (image : Selected)
    (pending : Option WalRecoverySlice.Segmented.Contract.Request := none) : Prop where
  rootFrame : ∀ u, Grant root lock ref → Custody physical root lock ref image u pending →
    Offline physical root ref image (lock.unlock.toBaseIO u).state pending
  unlocked : ∀ u t, Grant root lock ref → Custody physical root lock ref image u pending →
    lock.unlock u = .ok () t → (physical t).rootLock = none

structure Laws (heap : PhaseMemory) (physical : NativeScope.W → Footprint inode) (root : FilePath)
    (lock : IO.FS.Handle) (ref : NativeScope.Ref) (image : Selected) : Prop extends RootUnlock physical root lock ref image where
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

theorem RootUnlock.observed (laws : RootUnlock physical root lock ref image pending) (grant : Grant root lock ref)
    (held : Custody physical root lock ref image u pending) :
    Post lock.unlock u (fun _ t => Closed physical root lock ref image t pending)
      (fun _ t => Closed physical root lock ref image t pending) := by
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
  have finish u (h : Custody physical root lock ref image u) := (laws.toRootUnlock.observed grant h).weaken (fun _ => succeed) fail
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
      (fun e _ h => (laws.toRootUnlock.observed grant h).weaken (fun _ => fail e) (fun _ => fail e))

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
    ⟨c, step.child.trans cache, origin, installed.frame step cache, view⟩
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

/-- Both public callbacks return closed data. Each receives only the
assembled L0 handle, while the root descriptor is retained by withOpen. -/
inductive RootOperation where
  | reads (keys : List UInt64)
  | mutation (change : Change)

abbrev RootOperation.Result : RootOperation → Type
  | .reads _ => List Reply
  | .mutation _ => Unit

abbrev RootOperation.use : (op : RootOperation) → Native.Handle → IO op.Result
  | .reads keys, h => (readMany h keys : IO (List Reply))
  | .mutation change, h => Native.mutation h change

structure RootScope where
  path : FilePath
  operation : RootOperation
  start : NativeScope.W

def RootScope.run (c : RootScope) : IO c.operation.Result :=
  Native.withOpen c.path c.operation.use

structure RootCall where
  path : FilePath
  keys : List UInt64
  start : NativeScope.W

def RootCall.scope (c : RootCall) : RootScope := ⟨c.path, .reads c.keys, c.start⟩
instance : Coe RootCall RootScope := ⟨RootCall.scope⟩

def RootCall.run (c : RootCall) : IO (List Reply) := c.scope.run

def mutationCall (path : FilePath) (change : Change) (start : NativeScope.W) : RootScope :=
  ⟨path, .mutation change, start⟩

structure RootExit (c : RootScope) where
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
            (Native.recoverAt root fresh.val) (c.operation.use h)
            WalRecoverySlice.Segmented.Native.close lock.unlock fresh.state

def RootScope.exit (c : RootScope)
    (resolved : Native.validatedRoot c.path c.start = .ok root checked)
    (opened : IO.FS.Handle.mk (root / "l0.lock") .append checked = .ok lock entered) : RootExit c :=
  ⟨root, checked, lock, entered, resolved, opened, by
    have reached := Native.withOpen_reached c.path c.operation.use c.start
    cases taken : lock.tryLock true entered with
    | error e t => simpa only [resolved, opened, taken, RootScope.run] using reached
    | ok yes t =>
      cases yes <;> simpa only [resolved, opened, taken, RootScope.run] using reached⟩

abbrev RootCall.exit (c : RootCall)
    (resolved : Native.validatedRoot c.path c.start = .ok root checked)
    (opened : IO.FS.Handle.mk (root / "l0.lock") .append checked = .ok lock entered) : RootExit c :=
  c.scope.exit resolved opened

/-- The runtime gives a private descriptor on a successful lock-file open.
At return from its labelled withFile scope, destruction of its last Lean
reference closes it, including after a tryLock or unlock error. This
contract excludes aliases retained by FFI. Failure during fdopen on Lean
4.36 precedes creation of the labelled exit and lies outside this law. -/
structure RootLifetime where
  privateBorrow : IO.FS.Handle → NativeScope.W → Prop
  liveAtReturn : {c : RootScope} → RootExit c → IO.FS.Handle → Prop
  acquire : ∀ (root : FilePath) w h t, IO.FS.Handle.mk (root / "l0.lock") .append w = .ok h t →
    privateBorrow h t
  lastDrop : ∀ {c : RootScope} (exit : RootExit c), privateBorrow exit.lock exit.entered →
    ¬ liveAtReturn exit exit.lock

theorem RootScope.releasedAt (c : RootScope) (life : RootLifetime)
    (resolved : Native.validatedRoot c.path c.start = .ok root checked)
    (opened : IO.FS.Handle.mk (root / "l0.lock") .append checked = .ok lock entered) :
    ¬ life.liveAtReturn (c.exit resolved opened) lock :=
  life.lastDrop (c.exit resolved opened) (life.acquire _ _ _ _ opened)

/-- Disposal for the actual public invocation. Before a Lean handle exists
there is no labelled root exit. Every successful constructor identifies the
exact descriptor and scope, irrespective of subsequent primitive reports. -/
def RootScope.Released (c : RootScope) (life : RootLifetime) : Prop :=
  match resolved : Native.validatedRoot c.path c.start with
  | .error _ _ => True
  | .ok root checked =>
    match opened : IO.FS.Handle.mk (root / "l0.lock") .append checked with
    | .error _ _ => True
    | .ok lock _entered => ¬ life.liveAtReturn (c.exit resolved opened) lock

theorem RootScope.released (c : RootScope) (life : RootLifetime) : c.Released life := by
  unfold RootScope.Released
  split
  · trivial
  · split
    · trivial
    · exact c.releasedAt life _ _

abbrev RootCall.Released (c : RootCall) (life : RootLifetime) := c.scope.Released life

theorem RootCall.released (c : RootCall) (life : RootLifetime) : c.Released life :=
  c.scope.released life

theorem root_released (c : RootCall) (life : RootLifetime)
    (resolved : Native.validatedRoot c.path c.start = .ok root checked)
    (opened : IO.FS.Handle.mk (root / "l0.lock") .append checked = .ok lock entered) :
    ¬ life.liveAtReturn (c.exit resolved opened) lock :=
  c.scope.releasedAt life resolved opened

theorem mutation_released (path : FilePath) (change : Change) (start : NativeScope.W) (life : RootLifetime) :
    (mutationCall path change start).Released life :=
  (mutationCall path change start).released life

end ExperimentalL0.NativeReadRelease
