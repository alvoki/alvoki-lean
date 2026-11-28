import Alvoki.Experiments.L0.HealthyClose
import Alvoki.Experiments.L0.HealthyRootAcquisition
import Alvoki.Experiments.L0.WithOpenReads
import Alvoki.Experiments.WAL.Segmented.Proofs.HealthyEmpty

namespace ExperimentalL0.HealthyReads
open System Lifecycle NativeRead
open WalRecoverySlice.Segmented.Native (PhaseMemory)
open WalRecoverySlice.Segmented.Native.HealthyEmpty (FileBytes lift_ok bind_ok io_bind_ok)
abbrev W := NativeScope.W
abbrev Ref := NativeScope.Ref
abbrev Wal := NativeScope.Wal
abbrev F := ExceptT String IO
def empty : Session := ⟨.empty, ∅⟩

structure Manifest (root : FilePath) (w t : W) where
  readWorld : W
  dirWorld : W
  dir : IO.FS.Handle
  bytes : FileBytes (root / "manifest" / "BLOB") w (L0Manifest.encode .empty) readWorld
  openDir : IO.FS.Handle.mk (root / "manifest") .read readWorld = .ok dir dirWorld
  sync : DurableBlob.syncHandle dir dirWorld = .ok () t

theorem Manifest.run (m : Manifest root w t) (ref : Ref) :
    (Native.callbackComponents root ref).manifest.reopen.run w = .ok (.ok .empty) t := by
  have read := m.bytes.run
  have blob : (DurableBlob.native (root / "manifest")).reopen w = .ok (L0Manifest.encode .empty) t := by
    rw [DurableBlob.native_reopen_schedule]
    simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, read, m.openDir, m.sync, Pure.pure,
      instMonadEIO._aux_5, EST.pure]
  change (NativeManifest.backend _).reopen.run w = _
  unfold NativeManifest.backend L0Manifest.backend
  apply bind_ok (lift_ok blob)
  rw [L0Manifest.decode_encode (by decide : L0Manifest.Version.empty.Valid)]
  rfl

theorem recover (manifest : Manifest root start t) (ref : Ref) (heap : PhaseMemory)
    (phaseRead : (ref.get : IO (Phase Wal)) t = .ok .opening u)
    (opened : WalRecoverySlice.Segmented.Native.openExisting (root / "wal") u = .ok wal v)
    (ready : heap.Ready wal WalRecoverySlice.Segmented.Native.HealthyEmpty.session
      ((ref.swap (.recovering wal) : BaseIO _) v).state) :
    Native.recoverAt root ref start = .ok empty
      (WalRecoverySlice.Segmented.Native.scanWorld wal ((ref.swap (.recovering wal) : BaseIO _) v).state) := by
  let reach := ((ref.swap (.recovering wal) : BaseIO _) v).state
  have scan := (WalRecoverySlice.Segmented.Native.scan_ready_world heap ready).1
  have reopen : (Native.callbackComponents root ref).reopenWal.run t =
      .ok (.ok ⟨0, []⟩) (WalRecoverySlice.Segmented.Native.scanWorld wal reach) := by
    unfold Native.callbackComponents Cell.components Cell.reopenWal
    apply bind_ok (lift_ok phaseRead)
    change ((do
      let h ← (liftM (WalRecoverySlice.Segmented.Native.openExisting (root / "wal")) : F Wal)
      let _ ← (liftM (ref.swap (.recovering h) : IO _) : F _)
      liftM (WalRecoverySlice.Segmented.Native.scan h)) : F _).run u = _
    apply bind_ok (lift_ok opened)
    apply bind_ok (lift_ok (NativeScope.swap_io ref (.recovering wal) v))
    exact lift_ok scan
  unfold Native.recoverAt
  change WalRecoverySlice.Segmented.Native.checked _ start = _
  apply WalRecoverySlice.Segmented.Native.HealthyEmpty.checked_ok
  unfold ExperimentalL0.recover
  apply bind_ok (manifest.run ref)
  apply bind_ok reopen
  rfl

theorem getEmpty (binding : Native.Handle.AtRoot h root ref)
    (phase : (ref.get : IO (Phase Wal)) w = .ok (.online wal empty) t) (k : UInt64) :
    Native.get h k w = .ok none t := by
  rw [Native.get_atRoot binding phase (Native.callbackComponents root ref) rfl]
  simp [ExperimentalL0.get, empty, lookupTables, L0Manifest.Version.empty, Bind.bind,
    instMonadEIO._aux_13, EST.bind, Pure.pure, instMonadEIO._aux_5]
  rfl


/-- Successful acquisition of the initialized WAL root. Each operation
uses the previous primitive's returned world and descriptor. -/
structure WalRoot (dir : FilePath) (w : W) where
  canonical : FilePath
  directory : IO.FS.Handle
  lock : IO.FS.Handle
  md : IO.FS.Metadata
  resolved : W
  dirWorld : W
  statWorld : W
  lockWorld : W
  heldWorld : W
  resolve : IO.FS.realPath dir w = .ok canonical resolved
  openDir : IO.FS.Handle.mk canonical .read resolved = .ok directory dirWorld
  stat : (canonical / "lock").symlinkMetadata dirWorld = .ok md statWorld
  valid : (md.type == .file && md.numLinks == 1) = true
  openLock : IO.FS.Handle.mk (canonical / "lock") .append statWorld = .ok lock lockWorld
  held : lock.tryLock true lockWorld = .ok true heldWorld

open WalRecoverySlice.Segmented.Native (ChildMemory Registration Origin LocksFrom)
abbrev storeEntry (p : WalRoot dir w) := (IO.mkRef (none : Option (Nat × WalRecoverySlice.SingleFile.Handle)) p.heldWorld).state

theorem WalRoot.open (p : WalRoot dir w) (heap : PhaseMemory)
    (worker : ∀ s, WalRecoverySlice.Segmented.Native.acquireStore dir w = .ok s (storeEntry p) →
      s.root = p.canonical → s.directory = p.directory → s.lock = p.lock →
      WalRecoverySlice.Segmented.Native.HealthyEmpty.Worker s disk Q mem (storeEntry p)) :
    ∃ wal t reg, WalRecoverySlice.Segmented.Native.openExisting dir w = .ok wal t ∧
      reg.session = WalRecoverySlice.Segmented.Native.HealthyEmpty.session ∧
      Origin dir wal reg w t ∧ heap.Registered wal reg t ∧ LocksFrom reg := by
  obtain ⟨s, grant, root, directory, lock, _⟩ :=
    HealthyRootAcquisition.walStore dir p.canonical p.resolve p.openDir p.stat p.valid p.openLock p.held
  apply (worker s grant root directory lock).openExisting heap grant
  rw [root, lock]
  exact ⟨p.statWorld, p.lockWorld, p.heldWorld, p.openLock, p.held⟩

/-- Positive reports for root validation and the exclusive L0 lock. -/
structure Entry (path root : FilePath) (w : W) where
  resolved : W
  wal : W
  manifest : W
  tables : W
  firstLock : W
  checkedLock : W
  opened : W
  held : W
  wd : IO.FS.Metadata
  md : IO.FS.Metadata
  td : IO.FS.Metadata
  ld : IO.FS.Metadata
  ld' : IO.FS.Metadata
  lock : IO.FS.Handle
  resolve : IO.FS.realPath path w = .ok root resolved
  walStat : (root / "wal").symlinkMetadata resolved = .ok wd wal
  walDir : wd.type = .dir
  manifestStat : (root / "manifest").symlinkMetadata wal = .ok md manifest
  manifestDir : md.type = .dir
  tableStat : (root / "tables").symlinkMetadata manifest = .ok td tables
  tableDir : td.type = .dir
  existsLock : (root / "l0.lock").symlinkMetadata tables = .ok ld firstLock
  lockStat : (root / "l0.lock").symlinkMetadata firstLock = .ok ld' checkedLock
  regular : (ld'.type == .file && ld'.numLinks == 1) = true
  openLock : IO.FS.Handle.mk (root / "l0.lock") .append checkedLock = .ok lock opened
  exclusive : lock.tryLock true opened = .ok true held

def Entry.fresh (p : Entry path root w) := IO.mkRef (.opening : Phase Wal) p.held

theorem Entry.reached (p : Entry path root w) (use : Native.Handle → IO α) :
    ∃ h, h.AtRoot root p.fresh.val ∧ Native.withOpen path use w =
      (Native.phaseCell p.fresh.val).withSession (IO.userError "L0 cannot publish a session")
        (Native.recoverAt root p.fresh.val) (use h) WalRecoverySlice.Segmented.Native.close p.lock.unlock
        p.fresh.state := by
  have grant := Native.withOpen_reached path use w
  have r := HealthyRootAcquisition.validatedRoot path root p.resolve p.walStat p.walDir p.manifestStat
    p.manifestDir p.tableStat p.tableDir p.existsLock p.lockStat p.regular
  simpa only [r, p.openLock, p.exclusive, Entry.fresh] using grant

abbrev specSession := WalRecoverySlice.Segmented.Native.HealthyEmpty.session
abbrev registered (heap : PhaseMemory) (wal : Wal) := heap.Registered wal

/-- Frame a ready child through this specific read of a distinct L0 ref. -/
theorem readFrame (heap : PhaseMemory) (ref : Ref) (p : registered heap wal reg w) :
    registered heap wal reg ((ref.get : BaseIO _) w).state := by
  obtain ⟨distinct, parent, slot⟩ := p
  exact ⟨distinct, heap.readFrame ref parent, heap.readFrame ref slot⟩

def attached (ref : Ref) (wal : Wal) (w : W) := ((ref.swap (.recovering wal) : BaseIO _) w).state
def scanned (ref : Ref) (wal : Wal) (w : W) := WalRecoverySlice.Segmented.Native.scanWorld wal (attached ref wal w)
def phaseRead (ref : Ref) (w : W) := (ref.get : BaseIO _) w
def online (ref : Ref) (wal : Wal) (w : W) :=
  ((ref.swap (.online wal empty) : BaseIO _) (phaseRead ref (scanned ref wal w)).state).state
def firstRead (ref : Ref) (wal : Wal) (w : W) := phaseRead ref (online ref wal w)
def secondRead (ref : Ref) (wal : Wal) (w : W) := phaseRead ref (firstRead ref wal w).state
def offline (ref : Ref) (wal : Wal) (w : W) :=
  (ref.swap .offline : BaseIO _) (secondRead ref wal w).state

/-- All reports apply to this L0 cell at the reached read/swap, starting
from the concrete successful WAL installation. -/
structure RefOps (heap : PhaseMemory) (ref : Ref) (wal : Wal) (reg : Registration) (w : W) : Prop where
  attachKeeps : registered heap wal reg w → registered heap wal reg (attached ref wal w)
  publishRead : (phaseRead ref (scanned ref wal w)).val = .recovering wal
  publishKeeps : registered heap wal reg (phaseRead ref (scanned ref wal w)).state → registered heap wal reg (online ref wal w)
  first : (firstRead ref wal w).val = .online wal empty
  second : (secondRead ref wal w).val = .online wal empty
  closeSwap : (offline ref wal w).val = .online wal empty
  closeKeeps : registered heap wal reg (secondRead ref wal w).state → registered heap wal reg (offline ref wal w).state

theorem RefOps.readyToClose (ops : RefOps heap ref wal reg w) (installed : registered heap wal reg w) :
    registered heap wal reg (offline ref wal w).state := by
  obtain ⟨distinct, phase, slot⟩ := ops.attachKeeps installed
  have atScan : registered heap wal reg (scanned ref wal w) :=
    ⟨distinct, heap.unlock _ (heap.readFrame _ (heap.lock _ phase)), heap.unlock _ (heap.readFrame _ (heap.lock _ slot))⟩
  exact ops.closeKeeps (readFrame heap ref (readFrame heap ref (ops.publishKeeps (readFrame heap ref atScan))))

theorem RefOps.use (p : RefOps heap ref wal reg w) (binding : Native.Handle.AtRoot h root ref) (first second : UInt64) :
    (readMany h [first, second] : IO (List Reply)) (online ref wal w) =
      .ok [.ok none, .ok none] (secondRead ref wal w).state := by
  have a := NativeScope.read_io ref (online ref wal w)
  rw [show ((ref.get : BaseIO _) _).val = _ from p.first] at a
  have b := NativeScope.read_io ref (firstRead ref wal w).state
  rw [show ((ref.get : BaseIO _) _).val = _ from p.second] at b
  have ra := getEmpty binding a first
  have rb := getEmpty binding b second
  dsimp only [firstRead, phaseRead] at rb
  change BaseIO.toEIO (readMany h [first, second]) _ = _
  simp only [BaseIO.toEIO, readMany, EIO.toBaseIO, Bind.bind, instMonadBaseIO._aux_13, ST.bind, ra, rb]
  rfl


private theorem scopeRun {lock : IO.FS.Handle} (p : RefOps heap ref wal reg w) (binding : Native.Handle.AtRoot h root ref)
    (recovered : Native.recoverAt root ref start = .ok empty (scanned ref wal w))
    (closed : WalRecoverySlice.Segmented.Native.close wal (offline ref wal w).state = .ok () after)
    (unlocked : lock.unlock after = .ok () stop) (first second : UInt64) :
    (Native.phaseCell ref).withSession (IO.userError "L0 cannot publish a session") (Native.recoverAt root ref)
      (readMany h [first, second] : IO (List Reply)) WalRecoverySlice.Segmented.Native.close lock.unlock start =
        .ok [.ok none, .ok none] stop := by
  let invalid := IO.userError "L0 cannot publish a session"
  let use := (readMany h [first, second] : IO (List Reply))
  let body := (do
    let session ← Native.recoverAt root ref
    (Native.phaseCell ref).publish invalid session
    use : IO _)
  have publish : (Native.phaseCell ref).publish invalid empty (scanned ref wal w) =
      .ok () (online ref wal w) := by
    unfold Cell.publish
    apply io_bind_ok ((NativeScope.read_io ref (scanned ref wal w)).trans
      (congrArg (fun v => EST.Out.ok v (phaseRead ref (scanned ref wal w)).state) p.publishRead))
    apply io_bind_ok (NativeScope.swap_io ref (.online wal empty) _)
    rfl
  have success : body start = .ok [.ok none, .ok none] (secondRead ref wal w).state :=
    io_bind_ok recovered (io_bind_ok (f := fun _ : Unit => use) publish (p.use binding first second))
  have child : (Native.phaseCell ref).close WalRecoverySlice.Segmented.Native.close
      (secondRead ref wal w).state = .ok () after := by
    unfold Cell.close
    have swap := NativeScope.swap_io ref .offline (secondRead ref wal w).state
    rw [show ((ref.swap .offline : BaseIO _) _).val = _ from p.closeSwap] at swap
    apply io_bind_ok swap
    exact closed
  let cleanup := (Lifecycle.finish (ε := IO.Error) ((Native.phaseCell ref).close WalRecoverySlice.Segmented.Native.close)
    lock.unlock)
  have released : cleanup (secondRead ref wal w).state = .ok () stop := by
    unfold cleanup
    rw [Lifecycle.finish_io]
    simp only [EIO.toBaseIO, child, unlocked]
  change Lifecycle.finish body cleanup start = _
  rw [Lifecycle.finish_io]
  simp only [EIO.toBaseIO, success, released]


/-- Progress on an initialized empty root under successful *reached*
primitive reports. The public result, post-cleanup state, client trace and
intermediate online witnesses all concern one evaluation of withOpen. -/
theorem withOpen {physical : W → Footprint inode} {Q : W → Prop}
    {mem : ChildMemory (fun w => (physical w).disk)}
    (entry : NativeReadScope.Entry physical path root image)
    (files : NativeReadScope.Files physical root image start)
    (heap : PhaseMemory) (runtime : ∀ l r, WithOpenReads.Runtime physical root l r image life heap)
    (prior : Execution.Run events none image)
    (p : Entry path root start) (manifest : Manifest root p.fresh.state t)
    (opening : (p.fresh.val.get : IO (Phase Wal)) t = .ok .opening u)
    (grant : WalRoot (root / "wal") u)
    (worker : ∀ s, WalRecoverySlice.Segmented.Native.acquireStore (root / "wal") u = .ok s (storeEntry grant) →
      s.root = grant.canonical → s.directory = grant.directory → s.lock = grant.lock →
      WalRecoverySlice.Segmented.Native.HealthyEmpty.Worker s (fun w => (physical w).disk) Q mem (storeEntry grant))
    (refs : ∀ wal v reg, Origin (root / "wal") wal reg u v → LocksFrom reg →
      registered heap wal reg v → RefOps heap p.fresh.val wal reg v)
    (cleanup : ∀ wal v reg, Origin (root / "wal") wal reg u v → LocksFrom reg →
      registered heap wal reg (offline p.fresh.val wal v).state →
      HealthyRootAcquisition.Unlocks wal reg (offline p.fresh.val wal v).state)
    (unlock : ∀ wal v endWal, WalRecoverySlice.Segmented.Native.openExisting (root / "wal") u = .ok wal v →
      WalRecoverySlice.Segmented.Native.close wal (offline p.fresh.val wal v).state = .ok () endWal →
      ∃ stop, p.lock.unlock endWal = .ok () stop)
    (first second : UInt64) (rootLife : NativeReadRelease.RootLifetime) :
    ∃ stop, Native.withOpen path (fun h => (readMany h [first, second] : IO (List Reply))) start =
        .ok [.ok none, .ok none] stop ∧
      WithOpenReads.Finished physical root image life events ⟨path, [first, second], start⟩ rootLife [.ok none, .ok none] stop := by
  let use := fun h => (readMany h [first, second] : IO (List Reply))
  obtain ⟨h, binding, outer⟩ := p.reached use
  obtain ⟨wal, v, reg, opened, sessionEq, origin, held, locks⟩ := grant.open heap worker
  let ops := refs wal v reg origin locks held
  have recovered := recover manifest p.fresh.val heap opening opened (sessionEq ▸ (ops.attachKeeps held).ready)
  have kept := ops.readyToClose held
  obtain ⟨endWal, ended⟩ := HealthyRootAcquisition.walClose kept (cleanup wal v reg origin locks kept)
  obtain ⟨stop, unlocked⟩ := unlock wal v endWal opened ended
  have completed := outer.trans (scopeRun ops binding recovered ended unlocked first second)
  refine ⟨stop, completed, ?_⟩
  have safety := WithOpenReads.withOpen entry files heap runtime prior [first, second] rootLife
  rw [NativeScope.Post, completed] at safety
  exact safety

end ExperimentalL0.HealthyReads
