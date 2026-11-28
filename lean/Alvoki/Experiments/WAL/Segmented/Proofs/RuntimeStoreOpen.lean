import Alvoki.Experiments.WAL.Segmented.Proofs.RuntimeChild
import Alvoki.Experiments.WAL.Segmented.Proofs.StoreAcquisition

namespace WalRecoverySlice.Segmented.Native
open Alvoki.NativePost System Model

/-- Primitive effects for the canonical root, its opened directory, and its
exclusive lock. The lock binding refers to the already opened descriptor.
The caller chooses its protected footprint independently of these resources. -/
structure AcquireIO (dir : FilePath) (P : W → Prop) where
  canonical : FilePath
  directory : IO.FS.Handle → W → Prop
  locked : IO.FS.Handle → W → Prop
  opened : IO.FS.Handle → IO.FS.Handle → W → Prop
  resolve : ∀ w, P w → IOReturns (IO.FS.realPath dir) w (fun r t => r = canonical ∧ P t) P
  openDir : ∀ t, P t → IOReturns (IO.FS.Handle.mk canonical .read) t
    (fun d u => directory d u ∧ P u) P
  stat : ∀ d t, directory d t → P t → IOReturns (canonical / "lock").symlinkMetadata t
    (fun _ u => directory d u ∧ P u) (fun u => directory d u ∧ P u)
  openLock : ∀ d t, directory d t → P t → IOReturns (IO.FS.Handle.mk (canonical / "lock") .append) t
    (opened d) P
  tryLock : ∀ d h t, opened d h t → IOReturns (h.tryLock true) t
    (fun yes u => if yes then directory d u ∧ locked h u ∧ P u else P u) P
  fresh : ∀ d h t, directory d t → locked h t → P t →
    let r := (IO.mkRef (none : Option (Nat × SingleFile.Handle)) : BaseIO _) t
    directory d r.state ∧ locked h r.state ∧ P r.state

abbrev WaitingFor (req : Option Contract.Request) (known : Contract.View) (disk : W → Disk) (Q : W → Prop) (w : W) :=
  Recoverable known req (disk w) ∧ Q w

abbrev Waiting := WaitingFor none

/-- Both descriptor bindings belong to the WAL's acquired canonical directory.
The lock predicate can track the identity of an enclosing, separately held lock. -/
def AcquireIO.Lease (io : AcquireIO dir P) (s : Store) (w : W) : Prop :=
  s.root = io.canonical ∧ io.directory s.directory w ∧ io.locked s.lock w

/-- Inputs for an actual public open, grouped by their corresponding
runtime or filesystem primitives. The worker starts with the specific
directory, exclusive lock and typed empty slot produced by acquisition. -/
structure OpenOperations (heap : PhaseMemory) (dir : FilePath) (disk : W → Disk)
    (known : Contract.View) (Q : W → Prop) (workerInputs : Store → (W → Prop) → Type)
    (childOwns : (s : Store) → (P : W → Prop) → workerInputs s P → Policy → Nat → SingleFile.Handle → List Bytes → W → Prop)
    (req : Option Contract.Request := none) where
  acquire : AcquireIO dir (WaitingFor req known disk Q)
  worker : ∀ s : Store, s.root = acquire.canonical →
    workerInputs s (fun t => acquire.directory s.directory t ∧ acquire.locked s.lock t ∧
      heap.holds s.active none t ∧ Q t)
  install : ∀ s path session h, InstallFrame (fun t =>
    RecoveredChild disk (childOwns s _ (worker s path)) session h t ∧ Q t)
  take : ∀ (s : Store) t, StoreUnwinding dir s t → heap.holds s.active none t → acquire.Lease s t →
    WaitingFor req known disk Q t → let next := ((s.active.swap none : BaseIO _) t).state
    acquire.Lease s next ∧ WaitingFor req known disk Q next
  unlock : ∀ (s : Store) u, StoreUnlockAt dir s u → acquire.Lease s u → WaitingFor req known disk Q u →
    IOReturns s.lock.unlock u (fun _ t => WaitingFor req known disk Q t) (WaitingFor req known disk Q)

abbrev OpenIO (heap : PhaseMemory) (dir : FilePath) (disk : W → Disk) (known : Contract.View) (Q : W → Prop) (req : Option Contract.Request := none) :=
  OpenOperations heap dir disk known Q (fun s P => StoreIO s disk P) (fun _ _ ops => ops.children.owns) req

/-- Supply only the selected child's primitive interpretation to the root
adapter. The checked child assembly constructs all three operation laws. -/
abbrev LocalStoreIO (s : Store) (disk : W → Disk) (Q : W → Prop) :=
  StoreOperations s disk Q (ChildPrimitives s disk Q) ChildPrimitives.access

def LocalStoreIO.toStoreIO (localIO : LocalStoreIO s disk Q) : StoreIO s disk Q where
  controlBytes := localIO.controlBytes
  controlBound := localIO.controlBound
  metadata := localIO.metadata
  file := localIO.file
  sync := localIO.sync
  children := localIO.children.access
  cleanup := localIO.cleanup
  cleanupSync := localIO.cleanupSync

abbrev LocalOpenIO (heap : PhaseMemory) (dir : FilePath) (disk : W → Disk) (known : Contract.View) (Q : W → Prop) (req : Option Contract.Request := none) :=
  OpenOperations heap dir disk known Q (fun s P => LocalStoreIO s disk P) (fun _ _ ops => ops.children.access.owns) req

def LocalOpenIO.toOpenIO (localIO : LocalOpenIO heap dir disk known Q req) : OpenIO heap dir disk known Q req where
  acquire := localIO.acquire
  worker s canonical := (localIO.worker s canonical).toStoreIO
  install := localIO.install
  take := localIO.take
  unlock := localIO.unlock

/-- Actual store acquisition produces the canonical path, held lock, directory,
and freshly allocated empty child slot. The worker consumes those resources;
every failed episode still carries the slot needed by the outer unwinder. -/
def OpenIO.Custody (ops : OpenIO heap dir disk known Q req) (s : Store) (session : Session) (h : SingleFile.Handle) (w : W) : Prop :=
  ∃ path : s.root = ops.acquire.canonical, RecoveredChild disk (ops.worker s path).children.owns session h w

theorem openExisting_registered_selected (ops : OpenIO heap dir disk known Q req)
    (start : WaitingFor req known disk Q w) :
    IOReturns (openExisting dir) w
      (fun h t => ∃ reg, Origin dir h reg w t ∧ heap.Registered h reg t ∧ LocksFrom reg ∧
        ops.Custody reg.store reg.session reg.child t ∧ PermittedView known req reg.session.view ∧ Q t)
      (WaitingFor req known disk Q) := by
  let openIO := ops.acquire
  apply openExisting_registered_of_worker heap dir disk known req Q ops.Custody
    (StoreAt heap openIO.canonical openIO.directory openIO.locked (WaitingFor req known disk Q)) openIO.Lease
    (acquireStore_io heap dir openIO.canonical (openIO.resolve w start) openIO.openDir openIO.stat
      openIO.opened openIO.openLock openIO.tryLock openIO.fresh) (fun _ _ => acquireStore_rootLockAt heap dir) _ _ ops.take ops.unlock
  · intro s u entry
    let Qs := fun t => openIO.directory s.directory t ∧ openIO.locked s.lock t ∧
      heap.holds s.active none t ∧ Q t
    have owned : Qs u := ⟨entry.directoryBound, entry.owns, entry.empty, entry.frame.2⟩
    have step := (ops.worker s entry.path).recoverChild_selected owned entry.frame.1
    unfold IOReturns at *
    cases ran : s.recoverChild u with
    | ok pair t =>
      rw [ran] at step
      exact ⟨step.1, ⟨entry.path, step.2.2.2.2⟩, step.2.2.2.1, step.2.1.2.2.2⟩
    | error e t =>
      rw [ran] at step
      exact ⟨step.1.2.2.1, ⟨entry.path, step.1.1, step.1.2.1⟩, step.2, step.1.2.2.2⟩
  · intro s session h
    constructor
    · rintro r id child u ⟨⟨path, custody⟩, frame⟩
      obtain ⟨kept, frame⟩ := (ops.install s path session h).attach r id child u ⟨custody, frame⟩
      exact ⟨⟨path, kept⟩, frame⟩
    · rintro store c u ⟨⟨path, custody⟩, frame⟩
      obtain ⟨kept, frame⟩ := (ops.install s path session h).phase store c u ⟨custody, frame⟩
      exact ⟨⟨path, kept⟩, frame⟩
    · rintro u ⟨⟨path, custody⟩, frame⟩
      obtain ⟨kept, frame⟩ := (ops.install s path session h).mutex u ⟨custody, frame⟩
      exact ⟨⟨path, kept⟩, frame⟩

theorem openExisting_registered_diskPost (ops : OpenIO heap dir disk known Q) (start : Waiting known disk Q w) :
    IOReturns (openExisting dir) w
      (fun h t => ∃ reg, Origin dir h reg w t ∧ heap.Registered h reg t ∧ LocksFrom reg ∧
        Installed reg.session (disk t) ∧ reg.session.view = known ∧ Q t)
      (Waiting known disk Q) := by
  have h := openExisting_registered_selected ops start
  unfold IOReturns at *
  cases ran : openExisting dir w with
  | error e t => rw [ran] at h; exact h
  | ok handle t =>
    rw [ran] at h
    obtain ⟨reg, origin, cached, locks, ⟨_, custody⟩, choice, frame⟩ := h
    exact ⟨reg, origin, cached, locks, custody.installed, by simpa [PermittedView] using choice, frame⟩

end WalRecoverySlice.Segmented.Native
