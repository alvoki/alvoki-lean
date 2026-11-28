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

abbrev Waiting (known : Contract.View) (disk : W → Disk) (Q : W → Prop) (w : W) :=
  Recoverable known none (disk w) ∧ Q w

/-- Both descriptor bindings belong to the WAL's acquired canonical directory.
The lock predicate can track the identity of an enclosing, separately held lock. -/
def AcquireIO.Lease (io : AcquireIO dir P) (s : Store) (w : W) : Prop :=
  s.root = io.canonical ∧ io.directory s.directory w ∧ io.locked s.lock w

/-- Inputs for an actual public open, grouped by their corresponding
runtime or filesystem primitives. The worker starts with the specific
directory, exclusive lock and typed empty slot produced by acquisition. -/
structure OpenOperations (heap : PhaseMemory) (dir : FilePath) (disk : W → Disk)
    (known : Contract.View) (Q : W → Prop) (workerInputs : Store → (W → Prop) → Type) where
  acquire : AcquireIO dir (Waiting known disk Q)
  worker : ∀ s : Store, s.root = acquire.canonical →
    workerInputs s (fun t => acquire.directory s.directory t ∧ acquire.locked s.lock t ∧
      heap.holds s.active none t ∧ Q t)
  install : ∀ c, InstallFrame (fun t => Installed c (disk t) ∧ Q t)
  take : ∀ (s : Store) t, StoreUnwinding dir s t → heap.holds s.active none t → acquire.Lease s t →
    Waiting known disk Q t → let next := ((s.active.swap none : BaseIO _) t).state
    acquire.Lease s next ∧ Waiting known disk Q next
  unlock : ∀ (s : Store) u, StoreUnlockAt dir s u → acquire.Lease s u → Waiting known disk Q u →
    IOReturns s.lock.unlock u (fun _ t => Waiting known disk Q t) (Waiting known disk Q)

abbrev OpenIO (heap : PhaseMemory) (dir : FilePath) (disk : W → Disk) (known : Contract.View) (Q : W → Prop) :=
  OpenOperations heap dir disk known Q (fun s P => StoreIO s disk P)

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

abbrev LocalOpenIO (heap : PhaseMemory) (dir : FilePath) (disk : W → Disk) (known : Contract.View) (Q : W → Prop) :=
  OpenOperations heap dir disk known Q (fun s P => LocalStoreIO s disk P)

def LocalOpenIO.toOpenIO (localIO : LocalOpenIO heap dir disk known Q) : OpenIO heap dir disk known Q where
  acquire := localIO.acquire
  worker s canonical := (localIO.worker s canonical).toStoreIO
  install := localIO.install
  take := localIO.take
  unlock := localIO.unlock

/-- Actual store acquisition produces the canonical path, held lock, directory,
and freshly allocated empty child slot. The worker consumes those resources;
every failed episode still carries the slot needed by the outer unwinder. -/
theorem openExisting_registered_diskPost (ops : OpenIO heap dir disk known Q) (start : Waiting known disk Q w) :
    IOReturns (openExisting dir) w
      (fun h t => ∃ reg, Origin dir h reg w t ∧ heap.Registered h reg t ∧
        Installed reg.session (disk t) ∧ reg.session.view = known ∧ Q t)
      (Waiting known disk Q) := by
  let openIO := ops.acquire
  apply openExisting_registered_of_worker heap dir disk known Q
    (StoreAt heap openIO.canonical openIO.directory openIO.locked (Waiting known disk Q)) openIO.Lease
    (acquireStore_io heap dir openIO.canonical (openIO.resolve w start) openIO.openDir openIO.stat
      openIO.opened openIO.openLock openIO.tryLock openIO.fresh) _ ops.install ops.take ops.unlock
  intro s u entry
  let Qs := fun t => openIO.directory s.directory t ∧ openIO.locked s.lock t ∧
    heap.holds s.active none t ∧ Q t
  have owned : Qs u := ⟨entry.directoryBound, entry.owns, entry.empty, entry.frame.2⟩
  have step := (ops.worker s entry.path).recoverChild_disk owned entry.frame.1
  unfold IOReturns at *
  cases ran : s.recoverChild u with
  | ok pair t =>
    rw [ran] at step
    exact ⟨step.2.1, step.2.2, step.1.2.2.2⟩
  | error e t =>
    rw [ran] at step
    exact ⟨step.1.2.2.1, ⟨entry.path, step.1.1, step.1.2.1⟩, step.2, step.1.2.2.2⟩

end WalRecoverySlice.Segmented.Native
