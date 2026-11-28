import Alvoki.Experiments.WAL.Segmented.Proofs.RuntimeStoreOpen
import Alvoki.Experiments.WAL.Segmented.Proofs.AppendIO
import Alvoki.Experiments.WAL.Proofs.ConcreteAppend
import Alvoki.Experiments.WAL.Proofs.ConcreteCreate

namespace WalRecoverySlice.Segmented.Native.AppendIO

open System
open Alvoki.NativePost (W)
variable {id : Nat} {session : Session}
open Persistence
open SingleFile.ConcreteRecovery (OpenedTogether)
open Model (Disk State AppendChild)

/-- The held description and child were produced in the same invocation.
A prepared rotation successor is distinct from a child returned by reopen. -/
inductive ChildSource (dir : FilePath) (p : Policy) (h : SingleFile.Handle) (fd : IO.FS.Handle) : Prop where
  | reopened : ChildLockAt dir h fd → ChildSource dir p h fd
  | created : RootLockFrom dir fd w → SingleFile.create dir p w = .ok h t → ChildSource dir p h fd

theorem ChildSource.root (source : ChildSource dir p h fd) : RootLockAt dir fd := by
  cases source with
  | reopened orig => exact orig.root
  | created orig _ => exact ⟨_, orig⟩

/-- Stable identities that came from installation. The changing phase and
mutex state are tracked separately by Live on each reached native world. -/
structure ChildAuthority (mem : ChildMemory disk) (dir : FilePath) (id : Nat) (p : Policy) (h : SingleFile.Handle) where
  ref : SingleFile.ConcreteRecovery.Ref
  mutex : Std.BaseMutex
  fd : IO.FS.Handle
  reader : IO.FS.Handle
  writer : IO.FS.Handle
  markers : Option (IO.FS.Handle × IO.FS.Handle)
  assembled : h.Assembled p ref mutex
  source : ChildSource dir p h fd
  lockBound : mem.bound id fd .lock
  readerBound : mem.bound id reader .reader
  writerBound : mem.bound id writer .writer
  markerBound : SingleFile.ConcreteRecovery.Markers (mem.bound id) p markers

def ChildAuthority.files (a : ChildAuthority mem dir id p h) : SingleFile.AppendFiles IO.FS.Handle :=
  SingleFile.appendFiles a.writer a.reader a.markers

def ChildAuthority.Live (a : ChildAuthority mem dir id p h) (w : W) (phase : SingleFile.AppendPhase) : Prop :=
  mem.mutex w a.mutex ∧ match phase with
  | .active token boundFiles pos bs => token = .lock ∧ boundFiles = SingleFile.appendBindings p ∧
    mem.cell w a.ref (.active a.fd a.files pos bs)
  | .poisoned token => token = .lock ∧ mem.cell w a.ref (.poisoned a.fd)
  | .closed => False

theorem ChildAuthority.opened {mem : ChildMemory disk} (owned : mem.Owns root p id h bs t)
    (installed : Child.Installed p ((disk t).segment id) ((disk t).cursor id) bs) :
    ∃ a : ChildAuthority mem (segmentPath root id) id p h,
      a.Live t (.active .lock (SingleFile.appendBindings p) (historyCursor bs) bs) := by
  obtain ⟨ready, obj, ref, mutex, batchEq, pair, assembled, cell, guard, source⟩ := owned
  have cur := mem.cursor id t ref obj.lock obj.writer obj.reader obj.markers
    obj.recovered.cursor obj.recovered.batches pair.writer (pair.phase ▸ cell)
  let a : ChildAuthority mem (segmentPath root id) id p h :=
    ⟨ref, mutex, obj.lock, obj.reader, obj.writer, obj.markers, pair.policy ▸ assembled, .reopened source,
      pair.lock, pair.reader, pair.writer, pair.markers⟩
  refine ⟨a, guard, rfl, rfl, ?_⟩
  change mem.cell t ref (.active obj.lock (SingleFile.appendFiles obj.writer obj.reader obj.markers) _ _)
  rw [← installed.position, cur, ← batchEq, ← pair.batches, ← pair.phase]
  exact cell

theorem ChildAuthority.created {mem : ChildMemory disk}
    (steps : SingleFile.ConcreteCreate.Steps R (mem.bound id) dir p reports origin)
    (actual : SingleFile.create dir p origin = .ok h t)
    (modeled : SingleFile.createModel dir p reports = .ok (.ok ready) after)
    (linux : System.Platform.isWindows = false)
    (cellLaw : ∀ t ref phase, steps.runtime.cell t ref phase → mem.cell t ref phase)
    (mutexLaw : ∀ t m, steps.runtime.mutex t m → mem.mutex t m) :
    R t after ∧ ∃ a : ChildAuthority mem dir id p h,
      a.Live t (SingleFile.storedPhase ready) := by
  have ran := SingleFile.ConcreteCreate.create steps
  rw [actual, modeled] at ran
  obtain ⟨frame, obj, pair, ref, mutex, locked, assembled, cell, guard, grant⟩ := ran
  have root : RootLockFrom dir obj.lock origin := rootLockFrom grant
  let a : ChildAuthority mem dir id p h :=
    ⟨ref, mutex, obj.lock, obj.reader, obj.writer, obj.markers, pair.policy ▸ assembled, .created root actual,
      pair.lock, pair.reader, pair.writer, pair.markers⟩
  have guarantee := (SingleFile.createModel_opened dir p reports linux modeled).1
  rw [SingleFile.openedAppendPhase guarantee]
  refine ⟨frame, a, mutexLaw _ _ guard, rfl, rfl, ?_⟩
  have fields := guarantee.2.2
  obtain ⟨_, _, _, _, _, _, _, _, _, cur, _, _, _⟩ := fields
  change mem.cell t ref (.active obj.lock (SingleFile.appendFiles obj.writer obj.reader obj.markers) _ _)
  rw [← cur, ← pair.batches, ← pair.phase]
  exact cellLaw _ _ _ cell

def childCursor (old : Cursor) : SingleFile.AppendPhase → Cursor
  | .active _ _ pos _ => pos
  | _ => old

def childDisk (before : Model.State) (id : Nat) (child : SingleFile.AppendImage) : Disk :=
  before.disk.setSegment id child.image (childCursor (before.disk.cursor id) child.phase)

/-- The caller's selected disk frame and the exact child heap state travel
together through each primitive, including a poisoned return. -/
def ChildAuthority.Link (auth : ChildAuthority mem dir id p h)
    (frame : W → Disk → Prop) (before : Model.State) (t : W) (child : SingleFile.AppendImage) : Prop :=
  auth.Live t child.phase ∧ frame t (childDisk before id child)

theorem ChildAuthority.writeAs {frame : W → Disk → Prop} {before : State} (auth : ChildAuthority mem dir id session.control.policy h)
    (key : AppendChild) (same : key.segment = id)
    (reports : ∀ c, SingleFile.AppendReports session.control.policy c batch)
    (steps : SingleFile.ConcreteAppend.Steps (auth.Link frame before) session.control.policy pos batch (reports pos)
      bs (before.disk.segment id) auth.ref auth.fd auth.files auth.mutex w)
    (live : auth.Live w (.active .lock (SingleFile.appendBindings session.control.policy) pos bs))
    (posEq : before.disk.cursor id = pos) (initial : frame w before.disk) :
    At (SingleFile.append h batch) (Model.writeAs session reports key key batch) w
      (before, .active .lock (SingleFile.appendBindings session.control.policy) pos bs)
      (fun _ _ t u => auth.Live t u.2 ∧ frame t u.1.disk)
      (fun t u => auth.Live t u.2 ∧ frame t u.1.disk) := by
  have unchanged : childDisk before id
      (SingleFile.ConcreteAppend.activeImage session.control.policy (before.disk.segment id) pos bs) = before.disk := by
    unfold childDisk SingleFile.ConcreteAppend.activeImage childCursor
    rw [← posEq]
    cases before.disk
    simp [Disk.setSegment]
    constructor <;> funext i <;> split <;> simp_all
  have start := SingleFile.ConcreteAppend.append reports auth.assembled steps ⟨live, by rw [unchanged]; exact initial⟩
  unfold At Model.writeAs Model.writeRequested
  simp only [↓reduceIte, same]
  unfold Model.writeActive
  simp only [ExceptT.run]
  let input := SingleFile.ConcreteAppend.activeImage session.control.policy (before.disk.segment id) pos bs
  change (match SingleFile.append h batch w, SingleFile.appendModel reports input with
    | .ok () t, .ok (.ok ()) u => auth.Link frame before t u
    | .error _ t, .ok (.error _) u => auth.Link frame before t u
    | _, _ => False) at start
  cases actual : SingleFile.append h batch w <;> cases outcome : SingleFile.appendModel reports input <;>
    simp only [actual, outcome] at start
  case ok.ok x t y u =>
    cases x
    cases y with
    | error => contradiction
    | ok y =>
      cases y
      have diskEq := start.2
      change _ ∧ _ at start
      dsimp only [input, SingleFile.ConcreteAppend.activeImage] at outcome
      rw [outcome]
      exact start
  case error.ok e t y u =>
    cases y with
    | ok => contradiction
    | error d =>
      have poisoned := SingleFile.appendModel_error_phase reports outcome
      dsimp only [input, SingleFile.ConcreteAppend.activeImage] at outcome
      rw [outcome]
      have cur : childCursor (before.disk.cursor id) u.phase = before.disk.cursor id := by rw [poisoned]; rfl
      exact ⟨start.1, by simpa [childDisk, cur] using start.2⟩
  all_goals contradiction

end WalRecoverySlice.Segmented.Native.AppendIO
