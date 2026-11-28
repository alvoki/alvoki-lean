import Alvoki.Experiments.WAL.Segmented.Proofs.RuntimeDisk
import Alvoki.Experiments.WAL.Segmented.Proofs.NativeChildIO
import Alvoki.Experiments.WAL.Proofs.ConcreteOpen

namespace WalRecoverySlice.Segmented.Native
open Alvoki.NativePost System
open Model (Disk)
open SingleFile (OpenImage OpenReports)

private theorem Writebacks.change {id : Nat} (writes : Writebacks before after) :
    ChildChange id before after := by
  refine ⟨after, writes, ?_⟩
  cases after
  simp [Disk.setSegment]
  constructor <;> funext i <;> split <;> simp_all

private theorem ChildChange.prepend {id : Nat} (writes : Writebacks before between)
    (next : ChildChange id between after) : ChildChange id before after := by
  obtain ⟨saved, more, exact⟩ := next
  exact ⟨saved, writes.trans more, exact⟩

private theorem Writebacks.named (writes : Writebacks before after) :
    after.liveNames = before.liveNames := by
  induction writes <;> first | rfl | assumption

private theorem Writebacks.segment {id : Nat} (writes : Writebacks before after)
    (prior : Child.Recoverable p bs none (before.segment id)) :
    Child.Recoverable p bs none (after.segment id) := by
  induction writes with
  | nil => exact prior
  | next _ slot file ih =>
    by_cases hit : id = slot
    · subst slot; simpa [Disk.writeback] using ih.settle file
    · simpa [Disk.writeback, hit] using ih

/-- The representation of one in-flight single-file image, qualified by the
segment path. Other files may have undergone writebacks since entry. -/
structure ChildAt (disk : W → Disk) (Q : W → Prop) (id : Nat) (start : Disk)
    (w : W) (model : OpenImage) : Prop where
  frame : Q w
  changed : ChildChange id start (disk w)
  image : (disk w).segment id = model.image

def ChildOpened (owns : SingleFile.Handle → List Bytes → W → Prop) (disk : W → Disk)
    (Q : W → Prop) (id : Nat) (p : Policy) (bs : List Bytes) (before : Disk)
    (h : SingleFile.Handle) (t : W) : Prop :=
  Q t ∧ ChildChange id before (disk t) ∧ owns h bs t ∧
    Child.Installed p ((disk t).segment id) ((disk t).cursor id) bs ∧
    (Child.Settled p (before.segment id) bs → (disk t).segment id = before.segment id)

def ChildFailed (disk : W → Disk) (Q : W → Prop) (id : Nat) (p : Policy)
    (bs : List Bytes) (before : Disk) (t : W) : Prop :=
  Q t ∧ ChildChange id before (disk t) ∧ Child.Recoverable p bs none ((disk t).segment id) ∧
    (Child.Settled p (before.segment id) bs → (disk t).segment id = before.segment id)

private theorem model_keeps_settled (r : OpenReports) (dir : FilePath) (initial : OpenImage) (free : initial.held = false) (prior : Child.Recoverable p bs none initial.image)
    (entry : Child.Settled p initial.image bs) :
    (SingleFile.postState (SingleFile.openExistingModel dir p r initial)).image = initial.image := by
  have physical := SingleFile.openExisting_worker dir p r initial free prior.dirty prior.markers
  have bound : ∀ b ∈ bs, b.length ≤ 32 := by simpa using prior.dirty.bounded
  have fit : bs.length ≤ 255 := by simpa using prior.dirty.fits
  have worker := (reopensSettledSegmentScheduled entry.ready entry.clean bound fit r.worker r.writebacks).1
  rw [← SingleFile.recoverScheduled_eq] at worker
  dsimp only at physical
  rw [Persistence.settleFiles_clean _ _ entry.clean, worker, Persistence.settleFiles_clean _ _ entry.clean] at physical
  exact physical.1.elim id id

/-- Interpret the exact model return produced by the child executable.
The current cursor comes from the stored active phase of this returned handle. -/
theorem ChildAt.opened {id : Nat} (physical : ChildAt disk Q id before t after)
    (initial : OpenImage) (same : before.segment id = initial.image) (free : initial.held = false)
    (r : OpenReports) (prior : Child.Recoverable p bs none (before.segment id))
    (report : SingleFile.openExistingModel dir p r initial = .ok (.ok ready) after)
    (owned : owns h ready.recovered.batches t) (cursor : (disk t).cursor id = ready.recovered.cursor) :
    ChildOpened owns disk Q id p bs before h t := by
  have data := same ▸ prior
  have facts := data.nativeOpen dir r initial free
  rw [report] at facts
  obtain ⟨_, _, _, permit, installed, _⟩ := facts.2
  have bytes : ready.recovered.batches = bs := by simpa [WalRecoverySlice.Contract.Permitted] using permit
  refine ⟨physical.frame, physical.changed, bytes ▸ owned, ?_, ?_⟩
  · rw [physical.image, cursor, ← bytes]; exact installed
  · intro clean
    have stable := model_keeps_settled r dir initial free data (same ▸ clean)
    rw [report] at stable
    exact physical.image.trans (stable.trans same.symm)

theorem ChildAt.failed {id : Nat} (physical : ChildAt disk Q id before t (SingleFile.postState result))
    (initial : OpenImage) (same : before.segment id = initial.image) (free : initial.held = false)
    (r : OpenReports) (prior : Child.Recoverable p bs none (before.segment id))
    (report : SingleFile.openExistingModel dir p r initial = result) :
    ChildFailed disk Q id p bs before t := by
  have data := same ▸ prior
  have facts := data.nativeOpen dir r initial free
  rw [report] at facts
  refine ⟨physical.frame, physical.changed, physical.image.symm ▸ facts.1, ?_⟩
  intro clean
  have stable := model_keeps_settled r dir initial free data (same ▸ clean)
  rw [report] at stable
  exact physical.image.trans (stable.trans same.symm)

/-- The policy stamp is read from the selected child's pathname. Reads and
metadata checks may advance writeback, including in the active child. -/
structure ValidationIO (s : Store) (disk : W → Disk) (Q : W → Prop) where
  policyBytes : Nat → W → ByteArray
  stat : ∀ before (path : FilePath), Keeps (fun t => Q t ∧ Writebacks before (disk t)) path.symlinkMetadata
  list : ∀ before id, Keeps (fun t => Q t ∧ Writebacks before (disk t)) (entries (segmentPath s.root id))
  file : ∀ before id, FileRead.Primitives (segmentPath s.root id / "policy")
    (fun t => Q t ∧ Writebacks before (disk t)) (policyBytes id) (fun x => x)

private theorem ioMap {a : IO α} {ok : α → W → Prop} {fail : W → Prop}
    {done : α → W → Prop} {bad : W → Prop}
    (h : IOReturns a w ok fail) (success : ∀ x t, ok x t → done x t)
    (failure : ∀ t, fail t → bad t) : IOReturns a w done bad := by
  unfold IOReturns at *
  cases r : a w with
  | ok x t => rw [r] at h; exact success x t h
  | error e t => rw [r] at h; exact failure t h

theorem ValidationIO.acquire {id : Nat} (check : ValidationIO s disk Q)
    (start : Q w) (named : id ∈ (disk w).liveNames)
    (prior : Child.Recoverable p bs none ((disk w).segment id))
    (enter : ∀ u, Q u → id ∈ (disk u).liveNames →
      check.policyBytes id u = (policyStamp p).toUTF8 →
      Child.Recoverable p bs none ((disk u).segment id) →
      IOReturns (SingleFile.openExisting (segmentPath s.root id)) u
        (ChildOpened owns disk Q id p bs (disk u)) (ChildFailed disk Q id p bs (disk u))) :
    IOReturns (s.acquireChild p id) w (ChildOpened owns disk Q id p bs (disk w))
      (ChildFailed disk Q id p bs (disk w)) := by
  apply s.acquireChild_post p id (P := fun t => Q t ∧ Writebacks (disk w) (disk t)) ⟨start, .nil⟩
    (check.stat (disk w)) (check.list (disk w) id) (check.file (disk w) id)
  · rintro u ⟨held, writes⟩ stamp
    apply ioMap (enter u held (by rw [Writebacks.named writes]; exact named) stamp (Writebacks.segment writes prior))
    · rintro h t ⟨q, change, owns, inst, exact⟩
      refine ⟨q, change.prepend writes, owns, inst, ?_⟩
      intro clean
      have eq := writes.settled clean
      exact (exact (eq.symm ▸ clean)).trans eq
    · rintro t ⟨q, change, retry, exact⟩
      refine ⟨q, change.prepend writes, retry, ?_⟩
      intro clean
      have eq := writes.settled clean
      exact (exact (eq.symm ▸ clean)).trans eq
  · rintro t ⟨q, writes⟩
    exact ⟨q, Writebacks.change writes, Writebacks.segment writes prior, fun clean => writes.settled clean⟩

open SingleFile.ConcreteRecovery (ModelOpened ActualOpened Ref OpenedTogether OpenSteps WorkerSteps Runtime)

/-- A phase reference owned at this world records the cursor of its retained
writer's segment. Reading the same object after close requires fresh ownership. -/
structure ChildMemory (disk : W → Disk) where
  bound : Nat → IO.FS.Handle → SingleFile.OpenTarget → Prop
  cell : W → Ref → SingleFile.Phase IO.FS.Handle (SingleFile.AppendFiles IO.FS.Handle) → Prop
  mutex : W → Std.BaseMutex → Prop
  cursor : ∀ id w ref lock writer reader markers pos batches,
    bound id writer .writer →
    cell w ref (.active lock (SingleFile.appendFiles writer reader markers) pos batches) →
    (disk w).cursor id = pos

/-- The mutex and phase reference came from the same public child open.
The value binding persists for aliases; access to its contents still needs
the world-indexed live phase and mutex facts. -/
def IssuedPair (ref : Ref) (mutex : Std.BaseMutex) : Prop :=
  ∃ h p dir w t, SingleFile.openExisting dir w = .ok h t ∧ h.Assembled p ref mutex

def ChildMemory.Owns (mem : ChildMemory disk) (h : SingleFile.Handle) (bs : List Bytes) (t : W) : Prop :=
  ∃ (id : Nat) (p : Policy) (ready : ModelOpened) (a : ActualOpened), ∃ ref mutex, ready.recovered.batches = bs ∧
    OpenedTogether (mem.bound id) p a ready ∧ h.Assembled a.policy ref mutex ∧
    mem.cell t ref a.phase ∧ mem.mutex t mutex ∧ IssuedPair ref mutex

/-- Outside-worker writebacks belong to the first and terminal issued
primitives of this attempt, including a failed acquisition or unlock. -/
structure ChildAttempt (s : Store) (disk : W → Disk) (Q : W → Prop) (mem : ChildMemory disk)
    (id : Nat) (p : Policy) (w : W) where
  reports : OpenReports
  state : W → OpenImage → Prop
  steps : OpenSteps (segmentPath s.root id) p reports state (mem.bound id) w
  recovery : WorkerSteps (segmentPath s.root id) state (mem.bound id) reports w
  runtime : Runtime state
  cell : ∀ t ref phase, runtime.cell t ref phase → mem.cell t ref phase
  mutex : ∀ t m, runtime.mutex t m → mem.mutex t m
  boundaries : SingleFile.ConcreteRecovery.Boundaries (segmentPath s.root id) p reports state
    (mem.bound id) runtime w {image := (disk w).segment id} (ChildAt disk Q id (disk w))

theorem ChildAttempt.openExisting {id : Nat} (attempt : ChildAttempt s disk Q mem id p w)
    (prior : Child.Recoverable p bs none ((disk w).segment id)) :
    IOReturns (SingleFile.openExisting (segmentPath s.root id)) w
      (ChildOpened mem.Owns disk Q id p bs (disk w)) (ChildFailed disk Q id p bs (disk w)) := by
  let initial : OpenImage := {image := (disk w).segment id}
  let dir := segmentPath s.root id
  let reports := attempt.reports
  have run := SingleFile.ConcreteRecovery.openExisting attempt.steps attempt.recovery attempt.runtime initial
    attempt.boundaries
  change (match SingleFile.openExisting dir w, SingleFile.openExistingModel dir p reports initial with
    | .ok h t, .ok (.ok ready) u => ChildAt disk Q id (disk w) t u ∧
      SingleFile.ConcreteRecovery.Owns attempt.runtime (mem.bound id) p t h ready
    | .error _ t, .ok (.error _) u => ChildAt disk Q id (disk w) t u
    | _, _ => False) at run
  unfold IOReturns
  dsimp only [dir] at run
  cases actual : SingleFile.openExisting (segmentPath s.root id) w <;>
    cases model : SingleFile.openExistingModel dir p reports initial <;> rw [actual, model] at run
  case ok.ok h t result after =>
    cases result with
    | error => contradiction
    | ok ready =>
      obtain ⟨physical, a, pair, ref, m, built, raw, mutex⟩ := run
      have cell := attempt.cell t ref a.phase raw
      have cur := mem.cursor id t ref a.lock a.writer a.reader a.markers a.recovered.cursor a.recovered.batches
        pair.writer (pair.phase ▸ cell)
      apply physical.opened initial rfl rfl reports prior model
      · exact ⟨id, p, ready, a, ref, m, rfl, pair, built, cell, attempt.mutex _ _ mutex,
          h, a.policy, _, w, t, actual, built⟩
      · rw [← pair.batches]; exact cur
  case error.ok e t result after =>
    cases result with
    | error => exact ChildAt.failed (result := .ok (.error _) after) run initial rfl rfl reports prior model
    | ok => contradiction
  all_goals contradiction

/-- The unlock operand and world after the active cell has been marked
closed. The phase is read under the matching mutex before this transition. -/
def ChildUnlockAt (mem : ChildMemory disk) (id : Nat) (fd : IO.FS.Handle) (m : Std.BaseMutex) (v : W) : Prop :=
  ∃ start ref files pos bs, IssuedPair ref m ∧ mem.mutex start m ∧
    mem.cell start ref (.active fd files pos bs) ∧ mem.bound id fd .lock ∧
    let got := (ref.get : BaseIO _) (m.lock start).state
    got.val = .active fd files pos bs ∧ v = ((ref.set .closed : BaseIO Unit) got.state).state

/-- The read laws apply only to the live cell and mutex. A terminal
reference write can forget the cursor; subsequent unlocks frame that state. -/
structure ChildUseIO (mem : ChildMemory disk) (Q : W → Prop) : Prop where
  lock : ∀ u ref m phase, IssuedPair ref m → Q u → mem.mutex u m → mem.cell u ref phase →
    let t := (m.lock u).state
    Q t ∧ Writebacks (disk u) (disk t) ∧ mem.mutex t m ∧ mem.cell t ref phase
  read : ∀ u ref m phase, IssuedPair ref m → Q u → mem.mutex u m → mem.cell u ref phase →
    let read := (ref.get : BaseIO _) u
    read.val = phase ∧ Q read.state ∧ Writebacks (disk u) (disk read.state) ∧
      mem.mutex read.state m ∧ mem.cell read.state ref phase
  unlock : ∀ u ref m phase, IssuedPair ref m → Q u → mem.mutex u m → mem.cell u ref phase →
    let t := (m.unlock u).state
    Q t ∧ Writebacks (disk u) (disk t) ∧ mem.mutex t m ∧ mem.cell t ref phase
  closed : ∀ start u ref m fd files pos bs, IssuedPair ref m → Q u → mem.mutex u m →
    mem.cell u ref (.active fd files pos bs) → Writebacks start (disk u) →
    let t := ((ref.set .closed : BaseIO Unit) u).state
    Q t ∧ AfterClose start (disk t)
  fileUnlock : ∀ start id fd m u, ChildUnlockAt mem id fd m u → Q u ∧ AfterClose start (disk u) →
    IOReturns fd.unlock u (fun _ t => Q t ∧ AfterClose start (disk t)) (fun t => Q t ∧ AfterClose start (disk t))
  leave : ∀ start id fd (m : Std.BaseMutex) v u, ChildUnlockAt mem id fd m v →
    returnedWorld (fd.unlock v) = u → Q u ∧ AfterClose start (disk u) →
    Q (m.unlock u).state ∧ AfterClose start (disk (m.unlock u).state)

theorem ChildUseIO.scan {disk : W → Disk} {mem : ChildMemory disk} (io : ChildUseIO mem Q) (owned : mem.Owns h bs w) (entry : Q w) :
    IOReturns (SingleFile.scan h) w
      (fun bytes t => bytes = bs ∧ mem.Owns h bs t ∧ Q t ∧ Writebacks (disk w) (disk t))
      (fun t => mem.Owns h bs t ∧ Q t ∧ Writebacks (disk w) (disk t)) := by
  obtain ⟨id, p, ready, a, ref, m, rfl, pair, bound, cell, mutex, issued⟩ := owned
  obtain ⟨q0, b0, m0, r0⟩ := io.lock _ _ _ _ issued entry mutex cell
  obtain ⟨got, q1, b1, m1, r1⟩ := io.read _ _ _ _ issued q0 m0 r0
  have run := SingleFile.scan_active_run bound w (got.trans pair.phase)
  obtain ⟨q2, b2, m2, r2⟩ := io.unlock _ _ _ _ issued q1 m1 r1
  unfold IOReturns
  rw [run, pair.batches]
  exact ⟨rfl, ⟨id, p, ready, a, ref, m, rfl, pair, bound, r2, m2, issued⟩, q2, (b0.trans b1).trans b2⟩

theorem ChildUseIO.close {disk : W → Disk} {mem : ChildMemory disk} (io : ChildUseIO mem Q) (owned : mem.Owns h bs w) (entry : Q w) :
    IOReturns (SingleFile.close h) w (fun _ t => Q t ∧ AfterClose (disk w) (disk t))
      (fun t => Q t ∧ AfterClose (disk w) (disk t)) := by
  obtain ⟨id, p, ready, a, ref, m, _, pair, bound, cell, mutex, issued⟩ := owned
  have binds : h.Binds ref m := by subst h; exact ⟨rfl, rfl⟩
  obtain ⟨q0, b0, m0, r0⟩ := io.lock _ _ _ _ issued entry mutex cell
  obtain ⟨got, q1, b1, m1, r1⟩ := io.read _ _ _ _ issued q0 m0 r0
  let locked := (m.lock w).state
  let read := (ref.get : BaseIO _) locked
  let stopped := ((ref.set .closed : BaseIO Unit) read.state).state
  have valid : ChildUnlockAt mem id a.lock m stopped :=
    ⟨w, ref, _, _, _, issued, mutex, pair.phase ▸ cell, pair.lock, got.trans pair.phase, rfl⟩
  have framed := io.closed (disk w) _ ref m _ _ _ _ issued q1 m1 (pair.phase ▸ r1) (b0.trans b1)
  have released := io.fileUnlock _ id a.lock m stopped valid framed
  change IOReturns a.lock.unlock stopped _ _ at released
  unfold IOReturns
  rw [SingleFile.close_run binds]
  change read.val = a.phase at got
  dsimp only
  dsimp only [read, locked] at got
  rw [got, pair.phase]
  dsimp only
  cases run : a.lock.unlock stopped <;> rw [IOReturns, run] at released <;>
    exact io.leave _ id a.lock m stopped _ valid (by rw [run]; rfl) released

/-- The segmented proof consumes these local child primitives. Validation
chooses the actual pathname, open installs its own phase, and scan or close
consume the exact active reference and mutex on that returned handle. -/
structure ChildPrimitives (s : Store) (disk : W → Disk) (Q : W → Prop) where
  validation : ValidationIO s disk Q
  memory : ChildMemory disk
  phase : ChildUseIO memory Q
  attempt : ∀ id p u, Q u → id ∈ (disk u).liveNames →
    validation.policyBytes id u = (policyStamp p).toUTF8 → ChildAttempt s disk Q memory id p u

def ChildPrimitives.access (primitives : ChildPrimitives s disk Q) : ChildAccess s disk Q where
  owns := primitives.memory.Owns
  acquire p id _ _ q named prior := primitives.validation.acquire q named prior
    (fun u valid present policy retry => (primitives.attempt id p u valid present policy).openExisting retry)
  scan _ _ _ owned := primitives.phase.scan owned
  close _ _ _ owned := primitives.phase.close owned

end WalRecoverySlice.Segmented.Native
