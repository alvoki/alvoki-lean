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

def ChildMemory.Owns (mem : ChildMemory disk) (h : SingleFile.Handle) (bs : List Bytes) (t : W) : Prop :=
  ∃ (id : Nat) (p : Policy) (ready : ModelOpened) (a : ActualOpened), ∃ ref mutex, ready.recovered.batches = bs ∧
    OpenedTogether (mem.bound id) p a ready ∧ h.Assembled a.policy ref mutex ∧
    mem.cell t ref a.phase ∧ mem.mutex t mutex

/-- A schedule for the issued file primitives on one reached segment. Its
entry and exit relate physical writebacks outside the recovery worker. -/
structure ChildAttempt (s : Store) (disk : W → Disk) (Q : W → Prop) (mem : ChildMemory disk)
    (id : Nat) (p : Policy) (w : W) where
  reports : OpenReports
  state : W → OpenImage → Prop
  steps : OpenSteps (segmentPath s.root id) p reports state (mem.bound id)
  recovery : WorkerSteps state (mem.bound id) reports
  runtime : Runtime state
  cell : ∀ t ref phase, runtime.cell t ref phase → mem.cell t ref phase
  mutex : ∀ t m, runtime.mutex t m → mem.mutex t m
  entry : state w (SingleFile.settleImage reports.beforeWorker {image := (disk w).segment id})
  exitFrame : ∀ t u, state t u →
    ChildAt disk Q id (disk w) t (SingleFile.settleImage reports.afterWorker u)

theorem ChildAttempt.openExisting {id : Nat} (attempt : ChildAttempt s disk Q mem id p w)
    (prior : Child.Recoverable p bs none ((disk w).segment id)) :
    IOReturns (SingleFile.openExisting (segmentPath s.root id)) w
      (ChildOpened mem.Owns disk Q id p bs (disk w)) (ChildFailed disk Q id p bs (disk w)) := by
  let initial : OpenImage := {image := (disk w).segment id}
  let dir := segmentPath s.root id
  let reports := attempt.reports
  have run := SingleFile.ConcreteRecovery.openExisting attempt.steps attempt.recovery attempt.runtime w initial
    attempt.entry attempt.exitFrame
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
      · exact ⟨id, p, ready, a, ref, m, rfl, pair, built, cell, attempt.mutex _ _ mutex⟩
      · rw [← pair.batches]; exact cur
  case error.ok e t result after =>
    cases result with
    | error => exact ChildAt.failed (result := .ok (.error _) after) run initial rfl rfl reports prior model
    | ok => contradiction
  all_goals contradiction

end WalRecoverySlice.Segmented.Native
