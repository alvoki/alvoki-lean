import Alvoki.Experiments.WAL.Proofs.ConcreteOpen
import Alvoki.Experiments.WAL.Proofs.NativeAppend

namespace WalRecoverySlice.SingleFile.ConcreteAppend
open Persistence ConcreteRecovery

theorem eval_append [Monad m] [MonadExceptOf String m]
    (ops : Ops m) (p : Policy) (cursor : Cursor) (batch : Bytes)
    (throwBind : ∀ {α β : Type} (e : String) (f : α → m β), (throw e >>= f) = throw e) :
    (appendBatch programOps p cursor batch).eval ops = appendBatch ops p cursor batch := by
  have step {β : Type} (op : Op) (f : op.Result → Program β) (g : op.Result → m β)
      (next : ∀ v, (f v).eval ops = g v) :
      ((Program.call op Program.ret : Program op.Result) >>= f).eval ops = (op.eval ops >>= g) := by
    change (op.eval ops >>= fun v => (f v).eval ops) = _
    rw [funext next]
  have noThrow {α β : Type} (e : String) (f : α → Program β) (g : α → m β) :
      ((throw e : Program α) >>= f).eval ops = (throw e >>= g) := by rw [throwBind]; rfl
  unfold appendBatch
  dsimp only
  repeat' first
    | rfl
    | exact noThrow _ _ _
    | apply step (.append _); intro v
    | apply step .syncData; intro v
    | apply step (.writeMarker _ _); intro v
    | apply step (.syncMarker _); intro v
    | simp only [throwBind]
    | split

/-- Contracts for precisely the native and modeled instructions issued by
this invocation. The issuing world starts after writing the poisoned phase. -/
structure WorkerSteps (R : W → Image → Prop) (actual : Ops F) (model : Ops M)
    (p : Policy) (cursor : Cursor) (batch : Bytes) (began : W) (image : Image) : Prop where
  issue : ∀ op (next : op.Result → Program Cursor) w i,
    Prefix actual model (appendBatch programOps p cursor batch) began image (.call op next) w i →
    R w i → At (op.eval actual) (op.eval model) w i (fun x y t u => R t u ∧ x = y) R

private theorem interpret (steps : WorkerSteps R actual model p cursor batch began image)
    (prog : Program Cursor) (prior : Prefix actual model (appendBatch programOps p cursor batch) began image prog w i)
    (frame : R w i) : At (prog.eval actual) (prog.eval model) w i (fun x y t u => R t u ∧ x = y) R := by
  induction prog generalizing w i with
  | ret => exact ⟨frame, rfl⟩
  | stop => exact frame
  | call op next ih =>
    change At (_ >>= _) (_ >>= _) _ _ _ _
    have leaf := steps.issue op next w i prior frame
    apply At.bind (mid := fun x y t u => R t u ∧ x = y ∧
      (op.eval actual).run w = .ok (.ok x) t ∧ (op.eval model).run i = .ok (.ok x) u)
    · unfold At at leaf ⊢
      cases a : (op.eval actual).run w <;> cases b : (op.eval model).run i <;> simp only [a, b] at leaf ⊢
      case ok.ok x t y u => cases x <;> cases y <;> first | exact leaf | obtain ⟨r, rfl⟩ := leaf; exact ⟨r, rfl, rfl, rfl⟩
      case error.ok _ _ y _ => cases y <;> exact leaf
      all_goals exact leaf
    · rintro x _ t u ⟨r, rfl, a, b⟩
      exact ih x (prior.next a b) r

abbrev nativeOps (files : AppendFiles IO.FS.Handle) := appendOps Internal.nativeAppend files
abbrev modeledOps (report : AppendReports p cursor batch) :=
  scheduledOps (appendPrimitives report.effects (report.torn.map Subtype.val)) report.writebacks

theorem worker (report : AppendReports p cursor batch)
    (steps : WorkerSteps R (nativeOps files) (modeledOps report) p cursor batch began image)
    (frame : R began image) :
    At (appendBatch (nativeOps files) p cursor batch) (appendWorker (appendBindings p) report)
      began image (fun x y t u => R t u ∧ x = y) R := by
  rw [appendWorker_eq]
  rw [← eval_append (nativeOps files) p cursor batch (fun _ _ => rfl)]
  rw [← eval_append (modeledOps report) p cursor batch (fun _ _ => rfl)]
  exact interpret steps _ .initial frame

abbrev PhaseRef := ConcreteRecovery.Ref

def activeImage (p : Policy) (i : Image) (cursor : Cursor) (known : List Bytes) : AppendImage :=
  ⟨i, .active .lock (appendBindings p) cursor known⟩

def poisonedImage (i : Image) : AppendImage := ⟨i, .poisoned .lock⟩

def readAt (cell : PhaseRef) (mutex : Std.BaseMutex) (start : W) :=
  (cell.get : BaseIO _) (mutex.lock start).state

def poisonAt (cell : PhaseRef) (fd : IO.FS.Handle) (mutex : Std.BaseMutex) (start : W) :=
  ((cell.set (.poisoned fd) : BaseIO Unit) (readAt cell mutex start).state).state

def installAt (cell : PhaseRef) (fd : IO.FS.Handle) (files : AppendFiles IO.FS.Handle)
    (cursor : Cursor) (known : List Bytes) (t : W) : W :=
  ((cell.set (.active fd files cursor known) : BaseIO Unit) t).state

/-- Heap and descriptor operations on the exact accepted active child. The
worker runs between the poisoned ref write and the last active ref write. -/
structure Steps (R : W → AppendImage → Prop) (p : Policy) (cursor : Cursor) (batch : Bytes)
    (report : AppendReports p cursor batch) (known : List Bytes) (image : Image) (cell : PhaseRef)
    (fd : IO.FS.Handle) (files : AppendFiles IO.FS.Handle) (mutex : Std.BaseMutex) (start : W) : Prop where
  read : (readAt cell mutex start).val = .active fd files cursor known
  lockFrame : R start (activeImage p image cursor known) →
    R (mutex.lock start).state (activeImage p image cursor known)
  readFrame : R (mutex.lock start).state (activeImage p image cursor known) →
    R (readAt cell mutex start).state (activeImage p image cursor known)
  poison : R (readAt cell mutex start).state (activeImage p image cursor known) →
    R (poisonAt cell fd mutex start) (poisonedImage image)
  issued : WorkerSteps (fun t i => R t (poisonedImage i)) (nativeOps files) (modeledOps report)
    p cursor batch (poisonAt cell fd mutex start) image
  activate : ∀ next t i,
    (appendBatch (nativeOps files) p cursor batch).run (poisonAt cell fd mutex start) = .ok (.ok next) t →
    R t (poisonedImage i) → R (installAt cell fd files next (known ++ [batch]) t)
      (activeImage p i next (known ++ [batch]))
  release : ∀ next t i,
    (appendBatch (nativeOps files) p cursor batch).run (poisonAt cell fd mutex start) = .ok (.ok next) t →
    let stored := installAt cell fd files next (known ++ [batch]) t
    R stored (activeImage p i next (known ++ [batch])) →
      R (mutex.unlock stored).state (activeImage p i next (known ++ [batch]))
  releaseError : ∀ t i,
    (match (appendBatch (nativeOps files) p cursor batch).run (poisonAt cell fd mutex start) with
     | .error _ u | .ok (.error _) u => u = t | _ => False) →
    R t (poisonedImage i) → R (mutex.unlock t).state (poisonedImage i)

/-- The returning public append, including the reached handle's active or
poisoned phase, against the very same reviewed persistence producer. -/
theorem append (reports : ∀ c, AppendReports p c batch)
    (assembled : h.Assembled p cell mutex)
    (steps : Steps R p cursor batch (reports cursor) known image cell fd files mutex start)
    (frame : R start (activeImage p image cursor known)) :
    match SingleFile.append h batch start, appendModel reports (activeImage p image cursor known) with
    | .ok () t, .ok (.ok ()) u => R t u
    | .error _ t, .ok (.error _) u => R t u
    | _, _ => False := by
  have poison := steps.poison (steps.readFrame (steps.lockFrame frame))
  have observed := worker (reports cursor) steps.issued poison
  unfold At at observed
  rw [append_active_run assembled start steps.read]
  unfold activeImage
  rw [activeResult]
  simp only [nativeOps, poisonAt, readAt] at observed
  generalize n : (appendBatch (appendOps Internal.nativeAppend files) p cursor batch).run ((cell.set (.poisoned fd) : BaseIO Unit) ((cell.get : BaseIO _) (mutex.lock start).state).state).state = result at observed ⊢
  cases result with
  | error err t =>
    cases b : (appendWorker (appendBindings p) (reports cursor)).run image with
    | error => rw [b] at observed; contradiction
    | ok response u =>
      cases response with
      | ok => rw [b] at observed; contradiction
      | error =>
        rw [b] at observed
        exact steps.releaseError t u (by simp only [nativeOps, poisonAt, readAt, n]) observed
  | ok response t =>
    cases response with
    | error =>
      cases b : (appendWorker (appendBindings p) (reports cursor)).run image with
      | error => rw [b] at observed; contradiction
      | ok resp u =>
        cases resp with
        | ok => rw [b] at observed; contradiction
        | error =>
          rw [b] at observed
          exact steps.releaseError t u (by simp only [nativeOps, poisonAt, readAt, n]) observed
    | ok next =>
      cases b : (appendWorker (appendBindings p) (reports cursor)).run image with
      | error => rw [b] at observed; contradiction
      | ok resp u =>
        cases resp with
        | error => rw [b] at observed; contradiction
        | ok modelNext =>
          rw [b] at observed
          obtain ⟨frame, rfl⟩ := observed
          exact steps.release next t u n (steps.activate next t u n frame)

end WalRecoverySlice.SingleFile.ConcreteAppend
