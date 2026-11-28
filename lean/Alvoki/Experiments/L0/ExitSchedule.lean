import Alvoki.Experiments.L0.NativeScope

namespace ExperimentalL0.MutationExitCut
open System Lifecycle NativeScope
open WalRecoverySlice
open WalRecoverySlice.Segmented.Native (Store)

open WalRecoverySlice.SingleFile (Handle)

/-- Ordered primitive calls after the WAL returned. Unlock is converted to
BaseIO so both reported outcomes lead to the same remaining finalizers. -/
inductive Tail where
  | done
  | call {α : Type} (op : BaseIO α) (next : α → Tail)

def Tail.run : Tail → BaseIO Unit
  | .done => pure ()
  | .call op next => do (next (← op)).run

noncomputable def child (h : Handle) (next : Tail) : Tail :=
  let cell := h.bindings.choose
  let mutex := h.bindings.choose_spec.choose
  let leave := Tail.call mutex.unlock (fun _ => next)
  let release := fun (fd : IO.FS.Handle) =>
    Tail.call (cell.set .closed) (fun _ => .call fd.unlock.toBaseIO (fun _ => leave))
  .call mutex.lock fun _ => .call cell.get fun
    | .closed => leave
    | .active fd _ _ _ | .poisoned fd => release fd

noncomputable def walClose (h : Wal) (next : Tail) : Tail :=
  let cell := h.parts.choose
  let mutex := h.parts.choose_spec.choose
  let leave := Tail.call mutex.unlock (fun _ => next)
  let release := fun (s : Store) =>
    let unlock := Tail.call s.lock.unlock.toBaseIO (fun _ => leave)
    Tail.call (s.active.swap none) fun
      | none => unlock
      | some (_, ch) => child ch unlock
  .call mutex.lock fun _ => .call (cell.swap .closed) fun
    | .closed => leave
    | .ready s _ | .poisoned s => release s

noncomputable def close (ref : Ref) (next : Tail) : Tail :=
  .call (ref.swap .offline) fun old =>
    match old.wal with
    | none => next
    | some wal => walClose wal next

/-- The outer close always runs. A reported WAL error additionally closes
the current phase in the mutation's own error handler. -/
noncomputable def suffix (ref : Ref) (lock : IO.FS.Handle) (next : Session) (accepted : Bool) : Tail :=
  let outer := close ref (.call lock.unlock.toBaseIO (fun _ => .done))
  if accepted then .call ref.get fun phase =>
    match phase.publish next with
    | some published => .call (ref.swap published) (fun _ => outer)
    | none => close ref outer
  else close ref outer

/-- Interpret the native close recipes in either IO or a tree of primitive
calls. IO errors retain their own continuations through both interpreters. -/
structure Instructions (m : Type → Type u) where
  base : {α : Type} → BaseIO α → m α
  unlock : IO.FS.Handle → m Unit

namespace Instructions
variable {m : Type → Type u} [Monad m] [MonadExceptOf IO.Error m] [MonadFinally m]

private def guarded (i : Instructions m) (mutex : Std.BaseMutex) (body : m α) : m α := do
  i.base mutex.lock
  try body finally i.base mutex.unlock

private def checked (a : ExceptT String m α) : m α := do
  match ← a.run with
  | .ok x => pure x
  | .error e => throw (IO.userError e)

noncomputable def child (i : Instructions m) (h : SingleFile.Handle) : m Unit :=
  let cell := h.bindings.choose
  i.guarded h.bindings.choose_spec.choose do
    let old ← i.base cell.get
    checked (SingleFile.closeWith (m := ExceptT String m) old
      (fun v => liftM (i.base (cell.set v))) (fun fd => liftM (i.unlock fd)))

noncomputable def wal (i : Instructions m) (h : Wal) : m Unit :=
  i.guarded h.parts.choose_spec.choose <| WalRecoverySlice.Segmented.Native.closeWith
    (fun next => i.base (h.parts.choose.swap next)) fun store =>
    WalRecoverySlice.Segmented.Native.releaseWith (error := IO.Error)
      (WalRecoverySlice.Segmented.Native.closeChildWith (i.base (store.active.swap none)) i.child) (i.unlock store.lock)

def cell (i : Instructions m) (r : Ref) : Cell m Wal where
  read := i.base r.get
  swap next := i.base (r.swap next)

def ordinary : Instructions IO := ⟨fun a => liftM a, IO.FS.Handle.unlock⟩

/-- Definitional erasure checks the mutex brackets and the native
single-file close program, including its checked string error. -/
theorem child_ordinary (h : SingleFile.Handle) : ordinary.child h = SingleFile.close h := by
  let cell := h.bindings.choose
  let mutex := h.bindings.choose_spec.choose
  have parts : h.Binds cell mutex := h.bindings.choose_spec.choose_spec
  unfold child
  change _ = _
  have hc := parts.1
  have hm := parts.2
  dsimp only [cell] at hc
  dsimp only [mutex] at hm
  try dsimp only
  rw [← hm, ← hc]
  have chk (a : ExceptT String IO Unit) : checked a = SingleFile.checked a := by
    unfold checked SingleFile.checked
    apply congrArg (Bind.bind a.run)
    funext result
    cases result <;> rfl
  simp only [chk]
  rfl

theorem wal_ordinary (h : Wal) : ordinary.wal h = WalRecoverySlice.Segmented.Native.close h := by
  let cell := h.parts.choose
  let mutex := h.parts.choose_spec.choose
  have parts : h.Parts cell mutex := h.parts.choose_spec.choose_spec
  unfold wal
  rw [show ordinary.child = SingleFile.close from funext child_ordinary]
  have hc := parts.1
  have hm := parts.2
  dsimp only [cell] at hc
  dsimp only [mutex] at hm
  try dsimp only
  rw [← hm, ← hc]
  rfl

theorem cell_ordinary (ref : Ref) : ordinary.cell ref = Native.phaseCell ref := rfl

/-- The same recipes give the ordinary callback and scope cleanup. -/
noncomputable def updating (i : Instructions m) (r : Ref) (lock : IO.FS.Handle)
    (op : Session → m Session) : m Unit :=
  let cell := i.cell r
  finish (ε := IO.Error) (cell.update (IO.userError "L0 requires reopen") op i.wal)
    (finish (ε := IO.Error) (cell.close i.wal) (i.unlock lock))

theorem updating_ordinary (r : Ref) (lock : IO.FS.Handle) (op : Session → IO Session) :
    ordinary.updating r lock op = finish (ε := IO.Error)
      ((Native.phaseCell r).update (IO.userError "L0 requires reopen") op Segmented.Native.close)
      (finish (ε := IO.Error) ((Native.phaseCell r).close Segmented.Native.close) lock.unlock) := by
  unfold updating
  rw [show ordinary.wal = Segmented.Native.close from funext wal_ordinary]
  rfl

end Instructions

/-- Both continuations retain the complete ordered tree of following calls. -/
def PathM (α : Type) := (α → Tail) → (IO.Error → Tail) → Tail

instance : Monad PathM where
  pure x := fun ok _ => ok x
  bind a f := fun ok err => a (fun x => f x ok err) err

instance : MonadExceptOf IO.Error PathM where
  throw e := fun _ err => err e
  tryCatch a f := fun ok err => a ok (fun e => f e ok err)

instance : MonadFinally PathM where
  tryFinally' a f := fun ok err =>
    a (fun x => f (some x) (fun y => ok (x,y)) err)
      (fun e => f none (fun _ => err e) err)

def pathInstructions : Instructions PathM where
  base op := fun ok _ => .call op ok
  unlock fd := fun ok err => .call fd.unlock.toBaseIO fun
    | .ok x => ok x
    | .error e => err e

private theorem contCongr (a : PathM α) {ok₁ ok₂ : α → Tail} {err₁ err₂ : IO.Error → Tail}
    (x : ok₁ = ok₂) (y : err₁ = err₂) : a ok₁ err₁ = a ok₂ err₂ := x ▸ y ▸ rfl

private theorem callCongr {op : BaseIO α} {f g : α → Tail} (eq : ∀ x, f x = g x) :
    Tail.call op f = Tail.call op g := congrArg (Tail.call op) (funext eq)

private theorem child_path (h : SingleFile.Handle) (k : Tail) :
    pathInstructions.child h (fun _ => k) (fun _ => k) = child h k := by
  unfold Instructions.child Instructions.guarded child
  apply callCongr
  intro x
  apply callCongr
  intro phase
  cases phase with
  | closed => rfl
  | active fd files pos bs | poisoned fd =>
    apply callCongr
    intro y
    apply callCongr
    intro reported
    cases reported <;> rfl

private theorem wal_path (h : Wal) (k : Tail) :
    pathInstructions.wal h (fun _ => k) (fun _ => k) = walClose h k := by
  unfold Instructions.wal Instructions.guarded walClose
  apply callCongr
  intro x
  apply callCongr
  intro p
  cases p with
  | closed => rfl
  | ready store s | poisoned store =>
    apply callCongr
    intro taken
    let leave := Tail.call h.parts.choose_spec.choose.unlock (fun _ => k)
    let unlock := Tail.call store.lock.unlock.toBaseIO (fun _ => leave)
    have ignore :
        pathInstructions.unlock store.lock (fun _ => leave) (fun _ => leave) = unlock := by
      apply callCongr
      intro reported
      cases reported <;> rfl
    cases taken with
    | none => exact ignore
    | some pair =>
      obtain ⟨_,ch⟩ := pair
      apply Eq.trans _ (child_path ch unlock)
      apply contCongr (pathInstructions.child ch)
      · funext _; exact ignore
      · funext _; exact ignore

private def forget (a : PathM α) (k : Tail) : Tail := a (fun _ => k) (fun _ => k)

private theorem finish_path (a : PathM α) (b : PathM Unit) (k : Tail) :
    forget (finish (ε := IO.Error) a b) k = forget a (forget b k) := by
  rfl

private theorem unlock_path (fd : IO.FS.Handle) (k : Tail) :
    forget (pathInstructions.unlock fd) k = .call fd.unlock.toBaseIO (fun _ => k) := by
  apply callCongr
  intro result
  cases result <;> rfl

private theorem close_path (r : Ref) (k : Tail) :
    forget ((pathInstructions.cell r).close pathInstructions.wal) k = close r k := by
  apply callCongr
  intro old
  cases branch : old.wal with
  | none => simp only [branch]; rfl
  | some h => simpa only [branch] using wal_path h k

/-- Source interpretation of a complete updating callback within its root
scope. The store operation is interpreted between reservation and publication. -/
noncomputable def updateTree (r : Ref) (lock : IO.FS.Handle) (op : Session → PathM Session) : Tail :=
  forget (pathInstructions.updating r lock op) .done

/-- Tree equality before any world or stop event has been chosen. Both
success and error continuations of the store come from the executable
update, WAL close and nested scope-finalizer recipes. -/
theorem updateTree_eq (r : Ref) (lock : IO.FS.Handle) (op : Session → PathM Session) :
    updateTree r lock op = .call r.get fun old =>
      match old.beginUpdate with
      | none => close r (.call lock.unlock.toBaseIO (fun _ => .done))
      | some (phase,session) => .call (r.swap phase) fun _ =>
          op session (fun next => suffix r lock next true) (fun _ => suffix r lock session false) := by
  unfold updateTree Instructions.updating
  rw [finish_path,finish_path,unlock_path,close_path]
  apply callCongr
  intro old
  cases choose : old.beginUpdate with
  | none =>
    simp only [choose]
    rfl
  | some x =>
    obtain ⟨phase,s⟩ := x
    simp only [choose]
    apply callCongr
    intro _
    apply contCongr (op s)
    · funext next
      apply callCongr
      intro stage
      cases choice : stage.publish next with
      | none => simp only [choice]; exact close_path _ _
      | some v => simp only [choice]; rfl
    · funext _
      exact close_path _ _

/-- Initial recovery and its publication lead into precisely this tree.
A failed open or publish enters the outer close and root unlock. -/
theorem withSession_tree (r : Ref) (lock : IO.FS.Handle) (recover : PathM Session)
    (op : Session → PathM Session) :
    let c := pathInstructions.cell r
    let cleanup := close r (.call lock.unlock.toBaseIO (fun _ => .done))
    forget (c.withSession (IO.userError "L0 cannot publish a session") recover
      (c.update (IO.userError "L0 requires reopen") op pathInstructions.wal)
      pathInstructions.wal (pathInstructions.unlock lock)) .done =
      recover (fun s => c.publish (IO.userError "L0 cannot publish a session") s
        (fun _ => updateTree r lock op) (fun _ => cleanup)) (fun _ => cleanup) := by
  intro c cleanup
  unfold Cell.withSession
  rw [finish_path, finish_path, unlock_path, close_path]
  unfold updateTree Instructions.updating
  rw [finish_path, finish_path, unlock_path, close_path]
  rfl

end ExperimentalL0.MutationExitCut
