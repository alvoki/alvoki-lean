import Alvoki.Experiments.WAL.Proofs.NativeOpen

namespace WalRecoverySlice.SingleFile.ConcreteRecovery
open Persistence
abbrev W := Void IO.RealWorld
abbrev F := ExceptT String IO

/-- Relate a returning Linux primitive to its persistence interpretation. A
model interruption has no returned IO result. Reported errors may carry
different diagnostics in the persistence interpreter. -/
def Sim (state : W → σ → Prop) (actual : F α) (model : ExceptT String (EStateM Unit σ) β)
    (same : α → β → Prop) : Prop :=
  ∀ w s, state w s →
    match actual.run w, model.run s with
    | .ok (.ok a) t, .ok (.ok b) u => state t u ∧ same a b
    | .error _ t, .ok (.error _) u | .ok (.error _) t, .ok (.error _) u => state t u
    | _, _ => False

theorem Sim.bind {state : W → σ → Prop} {a : F α} {f : α → F γ}
    {b : ExceptT String (EStateM Unit σ) β} {g : β → ExceptT String (EStateM Unit σ) δ}
    (first : Sim state a b rel) (next : ∀ x y, rel x y → Sim state (f x) (g y) out) :
    Sim state (a >>= f) (b >>= g) out := by
  intro w s prior
  have h := first w s prior
  rw [ExceptT.run_bind, ExceptT.run_bind]
  simp only [ Bind.bind, instMonadEIO._aux_13, EST.bind, EStateM.bind]
  cases ha : a.run w <;> cases hb : b.run s <;> simp only [ha, hb] at h ⊢
  case ok.ok x t y u => cases x <;> cases y <;> first | contradiction | exact h | exact next _ _ h.2 _ _ h.1
  case error.ok x t y u => cases y <;> first | contradiction | exact h
  all_goals first | contradiction | exact h | exact next _ _ h.2 _ _ h.1

theorem Sim.pure {state : W → σ → Prop} (h : rel x y) :
    Sim state (pure x) (pure y) rel :=
  fun _ _ frame => ⟨frame, h⟩

theorem Sim.throw {state : W → σ → Prop} : Sim state (throw e) (throw d) rel :=
  fun _ _ frame => frame

/-- A pointwise primitive observation with separate continuations for
returned values and errors. Each refers to both reached states. -/
def At (a : F α) (b : ExceptT String (EStateM Unit σ) β) (w : W) (s : σ)
    (ok : α → β → W → σ → Prop) (fail : W → σ → Prop) : Prop :=
  match a.run w, b.run s with
  | .ok (.ok x) t, .ok (.ok y) u => ok x y t u
  | .error _ t, .ok (.error _) u | .ok (.error _) t, .ok (.error _) u => fail t u
  | _, _ => False

theorem At.bind {a : F α} {b : ExceptT String (EStateM Unit σ) β} {f : α → F γ} {g : β → ExceptT String (EStateM Unit σ) δ}
    (first : At a b w s mid fail)
    (next : ∀ x y t u, mid x y t u → At (f x) (g y) t u ok fail) :
    At (a >>= f) (b >>= g) w s ok fail := by
  unfold At at *
  rw [ExceptT.run_bind, ExceptT.run_bind]
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, EStateM.bind]
  cases ha : a.run w <;> cases hb : b.run s <;> simp only [ha, hb] at first ⊢
  case ok.ok x t y u => cases x <;> cases y <;> first | contradiction | exact first | exact next _ _ _ _ first
  case error.ok x t y u => cases y <;> first | contradiction | exact first
  all_goals exact first

theorem Sim.atPost {a : F α} {b : ExceptT String (EStateM Unit σ) β} (h : Sim R a b rel)
    (entry : R w s) : At a b w s (fun x y t u => R t u ∧ rel x y) R := by
  have post := h w s entry
  unfold At
  cases ha : a.run w <;> cases hb : b.run s <;> simp only [ha, hb] at post ⊢
  case ok.ok x t y u => cases x <;> cases y <;> exact post
  case error.ok x t y u => cases y <;> exact post
  all_goals exact post

inductive Op where
  | readData
  | readMarker (slot : Nat)
  | syncData
  | syncMarker (slot : Nat)
  | truncate (size : Nat)
  | append (bytes : Bytes)
  | writeMarker (slot : Nat) (bytes : Bytes)

def Op.Result : Op → Type
  | .readData | .readMarker _ => Bytes
  | _ => Unit

def Op.eval (ops : Ops m) : (op : Op) → m op.Result
  | .readData => ops.readData
  | .readMarker k => ops.readMarker k
  | .syncData => ops.syncData
  | .syncMarker k => ops.syncMarker k
  | .truncate n => ops.truncate n
  | .append b => ops.append b
  | .writeMarker k b => ops.writeMarker k b

inductive Program (α : Type) where
  | ret (a : α)
  | stop (err : String)
  | call (op : Op) (next : op.Result → Program α)

def Program.bind (x : Program α) (f : α → Program β) : Program β :=
  match x with
  | .ret a => f a
  | .stop err => .stop err
  | .call op next => .call op (fun a => (next a).bind f)

instance : Monad Program where
  pure := Program.ret
  bind := Program.bind

def Program.catchError (p : Program α) (f : String → Program α) : Program α :=
  match p with
  | .ret v => .ret v
  | .stop err => f err
  | .call op next => .call op fun x => (next x).catchError f

instance : MonadExceptOf String Program where
  throw := Program.stop
  tryCatch := Program.catchError

def programOps : Ops Program where
  readData := .call .readData .ret
  readMarker k := .call (.readMarker k) .ret
  syncData := .call .syncData .ret
  syncMarker k := .call (.syncMarker k) .ret
  truncate n := .call (.truncate n) .ret
  append b := .call (.append b) .ret
  writeMarker k b := .call (.writeMarker k b) .ret

def Program.eval [Monad m] [MonadExceptOf String m] (ops : Ops m) : Program α → m α
  | .ret a => pure a
  | .stop err => throw err
  | .call op next => op.eval ops >>= fun x => (next x).eval ops

/-- The evaluator follows the very same generic decoder that the executable
and persistence instance use. -/
theorem eval_reopen [Monad m] [LawfulMonad m] [MonadExceptOf String m] 
    (ops : Ops m) (p : Policy)
    (throwBind : ∀ {α β : Type} (e : String) (f : α → m β), (throw e >>= f) = throw e) : (WalRecoverySlice.reopen programOps p).eval ops = WalRecoverySlice.reopen ops p := by
  have pureLaw {α : Type} (x : α) : (pure x : Program α).eval ops = pure x := rfl
  have throwLaw {α : Type} (e : String) : (throw e : Program α).eval ops = throw e := rfl
  have step {β : Type} (op : Op) (f : op.Result → Program β) (g : op.Result → m β)
      (next : ∀ v, (f v).eval ops = g v) :
      ((Program.call op Program.ret : Program op.Result) >>= f).eval ops = (op.eval ops >>= g) := by
    change (op.eval ops >>= fun v => (f v).eval ops) = _
    rw [funext next]
  have noThrow {α β : Type} (e : String) (f : α → Program β) (g : α → m β) :
      ((throw e : Program α) >>= f).eval ops = (throw e >>= g) := by rw [throwBind]; rfl
  have lp {α β : Type} (x : α) (f : α → Program β) : (pure x >>= f) = f x := rfl
  unfold WalRecoverySlice.reopen
  dsimp only
  repeat' first
    | exact pureLaw _
    | exact throwLaw _
    | exact noThrow _ _ _
    | apply step .readData; intro v
    | apply step (.readMarker _); intro v
    | apply step (.syncMarker _); intro v
    | apply step (.truncate _); intro v
    | apply step .syncData; intro v
    | simp only [lp, pure_bind, throwBind]
    | split
    | rfl

/-- A strict prefix of successful issued calls. Every transition carries
the actual and model return for that exact instruction. -/
inductive Prefix (actual : Ops F) (model : Ops M) (entry : Program α) (start : W) (initial : Image) :
    Program α → W → Image → Prop where
  | initial : Prefix actual model entry start initial entry start initial
  | next {op : Op} {cont : op.Result → Program α} {x : op.Result} :
    Prefix actual model entry start initial (.call op cont) w i →
    (op.eval actual).run w = .ok (.ok x) t → (op.eval model).run i = .ok (.ok x) u →
    Prefix actual model entry start initial (cont x) t u

structure RecoveryOps (R : W → Image → Prop) (actual : Ops F) (model : Ops M)
    (p : Policy) (start : W) (initial : Image) : Prop where
  issue : ∀ (op : Op) (next : op.Result → Program Decoded) w i,
    Prefix actual model (WalRecoverySlice.reopen programOps p) start initial (.call op next) w i → R w i →
    At (op.eval actual) (op.eval model) w i (fun x y t u => R t u ∧ x = y) R

private theorem interpret (steps : RecoveryOps R actual model p start initial)
    (prog : Program Decoded) (prior : Prefix actual model (WalRecoverySlice.reopen programOps p) start initial prog w i)
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

local instance : LawfulMonad IO := .mk' IO
  (id_map := fun x => funext fun w => by
    simp only [Functor.map, instMonadEIO._aux_1, EST.bind]
    cases x w <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x _ _ => funext fun w => by
    simp only [Bind.bind, instMonadEIO._aux_13, EST.bind]
    cases x w <;> rfl)

theorem reopen (steps : RecoveryOps R actual model p w i) (frame : R w i) :
    At (WalRecoverySlice.reopen actual p) (WalRecoverySlice.reopen model p) w i
      (fun x y t u => R t u ∧ x = y) R := by
  have nativeThrow {α β : Type} (e : String) (f : α → F β) : (throw e >>= f) = throw e := rfl
  have modelThrow {α β : Type} (e : String) (f : α → M β) : (throw e >>= f) = throw e := rfl
  rw [← eval_reopen actual p nativeThrow, ← eval_reopen model p modelThrow]
  exact interpret steps _ .initial frame

end WalRecoverySlice.SingleFile.ConcreteRecovery
