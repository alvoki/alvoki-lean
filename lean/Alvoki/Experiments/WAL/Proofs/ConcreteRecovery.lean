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

/-- Refinement of the shared decoder and its branches. The only operation
laws are for the calls made through the data or one of the two marker
descriptions. The relations frame the precise next world on both outcomes. -/
structure RecoveryOps (r : W → Image → Prop) (actual : Ops F) (model : Ops M) : Prop where
  data : Sim r actual.readData model.readData Eq
  marker : ∀ slot, slot < 2 → Sim r (actual.readMarker slot) (model.readMarker slot) Eq
  truncate : ∀ n, Sim r (actual.truncate n) (model.truncate n) Eq
  syncData : Sim r actual.syncData model.syncData Eq
  syncMarker : ∀ slot, slot < 2 → Sim r (actual.syncMarker slot) (model.syncMarker slot) Eq

theorem reopen {actual : Ops F} {model : Ops M} (steps : RecoveryOps state actual model)
    (policy : Policy) : Sim state (reopen actual policy) (reopen model policy) Eq := by
  unfold WalRecoverySlice.reopen
  dsimp only
  repeat' first
    | exact Sim.pure rfl
    | exact Sim.throw
    | exact Sim.bind (rel := fun _ _ => False) Sim.throw (fun _ _ h => h.elim)
    | apply (steps.marker _ (by omega)).bind; intro a b eq; subst b
    | apply steps.data.bind; intro a b eq; subst b
    | apply (steps.truncate _).bind; intro a b eq; cases a; cases b
    | apply (steps.syncMarker _ (by omega)).bind; intro a b eq; cases a; cases b
    | apply steps.syncData.bind; intro a b eq; cases a; cases b
    | apply (Sim.pure rfl).bind; intro a b eq; subst b
    | split
    | dsimp only

end WalRecoverySlice.SingleFile.ConcreteRecovery
