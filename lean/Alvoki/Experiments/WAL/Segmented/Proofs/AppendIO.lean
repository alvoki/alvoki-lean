import Alvoki.Experiments.WAL.Segmented.Proofs.NativeAppend
import Alvoki.Experiments.WAL.Proofs.NativePost

namespace WalRecoverySlice.Segmented.Native.AppendIO
open Alvoki.NativePost (W)
abbrev M (σ α : Type) := ExceptT String (EStateM Unit σ) α

/-- A returning syscall/program is related to a returning model outcome.
An abrupt process stop has a separate prefix semantics. -/
def At (actual : IO α) (model : M σ β) (w : W) (s : σ)
    (ok : α → β → W → σ → Prop) (failed : W → σ → Prop) : Prop :=
  match actual w, model.run s with
  | .ok x t, .ok (.ok y) u => ok x y t u
  | .error _ t, .ok (.error _) u => failed t u
  | _, _ => False

theorem At.bind {a : IO α} {b : M σ β} {f : α → IO γ} {g : β → M σ δ}
    (first : At a b w s middle failed)
    (next : ∀ x y t u, middle x y t u → At (f x) (g y) t u ok failed) :
    At (a >>= f) (b >>= g) w s ok failed := by
  unfold At at *
  rw [ExceptT.run_bind]
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, EStateM.bind]
  cases ar : a w <;> cases br : b.run s <;> simp only [ar, br] at first
  case ok.ok x t result u =>
    cases result with
    | ok y => exact next x y t u first
    | error => contradiction
  case error.ok _ t result u =>
    cases result with
    | error => exact first
    | ok => contradiction
  all_goals contradiction

theorem At.map {a : IO α} {b : M σ β} {ok ok' : α → β → W → σ → Prop}
    {failed failed' : W → σ → Prop} (step : At a b w s ok failed)
    (success : ∀ x y t u, ok x y t u → ok' x y t u)
    (error : ∀ t u, failed t u → failed' t u) : At a b w s ok' failed' := by
  unfold At at *
  cases ar : a w <;> cases br : b.run s <;> simp only [ar, br] at step
  case ok.ok x t r u => cases r <;> first | contradiction | exact success _ _ _ _ step
  case error.ok _ t r u => cases r <;> first | contradiction | exact error _ _ step
  all_goals contradiction

end WalRecoverySlice.Segmented.Native.AppendIO
