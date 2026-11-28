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

private theorem io_cleanup_run (a : IO α) (c : IO Unit) (w : W) :
    cleanupOnError (error := IO.Error) a c w =
      match a w with
      | .ok x t => .ok x t
      | .error e t => .error e (returnedWorld (c t)) := by
  cases step : a w with
  | ok => simp [cleanupOnError, tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3, EST.tryCatch, step]
  | error e t =>
    cases cleanup : c t <;> simp [cleanupOnError, tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3,
      EST.tryCatch, step, cleanup, Bind.bind, instMonadEIO._aux_13, EST.bind, Pure.pure, instMonadEIO._aux_5,
      EST.pure, throw, throwThe, instMonadExceptOfEIO._aux_1, MonadExceptOf.throw, EST.throw, returnedWorld]

private theorem model_cleanup_run (a : M σ α) (c : M σ Unit) (s : σ) :
    (cleanupOnError (error := String) a c).run s =
      match a.run s with
      | .ok (.error e) t =>
        match c.run t with
        | .ok _ u => .ok (.error e) u
        | .error token u => .error token u
      | other => other := by
  simp only [cleanupOnError, tryCatchThe, MonadExceptOf.tryCatch, ExceptT.tryCatch, Bind.bind,
    ExceptT.bind, ExceptT.run, ExceptT.mk, EStateM.bind]
  cases first : a s with
  | error => rfl
  | ok x t =>
    cases x with
    | ok => rfl
    | error =>
      simp only [EStateM.bind]
      cases r : c t <;> first | rfl | rename_i value _; cases value <;> rfl

theorem At.cleanup {a : IO α} {b : M σ β} {c : IO Unit} {d : M σ Unit}
    (step : At a b w s ok unwind)
    (release : ∀ t u, unwind t u → At c d t u (fun _ _ v z => failed v z) failed) :
    At (cleanupOnError (error := IO.Error) a c) (cleanupOnError (error := String) b d) w s ok failed := by
  unfold At at *
  rw [io_cleanup_run, model_cleanup_run]
  cases ar : a w <;> cases br : b.run s <;> rw [ar, br] at step
  case ok.ok x t r u => cases r <;> first | contradiction | exact step
  case error.ok e t r u =>
    cases r with
    | ok => exact step
    | error =>
      dsimp only
      have closed := release t u step
      cases cr : c t <;> cases dr : d.run u <;> rw [cr, dr] at closed
      case ok.ok _ _ r _ => cases r <;> first | contradiction | exact closed
      case error.ok _ _ r _ => cases r <;> first | contradiction | exact closed
      all_goals contradiction
  all_goals exact step

theorem At.liftRoot {a : IO α} {b : Model.M β} (step : At a b w state ok fail)
    (phase : SingleFile.AppendPhase) :
    At a (Model.liftRootAction b) w (state, phase)
      (fun x y t u => ok x y t u.1 ∧ u.2 = phase)
      (fun t u => fail t u.1 ∧ u.2 = phase) := by
  unfold At at *
  have lifted : (Model.liftRootAction b).run (state, phase) =
      match b.run state with
      | .ok x u => .ok x (u, phase)
      | .error e u => .error e (u, phase) := rfl
  rw [lifted]
  cases ar : a w <;> cases br : b.run state <;> rw [ar, br] at step
  case ok.ok x t r u => cases r <;> first | contradiction | exact ⟨step, rfl⟩
  case error.ok e t r u => cases r <;> first | contradiction | exact ⟨step, rfl⟩
  all_goals contradiction

end WalRecoverySlice.Segmented.Native.AppendIO
