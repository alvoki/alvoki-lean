import Init.System.IO

namespace Alvoki.NativePost

abbrev W := Void IO.RealWorld
abbrev F := ExceptT String IO

/-- Both error channels retain the world at which the operation stopped.
The success predicate can depend on the returned value and the reached world. -/
def Returns (action : F α) (start : W) (ok : α → W → Prop) (failed : W → Prop) : Prop :=
  match action.run start with
  | .error _ reached | .ok (.error _) reached => failed reached
  | .ok (.ok value) reached => ok value reached

theorem Returns.bind {a : F α} {f : α → F β}
    (first : Returns a start middle failed)
    (next : ∀ x w, middle x w → Returns (f x) w done failed) :
    Returns (a >>= f) start done failed := by
  unfold Returns at *
  rw [ExceptT.run_bind]
  cases ran : a.run start with
  | error e t =>
    rw [ran] at first
    simpa only [Bind.bind, instMonadEIO._aux_13, EST.bind, ran, Pure.pure, instMonadEIO._aux_5, EST.pure] using first
  | ok r t =>
    rw [ran] at first
    cases r with
    | error => simpa only [Bind.bind, instMonadEIO._aux_13, EST.bind, ran, Pure.pure, instMonadEIO._aux_5, EST.pure] using first
    | ok x => simpa only [Bind.bind, instMonadEIO._aux_13, EST.bind, ran] using next x t first

/-- A returned IO exception and an ExceptT error can be inspected separately
by callers which promise an exact public error. Both carry a reached world. -/
def IOReturns (a : IO α) (w : W) (ok : α → W → Prop) (failed : W → Prop) : Prop :=
  match a w with
  | .ok v t => ok v t
  | .error _ t => failed t

theorem Returns.liftIO {a : IO α} (h : IOReturns a w ok failed) :
    Returns (liftM a : F α) w ok failed := by
  unfold Returns IOReturns at *
  have lifted : (liftM a : F α).run = (do return (Except.ok (← a) : Except String α) : IO _) := rfl
  rw [lifted]
  cases ran : a w <;>
    simpa [Bind.bind, instMonadEIO._aux_13, EST.bind, ran, Pure.pure, instMonadEIO._aux_5, EST.pure] using h

theorem IOReturns.bind {a : IO α} {f : α → IO β}
    (first : IOReturns a start middle failed)
    (next : ∀ x w, middle x w → IOReturns (f x) w done failed) :
    IOReturns (a >>= f) start done failed := by
  unfold IOReturns at *
  cases ran : a start with
  | error e t =>
    rw [ran] at first
    simpa only [Bind.bind, instMonadEIO._aux_13, EST.bind, ran] using first
  | ok x t =>
    rw [ran] at first
    simpa only [Bind.bind, instMonadEIO._aux_13, EST.bind, ran] using next x t first

theorem Returns.mapPost {done : α → W → Prop} {failed : W → Prop} {ok : α → W → Prop} {fail : W → Prop}
    (step : Returns a w ok fail) (success : ∀ x t, ok x t → done x t)
    (failure : ∀ t, fail t → failed t) : Returns a w done failed := by
  unfold Returns at *
  cases ran : a.run w with
  | error e t => rw [ran] at step; exact failure _ step
  | ok r t =>
    rw [ran] at step
    cases r with
    | error => exact failure _ step
    | ok x => exact success _ _ step

end Alvoki.NativePost
