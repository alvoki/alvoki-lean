import Alvoki.Experiments.DurableBlob.Proofs

/-! Small checks of the two VCGs and the nested outcome stack used by WAL. -/
namespace DurableBlob.WPComparison

def late : EStateM Unit Image Unit := do
  modify Image.barrier
  throw ()

section
open Std.Do

set_option linter.deprecated.syntax false in
theorem legacy (before : Image) :
    Std.Do.Triple late (fun s => ⌜s = before⌝)
      (post⟨fun _ _ => ⌜False⌝, fun _ s => ⌜s = before.barrier⌝⟩) := by
  mvcgen [late]
  all_goals grind

end

open Std.WP Lean.Order
set_option experimental.vcgen true

theorem current (before : Image) :
    ⦃fun s => s = before⦄ late ⦃fun _ _ => False; fun _ s => s = before.barrier⦄ := by
  vcgen [late] with finish

abbrev Nested := ExceptT String (EStateM Unit Image)

-- The two error posts apply to different constructors of the actual result.
theorem nested_result (action : Nested α) (P : Image → Prop)
    (Q : α → Image → Prop) (F : String → Image → Prop) (I : Unit → Image → Prop)
    (spec : Std.WP.Triple action P Q (F, I)) (s : Image) (pre : P s) :
    match action.run s with
    | .ok (.ok v) after => Q v after
    | .ok (.error e) after => F e after
    | .error interrupted after => I interrupted after := by
  have reached := spec.le_wp s pre
  rw [ExceptT.wp_apply_eq] at reached
  cases ran : action.run s with
  | error => simpa [wp, WP.trans, ran] using reached
  | ok value after => cases value <;> simpa [wp, WP.trans, pushExcept, ran] using reached

theorem nested_stop (before : Image) :
    let action : Nested Unit := ExceptT.lift late
    Std.WP.Triple action (fun s => s = before)
      (fun _ _ => False) (fun _ _ => False, fun _ s => s = before.barrier) := by
  dsimp only
  refine ⟨?_⟩
  intro s same
  subst s
  rfl

end DurableBlob.WPComparison
