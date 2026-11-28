import Alvoki.Experiments.WAL.Segmented.Native
import Alvoki.Checks.Audit.AxiomPolicy

namespace L0Audit
open WalRecoverySlice.Segmented.Native

/-- The old contract alone suffices. Only its set and read fields are used. -/
theorem phaseMemory_uninhabited : ¬ Nonempty PhaseMemory := by
  rintro ⟨heap⟩
  let W := Void IO.RealWorld
  let w₀ : W := Classical.choice inferInstance
  let r : IO.Ref (W → Bool) :=
    ((IO.mkRef (fun _ : W => false) : BaseIO (IO.Ref (W → Bool))) w₀).val
  let f : W → Bool := fun w => !(((r.get : BaseIO (W → Bool)) w).val w)
  let u : W := ((r.set f : BaseIO Unit) w₀).state
  have held : heap.holds r f u := heap.set r f w₀
  have readEq : ((r.get : BaseIO (W → Bool)) u).val = f := (heap.read held).1
  let b : Bool := ((r.get : BaseIO (W → Bool)) u).val u
  have impossible : b = !b := congrFun readEq u
  exact (show ∀ x : Bool, x ≠ !x from fun x => by cases x <;> decide) b impossible

#check_axioms phaseMemory_uninhabited

/-- Restricting only set does not suffice: allocation and read alone
encode the diagonal predicate on (address, world). -/
private abbrev W := Void IO.RealWorld

theorem unrestrictedAllocationFalse (heap : PhaseMemory) : False := by
  classical
  let A := ST.RefPointed.type × W
  let observed : A → (A → Prop) := fun s =>
    let r : IO.Ref (A → Prop) := ⟨s.1, inferInstance⟩
    ((r.get : BaseIO _) s.2).val
  let diag : A → Prop := fun x => ¬ observed x x
  let start : W := Classical.choice inferInstance
  let made := (IO.mkRef diag : BaseIO (IO.Ref (A → Prop))) start
  let p : A := ⟨made.val.ref, made.state⟩
  have fixed : observed p = diag := (heap.read (heap.allocate diag start)).1
  have no : (¬ observed p p) ↔ observed p p := (Iff.of_eq (congrFun fixed p)).symm
  exact (fun n => n (no.mp n)) (fun yes => no.mpr yes yes)

#check_axioms unrestrictedAllocationFalse

end L0Audit
