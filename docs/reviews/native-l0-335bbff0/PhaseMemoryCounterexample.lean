import Alvoki.Experiments.WAL.Segmented.Native
import Alvoki.Checks.Audit.AxiomPolicy

open WalRecoverySlice.Segmented.Native

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

#print axioms phaseMemory_uninhabited

#check_axioms phaseMemory_uninhabited
