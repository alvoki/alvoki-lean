import Alvoki.Experiments.WAL.Segmented.Native
import Alvoki.Checks.Audit.AxiomPolicy

namespace NativeArchitectureAudit
open WalRecoverySlice.Segmented.Native
private abbrev W := Void IO.RealWorld

/-- At a fixed reference, unrestricted set followed by read would make
every Boolean predicate on worlds retrievable from some world. -/
theorem phaseMemoryImpossible (heap : PhaseMemory) : False := by
  let w : W := Classical.choice inferInstance
  let r := ((IO.mkRef (fun _ : W => false) : BaseIO (IO.Ref (W → Bool))) w).val
  let observe := fun t : W => ((r.get : BaseIO (W → Bool)) t).val
  let diagonal := fun t : W => !(observe t t)
  let t := ((r.set diagonal : BaseIO Unit) w).state
  have eq : observe t = diagonal := (heap.read (heap.set r diagonal w)).1
  have bad : observe t t = !(observe t t) := congrFun eq t
  cases h : observe t t <;> simp [h] at bad

#check_axioms phaseMemoryImpossible
end NativeArchitectureAudit
