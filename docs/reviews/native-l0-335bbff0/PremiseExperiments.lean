import Alvoki.Experiments.WAL.Segmented.Native
import Alvoki.Checks.Audit.AxiomPolicy

namespace NativeL0Audit

/-- One reader from a fixed state space cannot return every Boolean predicate
on that same state space, even if the state producing each result is chosen freely. -/
theorem noUniversalReader (W : Type) (observe : W → W → Bool) :
    ¬ (∀ f : W → Bool, ∃ u, observe u = f) := by
  intro allValues
  obtain ⟨u, hu⟩ := allValues (fun w => !(observe w w))
  have bad : observe u u = !(observe u u) := congrFun hu u
  cases eq : observe u u <;> simp [eq] at bad

/-- Restricting set to an already allocated, live slot does not help if all
higher-order payloads are still admitted. Use an effect type as the payload. -/
theorem noLiveActionSlot
    (r : IO.Ref (BaseIO Bool)) (live : Void IO.RealWorld → Prop)
    (start : Void IO.RealWorld) (atStart : live start)
    (roundTrip : ∀ (s : Void IO.RealWorld), live s → ∀ action : BaseIO Bool,
      let u := ((r.set action : BaseIO Unit) s).state
      ((r.get : BaseIO (BaseIO Bool)) u).val = action) : False := by
  let observe := fun (s w : Void IO.RealWorld) =>
    ((((r.get : BaseIO (BaseIO Bool)) s).val) w).val
  apply noUniversalReader _ observe
  intro f
  let action : BaseIO Bool := fun w => ⟨f w, w⟩
  let u := ((r.set action : BaseIO Unit) start).state
  refine ⟨u, ?_⟩
  funext w
  exact congrArg (fun a : BaseIO Bool => (a w).val) (roundTrip start atStart action)

/-- A small closed family with two payload types and an explicit shared store. -/
structure Store where
  phase : Bool
  cursor : Nat

structure Slots where
  readPhase : Store → Bool
  setPhase : Bool → Store → Store
  readCursor : Store → Nat
  setCursor : Nat → Store → Store

structure SlotLaws (ops : Slots) : Prop where
  phaseAfterSet : ∀ s b, ops.readPhase (ops.setPhase b s) = b
  cursorAfterSet : ∀ s n, ops.readCursor (ops.setCursor n s) = n
  phaseFrame : ∀ s n, ops.readPhase (ops.setCursor n s) = ops.readPhase s
  cursorFrame : ∀ s b, ops.readCursor (ops.setPhase b s) = ops.readCursor s

def slots : Slots :=
  ⟨Store.phase, fun b s => {s with phase := b},
   Store.cursor, fun n s => {s with cursor := n}⟩

theorem slotLaws : SlotLaws slots :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem jointWitness : ∃ ops : Slots, SlotLaws ops ∧
    ∃ s : Store, ops.readPhase (ops.setCursor 7 (ops.setPhase true s)) = true ∧
      ops.readCursor (ops.setCursor 7 (ops.setPhase true s)) = 7 :=
  ⟨slots, slotLaws, ⟨false, 0⟩, rfl, rfl⟩

/-- A broken cursor write passes its own read-after-write check but destroys
the other slot. The joint package must reject this interpreter. -/
def clobber : Slots := { slots with setCursor := fun n _ => ⟨false, n⟩ }

theorem clobberCursorRoundTrip (s : Store) (n : Nat) :
    clobber.readCursor (clobber.setCursor n s) = n := rfl

theorem rejectClobber : ¬ SlotLaws clobber := by
  intro laws
  have bad : false = true := laws.phaseFrame ⟨true, 0⟩ 7
  contradiction

#check_axioms noUniversalReader
#check_axioms noLiveActionSlot
#check_axioms jointWitness
#check_axioms rejectClobber

end NativeL0Audit
