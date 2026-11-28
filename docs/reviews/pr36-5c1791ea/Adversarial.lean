import OwnedRoleModel
import Alvoki.Checks.Audit.AxiomPolicy

namespace PR36Audit
open L0Audit.OwnedRoleModel
open WalRecoverySlice.Segmented (Session)

private def vacant : Cell := ⟨0, none⟩
private def active : Key := ⟨0, 1, .active⟩
private def abandoned : Key := ⟨1, 1, .phase⟩
private def blocker : Key := ⟨2, 1, .mutex⟩
private def current : Key := ⟨3, 1, .phase⟩
private def gate : Key := ⟨2, 2, .mutex⟩
private def oldChild : Key := ⟨4, 1, .child⟩
private def selected : Key := ⟨5, 1, .child⟩
private def initial : Session := ⟨⟨.logOnly, 1, 0, 0⟩, 0, ⟨0, []⟩⟩
private def afterOne (b : WalRecoverySlice.Bytes) : Session :=
  ⟨initial.control, 1, initial.view.append b⟩

/-- A phase allocation lost on the failure path is still readable by its
predictable key. Combining it with the mutex of the successful retry spends
the active child twice while both phase snapshots report just one append. -/
theorem abandonedPhaseSkipsRotation :
    ∃ a b c start failed free ready first second,
      allocate (List.replicate 6 vacant) 0 (.active none) = some (active, a) ∧
      allocate a 2 (.mutex true) = some (blocker, b) ∧
      allocate b 4 (.child []) = some (oldChild, c) ∧
      allocate c 5 (.child []) = some (selected, start) ∧
      install active initial oldChild start = .error () failed ∧
      read failed active = some (.active none) ∧
      release failed blocker = some free ∧
      installAt 3 2 active initial selected free = .ok (current, gate) ready ∧
      appendUsing (current, gate) selected [11] ready = .ok (afterOne [11]) first ∧
      appendUsing (abandoned, gate) selected [22] first = .ok (afterOne [22]) second ∧
      read second selected = some (.child [[11], [22]]) ∧
      read second current = some (.phase (.ready active (afterOne [11]))) ∧
      read second abandoned = some (.phase (.ready active (afterOne [22]))) := by
  exact ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Role checking is shallow: installation accepts a self-reference as the child. -/
theorem installPointsAtActiveSlot :
    ∃ h t, allocate (List.replicate 3 vacant) 0 (.active none) = some (active, h) ∧
      install active initial active h = .ok (abandoned, blocker) t ∧
      read t active = some (.active (some (0, active))) :=
  ⟨_, _, rfl, rfl, rfl⟩

/-- On live cells only, this reader ignores the generation. -/
def generationBlind (h : Heap) (k : Key) : Option Value := do
  let cell ← h[k.slot]?
  let value ← cell.contents
  if value.role = k.role then some value else none

theorem generationBlindContract :
    Contract Heap Owns generationBlind write release allocate Free := by
  refine ⟨?_, realized.modify, ?_, realized.acquire⟩
  · intro h k v held
    simp [generationBlind, held.1, held.2]
  · intro h k v held
    obtain ⟨t, dropped, free, _, kept⟩ := realized.dispose held
    have empty : t[k.slot]? = some ⟨k.epoch, none⟩ := free
    exact ⟨t, dropped, free, by simp [generationBlind, empty], kept⟩

theorem blindStaleRead :
    ∃ h t u, allocate [vacant] 0 (.active none) = some (active, h) ∧
      release h active = some t ∧ read t active = none ∧
      allocate t 0 (.active none) = some (⟨0, 2, .active⟩, u) ∧
      read u active = none ∧ generationBlind u active = some (.active none) :=
  ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Concrete identity forgery needs no wrong epoch or invalid role. -/
theorem duplicateAndRelease :
    ∃ h empty, allocate [vacant] 0 (.active none) = some (active, h) ∧
      Owns h active (.active none) ∧ Owns h ⟨0, 1, .active⟩ (.active none) ∧
      release h ⟨0, 1, .active⟩ = some empty ∧ read empty active = none :=
  ⟨_, _, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl⟩

/-- A token plus an event/world side table still cannot decode every predicate
on that very observation domain, even if payloads are first-order tokens. -/
theorem noTotalRoundTrip {Index : Type} (decode : Index → Index → Bool)
    (all : ∀ f : Index → Bool, ∃ i, decode i = f) : False := by
  obtain ⟨i, eq⟩ := all (fun j => !(decode j j))
  have impossible : decode i i = !(decode i i) := congrFun eq i
  cases h : decode i i <;> simp [h] at impossible

#check_axioms abandonedPhaseSkipsRotation
#check_axioms installPointsAtActiveSlot
#check_axioms generationBlindContract
#check_axioms blindStaleRead
#check_axioms duplicateAndRelease
#check_axioms noTotalRoundTrip

end PR36Audit
