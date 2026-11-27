import Alvoki.Experiments.WAL.Segmented.Proofs.Publication
import Alvoki.Experiments.WAL.Segmented.Proofs.Invariant

namespace WalRecoverySlice.Segmented.Model

def initialControl (policy : Policy) (capacity : Nat) : Control := ⟨policy, capacity, 0, 0⟩

/-- Initialization installs an empty, durably named child before installing the
control record. Only a successful fresh creation returns a client handle. -/
theorem create_returns_ready (effects : Effects) (policy : Policy) {capacity : Nat}
    (positive : 0 < capacity) (fits : capacity ≤ 255) :
    let control := initialControl policy capacity
    DiskPost (fun ss disk =>
      ss = sessionOf control [] ∧ disk.liveControl = some control ∧
      disk.durableControl = some control ∧ ReadyLayout control [] disk)
      (fun _ => True) ((Segmented.create (ops effects) policy capacity).run {}) := by
  let c := initialControl policy capacity
  let initial : State := {}
  let named := (initial.disk.prepare 0 false).syncRoot
  change DiskPost _ _ ((Segmented.create (ops effects) policy capacity).run initial)
  have nonzero : capacity ≠ 0 := Nat.ne_of_gt positive
  have bounded : ¬capacity > 255 := Nat.not_lt.mpr fits
  simp only [Segmented.create, nonzero, bounded, decide_false, Bool.false_or, Bool.false_eq_true,
    ↓reduceIte]
  apply bindPost (P := fun _ d => ∃ persist, d = initial.disk.prepare 0 persist)
  · apply namespacePost (effects.prepare initial.step 0) (fun d flag => d.prepare 0 flag) initial
    · trivial
    · exact fun _ => trivial
    exact fun p => ⟨p, rfl⟩
  intro _ t ⟨p, prepared⟩
  apply bindPost (P := fun _ d => d = named)
  · apply barrierPost (effects.root t.step) Disk.syncRoot t
    · trivial
    · trivial
    rw [prepared]
    rfl
  intro _ u settled
  have cut := publish_cases effects c u
  apply bindPost (P := fun _ d => d = u.disk.published c)
  · change DiskPost _ _ ((Segmented.publish (ops effects) c).run u)
    generalize h : (Segmented.publish (ops effects) c).run u = result at cut ⊢
    cases result with
    | error => trivial
    | ok x _ => cases x with
      | error => trivial
      | ok => exact cut
  intro _ v published
  change _ ∧ v.disk.liveControl = some c ∧ v.disk.durableControl = some c ∧ ReadyLayout c [] v.disk
  rw [published, settled]
  refine ⟨by simp [sessionOf, segmentHistory, historyView, initialControl], rfl, rfl, ?_⟩
  have layout : Layout c [] (named.published c) := by
    refine ⟨positive, fits, ?_, ?_, Nat.le_refl 0, by simp, ?_, ?_⟩
    · simp [c, initialControl]
    · simp
    · intro id chosen
      have zero : id = 0 := Nat.eq_zero_of_le_zero chosen.2
      subst id
      exact ⟨List.Mem.head _, List.Mem.head _⟩
    · intro id _ sealed
      exact False.elim (Nat.not_lt_zero id sealed)
  have empty : segmentHistory c.capacity c.active [] = [] := by simp [segmentHistory]
  refine ⟨layout, ?_, rfl, ?_⟩ <;> rw [empty]
  · exact Persistence.fresh_ready policy
  · rfl

/-- The healthy initialization path is inhabited for every supported capacity. -/
theorem create_healthy (policy : Policy) {capacity : Nat} (positive : 0 < capacity) (fits : capacity ≤ 255) :
    ∃ state, (Segmented.create (ops healthy) policy capacity).run {} =
      .ok (.ok (sessionOf (initialControl policy capacity) [])) state := by
  have nonzero : capacity ≠ 0 := Nat.ne_of_gt positive
  have bounded : ¬capacity > 255 := Nat.not_lt.mpr fits
  simp only [Segmented.create, nonzero, bounded, decide_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  simp only [sessionOf, segmentHistory, List.drop_nil, List.take_nil, List.length_nil, historyView]
  exact ⟨_, rfl⟩

end WalRecoverySlice.Segmented.Model
