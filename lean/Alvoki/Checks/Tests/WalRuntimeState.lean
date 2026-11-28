import Alvoki.Checks.Audit.AxiomPolicy
import Alvoki.Experiments.WAL.Segmented.Proofs.Invariant

/-! Design checks for projecting positions and folding a replay suffix.
The native and model schedules are unchanged by this file. -/
namespace WalRecoverySlice.Segmented.RuntimeStateDesign

open WalRecoverySlice.Segmented.Contract

theorem installed_bounds {s : Session} {disk : Model.Disk} (installed : Installed s disk) :
    s.control.discarded = s.view.base ∧ s.tailPosition = s.view.tail ∧
      s.control.discarded ≤ s.tailPosition ∧ s.activeCount ≤ s.control.capacity := by
  obtain ⟨history, shape, ready, _, _⟩ := installed
  have lower := ready.layout.lower
  have covered := ready.layout.discardedFits
  have count := segmentHistory_active_length
    (active := s.control.active) ready.layout.upper
  have fits := segmentHistory_fits s.control.capacity s.control.active history
  have physicalTail : s.control.active * s.control.capacity +
      (segmentHistory s.control.capacity s.control.active history).length = history.length := by
    rw [count]
    omega
  rw [shape]
  simp only [sessionOf, Session.tailPosition]
  rw [physicalTail, historyView_tail covered]
  exact ⟨rfl, rfl, covered, fits⟩

/-- The published successor can be empty at a crash cut. Absolute positions
do not advance until the first append to that successor succeeds. -/
theorem empty_successor_tail (active capacity : Nat) :
    (active + 1) * capacity + 0 = active * capacity + capacity := by
  simp [Nat.add_mul]

/-- A design model of a left-to-right consumer. Input starts just after
`base`. Use the next position to decide whether to fold each batch. -/
def foldAfter (step : α → Batch → α) (through base : Nat) (acc : α) : List Batch → α
  | [] => acc
  | batch :: rest =>
    let position := base + 1
    foldAfter step through position (if through < position then step acc batch else acc) rest

theorem foldAfter_eq (step : α → Batch → α) (through base : Nat) (acc : α)
    (batches : List Batch) :
    foldAfter step through base acc batches = (batches.drop (through - base)).foldl step acc := by
  induction batches generalizing base acc with
  | nil => simp [foldAfter]
  | cons batch rest ih =>
    rw [foldAfter, ih]
    by_cases seen : through < base + 1
    · have zero : through - base = 0 := by omega
      have nextZero : through - (base + 1) = 0 := by omega
      simp [seen, zero, nextZero]
    · have dropHead : through - base = (through - (base + 1)) + 1 := by omega
      simp [seen, dropHead]

end WalRecoverySlice.Segmented.RuntimeStateDesign

#check_axioms WalRecoverySlice.Segmented.RuntimeStateDesign.installed_bounds
#check_axioms WalRecoverySlice.Segmented.RuntimeStateDesign.empty_successor_tail
#check_axioms WalRecoverySlice.Segmented.RuntimeStateDesign.foldAfter_eq
