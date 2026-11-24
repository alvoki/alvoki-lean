import Alvoki.Storage.Disk.WalSegmentBoundedOpen

namespace Alvoki.Storage.WalSegmentRepair

open System

private def countCall {α : Type} (result : α) : EStateM IO.Error Nat α :=
  fun calls => .ok result (calls + 1)

private theorem countRepairActions (directory : DiskDirectory) (plan : Plan)
    (actions : List Step) (before : Nat) :
    (actions.forM (performPaths directory plan (fun _ => countCall (.ok ())) throw
      (fun _ _ => countCall ()) (fun _ => countCall ()) (fun _ _ => countCall ()))) before =
      .ok () (before + actions.length) := by
  induction actions generalizing before with
  | nil => simp [List.forM, Pure.pure, EStateM.pure]
  | cons action rest ih =>
    have one : performPaths directory plan (fun _ => countCall (.ok ())) throw
        (fun _ _ => countCall ()) (fun _ => countCall ()) (fun _ _ => countCall ()) action before =
        .ok () (before + 1) := by
      cases action with
      | replace step => cases step <;> rfl
      | unlink _ | syncPruned | syncKeeper => rfl
    simp only [List.forM, Bind.bind, EStateM.bind, one, ih, List.length_cons]
    congr 1
    omega

/-- Interpret each repair callback as one successful operation. -/
def countBoundedRepairCallbacks (directory : DiskDirectory) (plan : Plan) (physicalSize : Nat) : Except IO.Error Nat :=
  match finishBoundedMarkedOpen directory plan physicalSize (fun _ => countCall (.ok ()))
      (fun _ _ => countCall ()) (fun _ => countCall ()) (fun _ _ => countCall ()) 0 with
  | .ok () count => .ok count
  | .error error _ => .error error

private theorem finishBoundedMarkedOpen_count (directory : DiskDirectory) (plan : Plan) (physicalSize before : Nat)
    (valid : plan.valid = true) (prefixSize : plan.keeperBytes.size = plan.keeperSize)
    (fits : plan.keeperSize ≤ physicalSize) :
    finishBoundedMarkedOpen directory plan physicalSize (fun _ => countCall (.ok ()))
        (fun _ _ => countCall ()) (fun _ => countCall ()) (fun _ _ => countCall ()) before =
      .ok () (before + if plan.newer.isEmpty && physicalSize == plan.keeperSize then 2
        else plan.newer.length + if plan.keeperSize < physicalSize then 6 else 3) := by
  unfold finishBoundedMarkedOpen
  simp only [valid, prefixSize, beq_self_eq_true, Bool.true_and, decide_eq_true fits, ↓reduceIte, Bind.bind]
  split
  · rfl
  · unfold runRepairPlan
    simp only [Bind.bind, EStateM.bind, countCall, countRepairActions, steps, List.length_append,
      List.length_map, List.length_singleton]
    by_cases clipped : plan.keeperSize < physicalSize <;> simp [clipped, Publication.steps] <;> omega

/-- A healthy bounded repair runs two callbacks for an aligned keeper
with no later names. Otherwise it unlinks the observed later names and
makes at most six more callbacks. The physical keeper size selects the
replacement route, independently of the truncated prefix read. -/
theorem countBoundedRepairCallbacks_exact (directory : DiskDirectory) (plan : Plan) (physicalSize : Nat)
    (valid : plan.valid = true) (prefixSize : plan.keeperBytes.size = plan.keeperSize)
    (fits : plan.keeperSize ≤ physicalSize) :
    countBoundedRepairCallbacks directory plan physicalSize =
      .ok (if plan.newer.isEmpty && physicalSize == plan.keeperSize then 2
        else plan.newer.length + if plan.keeperSize < physicalSize then 6 else 3) := by
  unfold countBoundedRepairCallbacks
  rw [finishBoundedMarkedOpen_count directory plan physicalSize 0 valid prefixSize fits, Nat.zero_add]

theorem countBoundedRepairCallbacks_bound (directory : DiskDirectory) (plan : Plan) (physicalSize : Nat)
    (valid : plan.valid = true) (prefixSize : plan.keeperBytes.size = plan.keeperSize)
    (fits : plan.keeperSize ≤ physicalSize) :
    ∃ count, countBoundedRepairCallbacks directory plan physicalSize = .ok count ∧ count ≤ plan.newer.length + 6 := by
  rw [countBoundedRepairCallbacks_exact directory plan physicalSize valid prefixSize fits]
  refine ⟨_, rfl, ?_⟩
  split
  · omega
  · split <;> omega

end Alvoki.Storage.WalSegmentRepair
