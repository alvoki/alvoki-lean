import Alvoki.Storage.Disk.WAL.WalSegmentBoundedOpen
import Alvoki.Storage.Disk.RecoveryRequestCount

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

open RecoveryRequestCount in
private theorem repairStep_requestBound (dir : DiskDirectory) (plan : Plan)
    (removeFile : FilePath → Except IO.Error (Except IO.Error Unit)) (write : FilePath → ByteArray → Except IO.Error Unit)
    (sync : Array FilePath → Except IO.Error Unit) (renameFile : FilePath → FilePath → Except IO.Error Unit)
    (step : Step) (before : Nat) :
    reached (performPaths dir plan (fun path => issued (removeFile path)) throw
      (fun path bytes => issued (write path bytes)) (fun paths => issued (sync paths))
      (fun source dest => issued (renameFile source dest)) step before) ≤ before + 1 := by
  cases step with
  | unlink first =>
    unfold performPaths RunCollection.performPaths
    change reached (((issued (removeFile (dir.file (.walSegment first)))) >>= _) before) ≤ _
    rw [show before + 1 = before + (1 + 0) from rfl]
    apply bind_bound (by simp only [reached_issued, Nat.le_refl])
    intro report count _
    cases RunCollection.ownedUnlinkResult report <;> exact Nat.le_refl _
  | syncPruned | syncKeeper => simp [performPaths, reached_issued]
  | replace step => cases step <;> simp [performPaths, Publication.performReplacement, reached_issued]

open RecoveryRequestCount in
/-- The shared repair issues at most one unlink per later WAL name and six
further requests. A rejecting plan or error exit obeys the same budget. -/
theorem finishBoundedMarkedOpen_requestBound (dir : DiskDirectory) (plan : Plan) (physicalSize : Nat)
    (removeFile : FilePath → Except IO.Error (Except IO.Error Unit)) (write : FilePath → ByteArray → Except IO.Error Unit)
    (sync : Array FilePath → Except IO.Error Unit) (renameFile : FilePath → FilePath → Except IO.Error Unit)
    (before : Nat) :
    reached (finishBoundedMarkedOpen dir plan physicalSize (fun path => issued (removeFile path))
      (fun path bytes => issued (write path bytes)) (fun paths => issued (sync paths))
      (fun source dest => issued (renameFile source dest)) before) ≤ before + (plan.newer.length + 6) := by
  unfold finishBoundedMarkedOpen
  by_cases valid : (plan.valid && plan.keeperBytes.size == plan.keeperSize && decide (plan.keeperSize ≤ physicalSize)) = true
  · simp only [ite_eq_left valid]
    split
    · have counted : reached (((issued (sync #[dir.path])) >>= fun _ =>
          issued (sync #[dir.file (.walSegment plan.keeper)])) before) ≤ before + (1 + 1) :=
        bind_bound (by simp only [reached_issued, Nat.le_refl]) (fun _ _ _ => by simp only [reached_issued, Nat.le_refl])
      exact Nat.le_trans counted (by omega)
    · unfold runRepairPlan
      rw [show plan.newer.length + 6 = 1 + (plan.newer.length + 5) by omega]
      apply bind_bound (first := 1) (second := plan.newer.length + 5)
      · simp only [reached_issued, Nat.le_refl]
      · intro _ after _
        have bounded := forM_bound _ (steps plan.newer (decide (plan.keeperSize < physicalSize))) after 1
          (repairStep_requestBound dir plan removeFile write sync renameFile)
        have total : (steps plan.newer (decide (plan.keeperSize < physicalSize))).length ≤ plan.newer.length + 5 := by
          by_cases clipped : plan.keeperSize < physicalSize <;> simp [steps, Publication.steps, clipped] <;> omega
        exact Nat.le_trans bounded (by omega)
  · simp [valid, Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw, reached]

end Alvoki.Storage.WalSegmentRepair
