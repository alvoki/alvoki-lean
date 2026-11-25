import Alvoki.Storage.Disk.CheckpointFileDispatch

namespace Alvoki.Storage.CheckpointPublication

/-- Every reached write and file-sync pair composes into the exact run
prefix, before the first directory barrier is called. -/
theorem runSteps_returned {state : Type} (perform : Step → EStateM IO.Error state Unit)
    (count : Nat) (atRun : Nat → state)
    (pairs : ∀ index < count,
      (perform (.writeRun index) >>= fun _ => perform (.syncRun index)) (atRun index) =
        .ok () (atRun (index + 1))) :
    ((runSteps count).forM perform) (atRun 0) = .ok () (atRun count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have prior := ih (fun index within => pairs index (Nat.lt_succ_of_lt within))
    rw [show runSteps (count + 1) = runSteps count ++ [.writeRun count, .syncRun count] by
      simp [runSteps, List.range_succ], List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM]
    change EStateM.bind ((runSteps count).forM perform)
      (fun _ => ([Step.writeRun count, .syncRun count].forM perform)) (atRun 0) = _
    rw [show ([Step.writeRun count, .syncRun count].forM perform) =
      (perform (.writeRun count) >>= fun _ => perform (.syncRun count)) by
      simp [List.forM_eq_forM, List.forM_cons, List.forM_nil]]
    simp only [EStateM.bind, prior, pairs count (Nat.lt_succ_self count)]

end Alvoki.Storage.CheckpointPublication
