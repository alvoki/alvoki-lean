import Alvoki.Storage.Disk.Proofs.WAL.LongWalBindingPublication

namespace Alvoki.Storage.WalSegmentRepair

open System

/-- The checked long-keeper prefix reaches the original replacement
continuation with the actual stage already written. Later callbacks
can return either success or error on that same execution. -/
theorem finishBoundedMarkedOpen_afterStage {heap : Type} (directory : DiskDirectory) (plan : Plan)
    (physicalSize : Nat) (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (valid : plan.valid = true) (size : plan.keeperBytes.size = plan.keeperSize)
    (longer : plan.keeperSize < physicalSize) {entry authorized pruned staged : heap}
    (authorize : sync #[directory.path] entry = .ok () authorized)
    (prune : ((plan.newer.map Step.unlink ++ [Step.syncPruned]).forM
      (performPaths directory plan remove throw write sync rename)) authorized = .ok () pruned)
    (written : write (directory.file .stagedWal) plan.keeperBytes pruned = .ok () staged) :
    let perform := performPaths directory plan remove throw write sync rename
    finishBoundedMarkedOpen directory plan physicalSize remove write sync rename entry =
      (do
        perform (.replace .syncStaged)
        perform (.replace .renameStaged)
        perform (.replace .syncDirectory)
        pure () : EStateM IO.Error heap Unit) staged := by
  intro perform
  rw [finishBoundedMarkedOpen_long directory plan physicalSize remove write sync rename valid size longer]
  change (do
    sync #[directory.path]
    ((plan.newer.map Step.unlink ++ [Step.syncPruned]).forM perform)
    perform (.replace .writeStaged)
    perform (.replace .syncStaged)
    perform (.replace .renameStaged)
    perform (.replace .syncDirectory)
    pure () : EStateM IO.Error heap Unit) entry = _
  change ((plan.newer.map Step.unlink ++ [Step.syncPruned]).forM perform) authorized = .ok () pruned at prune
  have exact : plan.keeperBytes.extract 0 plan.keeperSize = plan.keeperBytes := by
    rw [← size, ByteArray.extract_zero_size]
  have stagedWrite : perform (.replace .writeStaged) pruned = .ok () staged := by
    simp only [perform, performPaths, Publication.performReplacement, exact, written]
  simp only [Bind.bind, EStateM.bind, authorize, prune, stagedWrite]


namespace LongKeeperRepair

/-- Which exit of the replacement rename was reached in this repair.
A returned rename retains the heap used to issue the final directory sync. -/
inductive RenameOutcome (heap : Type) where
  | failed
  | returned (reached : heap)

/-- Record only the exit of the rename itself. The outer result still
carries the original diagnostic and the heap after any physical effects. -/
private def observe (action : EStateM IO.Error heap α) (recordRename : Bool := false) :
    EStateM IO.Error (heap × Option (RenameOutcome heap)) α := fun (before, prior) =>
  match action before with
  | .ok value after => .ok value (after, if recordRename then some (.returned after) else prior)
  | .error cause after => .error cause (after, if recordRename then some .failed else prior)

variable (dir : DiskDirectory) (plan : Plan) (extent : Nat)
  (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
  (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
  (sync : Array FilePath → EStateM IO.Error heap Unit)
  (rename : FilePath → FilePath → EStateM IO.Error heap Unit)

/-- The literal bounded finisher with one observation, initially absent. The
same rename on an earlier open cannot supply the returned heap. -/
def observeRename (start : heap) : EStateM.Result IO.Error (heap × Option (RenameOutcome heap)) Unit :=
  finishBoundedMarkedOpen dir plan extent (fun path => observe (remove path))
    (fun path bytes => observe (write path bytes)) (fun paths => observe (sync paths))
    (fun src dst => observe (rename src dst) true) (start, none)

private theorem observe_pure (value : α) :
    (pure value : EStateM IO.Error (heap × Option (RenameOutcome heap)) α) = observe (pure value) := rfl

private theorem observe_bind (action : EStateM IO.Error heap α) (next : α → EStateM IO.Error heap β) :
    (observe action >>= fun value => observe (next value)) = observe (action >>= next) := by
  funext pair
  rcases pair with ⟨before, prior⟩
  cases h : action before <;> simp [observe, Bind.bind, EStateM.bind, h]

local notation "perform" => performPaths dir plan remove throw write sync rename
local notation "seen" => performPaths dir plan (fun path => observe (remove path)) throw
  (fun path bytes => observe (write path bytes)) (fun paths => observe (sync paths))
  (fun src dst => observe (rename src dst) true)

private theorem observeUnlink (first : Nat) : seen (.unlink first) = observe (perform (.unlink first)) := by
  funext pair
  rcases pair with ⟨before, prior⟩
  cases h : remove (dir.file (.walSegment first)) before with
  | error cause reached => simp [performPaths, RunCollection.performPaths, Bind.bind, EStateM.bind, observe, h]
  | ok report reached =>
    cases accepted : RunCollection.ownedUnlinkResult report <;>
      simp [performPaths, RunCollection.performPaths, Bind.bind, EStateM.bind, observe, h, accepted,
        Pure.pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

private theorem observePrune (newer : List Nat) :
    ((newer.map Step.unlink ++ [Step.syncPruned]).forM seen) =
      observe ((newer.map Step.unlink ++ [Step.syncPruned]).forM perform) := by
  induction newer with
  | nil => change (observe (sync #[dir.path]) >>= fun _ => pure ()) = _
           rw [observe_pure, observe_bind]
           rfl
  | cons first tail ih =>
    simp only [List.map_cons, List.cons_append]
    change (seen (.unlink first) >>= fun _ => _) = observe (perform (.unlink first) >>= fun _ => _)
    rw [ih, observeUnlink, observe_bind]

/-- Only replacement can record a rename. An invalid extent, the aligned
fast path, and a prune followed by an ordinary keeper sync preserve the
initial empty observation, even when one of their calls fails. -/
theorem longerOfObservedRenameError
    (valid : plan.valid = true) (size : plan.keeperBytes.size = plan.keeperSize)
    {start reached : heap} {outcome : RenameOutcome heap} {cause : IO.Error}
    (observed : observeRename dir plan extent remove write sync rename start = .error cause (reached, some outcome)) :
    plan.keeperSize < extent := by
  apply Classical.byContradiction
  intro short
  by_cases fits : plan.keeperSize ≤ extent
  · have eq := Nat.le_antisymm fits (Nat.le_of_not_gt short)
    subst extent
    unfold observeRename at observed
    simp only [finishBoundedMarkedOpen, valid, size, beq_self_eq_true, Nat.le_refl, decide_true,
      Bool.and_self, Bool.and_true, Nat.lt_irrefl, decide_false] at observed
    by_cases empty : plan.newer.isEmpty = true
    · simp only [empty, ite_true] at observed
      cases first : sync #[dir.path] start <;> simp [observe, Bind.bind, EStateM.bind, first] at observed
      rename_i after
      cases last : sync #[dir.file (.walSegment plan.keeper)] after <;> simp [last] at observed
    · have remainder : (steps plan.newer false).forM seen = (do
          observe ((plan.newer.map Step.unlink ++ [Step.syncPruned]).forM perform)
          seen Step.syncKeeper
          pure () : EStateM IO.Error (heap × Option (RenameOutcome heap)) Unit) := by
        unfold steps
        simp only [Bool.false_eq_true, ite_false]
        rw [List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM,
          observePrune dir plan remove write sync rename]
        rfl
      simp only [empty, Bool.false_eq_true, ite_false, ite_true, runRepairPlan, remainder] at observed
      generalize ((plan.newer.map Step.unlink ++ [Step.syncPruned]).forM perform) = prune at observed
      cases first : sync #[dir.path] start <;> simp [observe, Bind.bind, EStateM.bind, first] at observed
      rename_i after
      cases cut : prune after <;> simp [cut] at observed
      rename_i pruned
      cases last : sync #[dir.file (.walSegment plan.keeper)] pruned <;>
        simp [performPaths, observe, last, Pure.pure, EStateM.pure] at observed
  · simp [observeRename, finishBoundedMarkedOpen, valid, size, fits, Bind.bind, EStateM.bind, throw,
      throwThe, MonadExceptOf.throw, EStateM.throw] at observed

/-- The literal prefix from repair entry through staging-file sync. Physical
frame laws at staging or rename can be restricted to these reached heaps. -/
def StagedFrom (start authorized pruned staged synced : heap) : Prop :=
    sync #[dir.path] start = .ok () authorized ∧
    ((plan.newer.map Step.unlink ++ [Step.syncPruned]).forM perform) authorized = .ok () pruned ∧
    write (dir.file .stagedWal) plan.keeperBytes pruned = .ok () staged ∧
    sync #[dir.file .stagedWal] staged = .ok () synced

/-- Both rename outcomes share the literal authorization, prune, write and
file sync. Only a returned rename can reach the final directory group. -/
theorem observeRename_error_iff
    (valid : plan.valid = true) (size : plan.keeperBytes.size = plan.keeperSize)
    (long : plan.keeperSize < extent) {start reached : heap} {outcome : RenameOutcome heap} {cause : IO.Error} :
    observeRename dir plan extent remove write sync rename start = .error cause (reached, some outcome) ↔
      ∃ authorized pruned staged synced,
        StagedFrom dir plan remove write sync rename start authorized pruned staged synced ∧
        match outcome with
        | .failed => rename (dir.file .stagedWal) (dir.file (.walSegment plan.keeper)) synced = .error cause reached
        | .returned renamed => rename (dir.file .stagedWal) (dir.file (.walSegment plan.keeper)) synced = .ok () renamed ∧
            sync #[dir.path] renamed = .error cause reached := by
  unfold StagedFrom observeRename
  simp only [and_assoc]
  rw [finishBoundedMarkedOpen_long _ _ _ _ _ _ _ valid size long]
  have bytes : plan.keeperBytes.extract 0 plan.keeperSize = plan.keeperBytes := by
    rw [← size, ByteArray.extract_zero_size]
  simp only [observePrune, performPaths, Publication.performReplacement, bytes]
  generalize pruneEq : ((plan.newer.map Step.unlink ++ [Step.syncPruned]).forM
    (performPaths dir plan remove throw write sync rename)) = prune
  simp only [Bind.bind, EStateM.bind]
  cases authorized : sync #[dir.path] start <;> simp [observe, authorized]
  rename_i authed
  cases pruned : prune authed <;> simp
  rename_i prunedHeap
  cases staged : write (dir.file .stagedWal) plan.keeperBytes prunedHeap <;> simp
  rename_i stagedHeap
  cases synced : sync #[dir.file .stagedWal] stagedHeap <;> simp
  rename_i syncedHeap
  cases moved : rename (dir.file .stagedWal) (dir.file (.walSegment plan.keeper)) syncedHeap with
  | error diagnostic after => cases outcome <;> simp
  | ok value renamed =>
    cases final : sync #[dir.path] renamed <;> cases outcome <;>
      simp_all [Pure.pure, EStateM.pure, and_comm, and_assoc] <;>
      rintro rfl <;> simp [final, and_comm]

/-- Forget the repair-local rename observation while retaining the native
return or error and the exact heap, including effects before an error. -/
def forgetRename : EStateM.Result IO.Error (heap × Option (RenameOutcome heap)) α → EStateM.Result IO.Error heap α
  | .ok value (after, _) => .ok value after
  | .error cause (after, _) => .error cause after

/-- An observed action projects to the same return and heap for every incoming observation. -/
def Erases (tagged : EStateM IO.Error (heap × Option (RenameOutcome heap)) α) (ordinary : EStateM IO.Error heap α) : Prop :=
  ∀ before prior, forgetRename (tagged (before, prior)) = ordinary before

theorem Erases.bind {tagged : EStateM IO.Error (heap × Option (RenameOutcome heap)) α} {ordinary : EStateM IO.Error heap α}
    {nextTagged : α → EStateM IO.Error (heap × Option (RenameOutcome heap)) β} {next : α → EStateM IO.Error heap β}
    (first : Erases tagged ordinary) (later : ∀ x, Erases (nextTagged x) (next x)) :
    Erases (tagged >>= nextTagged) (ordinary >>= next) := by
  intro before prior
  have same := first before prior
  cases step : tagged (before, prior) with
  | error cause pair =>
    obtain ⟨after, memo⟩ := pair
    simp only [step, forgetRename] at same
    simp [Bind.bind, EStateM.bind, step, ← same, forgetRename]
  | ok value pair =>
    obtain ⟨after, memo⟩ := pair
    simp only [step, forgetRename] at same
    simpa only [Bind.bind, EStateM.bind, step, ← same] using later value after memo

private theorem eraseObserved (action : EStateM IO.Error heap α) (record : Bool) :
    Erases (observe action record) action := by
  intro before prior
  cases h : action before <;> simp [observe, h, forgetRename]

private theorem eraseSteps (steps : List Step) : Erases (steps.forM seen) (steps.forM perform) := by
  induction steps with
  | nil => exact fun _ _ => rfl
  | cons step tail ih =>
    change Erases (seen step >>= fun _ => _) (perform step >>= fun _ => _)
    apply Erases.bind _ (fun _ => ih)
    cases step with
    | unlink first =>
      rw [observeUnlink]
      exact eraseObserved _ _
    | replace op => cases op <;> exact eraseObserved _ _
    | syncPruned | syncKeeper => exact eraseObserved _ _

/-- Every outcome of the instrumented finisher projects to the literal
finisher, including invalid plans, aligned repairs and failed renames. -/
theorem forget_observeRename (entry : heap) :
    forgetRename (observeRename dir plan extent remove write sync rename entry) =
      finishBoundedMarkedOpen dir plan extent remove write sync rename entry := by
  unfold observeRename finishBoundedMarkedOpen
  split
  · split
    · exact Erases.bind (eraseObserved _ false) (fun _ => eraseObserved _ false) entry none
    · exact Erases.bind (eraseObserved _ false) (fun _ => eraseSteps dir plan remove write sync rename _) entry none
  · rfl

end LongKeeperRepair

end Alvoki.Storage.WalSegmentRepair
