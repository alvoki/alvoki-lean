import Alvoki.Storage.Disk.LongWalBindingPublication

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

/-- A successful replacement rename records its return heap for this invocation.
Other callbacks preserve the observation, including when they report an error. -/
private def observe (action : EStateM IO.Error heap α) (recordRename : Bool := false) :
    EStateM IO.Error (heap × Option heap) α := fun (before, prior) =>
  match action before with
  | .ok value after => .ok value (after, if recordRename then some after else prior)
  | .error cause after => .error cause (after, prior)

variable (dir : DiskDirectory) (plan : Plan) (extent : Nat)
  (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
  (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
  (sync : Array FilePath → EStateM IO.Error heap Unit)
  (rename : FilePath → FilePath → EStateM IO.Error heap Unit)

/-- The literal bounded finisher with one observation, initially absent. The
same rename on an earlier open cannot supply the returned heap. -/
def observeRename (start : heap) : EStateM.Result IO.Error (heap × Option heap) Unit :=
  finishBoundedMarkedOpen dir plan extent (fun path => observe (remove path))
    (fun path bytes => observe (write path bytes)) (fun paths => observe (sync paths))
    (fun src dst => observe (rename src dst) true) (start, none)

private theorem observe_pure (value : α) :
    (pure value : EStateM IO.Error (heap × Option heap) α) = observe (pure value) := rfl

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

/-- Reaching an error with a recorded rename is equivalent to the ordinary
prefix returning, the actual rename returning at that heap, and the final
directory group failing there. Both earlier directory syncs share its target. -/
theorem observeRename_error_iff
    (valid : plan.valid = true) (size : plan.keeperBytes.size = plan.keeperSize)
    (long : plan.keeperSize < extent) {start renamed reached : heap} {cause : IO.Error} :
    observeRename dir plan extent remove write sync rename start = .error cause (reached, some renamed) ↔
      ∃ authorized pruned staged synced,
        sync #[dir.path] start = .ok () authorized ∧
        ((plan.newer.map Step.unlink ++ [Step.syncPruned]).forM perform) authorized = .ok () pruned ∧
        write (dir.file .stagedWal) plan.keeperBytes pruned = .ok () staged ∧
        sync #[dir.file .stagedWal] staged = .ok () synced ∧
        rename (dir.file .stagedWal) (dir.file (.walSegment plan.keeper)) synced = .ok () renamed ∧
        sync #[dir.path] renamed = .error cause reached := by
  unfold observeRename
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
  cases moved : rename (dir.file .stagedWal) (dir.file (.walSegment plan.keeper)) syncedHeap <;> simp
  rename_i renamedHeap
  by_cases same : renamedHeap = renamed
  · subst renamedHeap
    cases final : sync #[dir.path] renamed <;> simp [Pure.pure, EStateM.pure]
  · cases final : sync #[dir.path] renamedHeap <;> simp [same, Pure.pure, EStateM.pure]

end LongKeeperRepair

end Alvoki.Storage.WalSegmentRepair
