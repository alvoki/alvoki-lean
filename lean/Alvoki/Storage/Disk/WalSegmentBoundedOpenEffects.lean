import Alvoki.Storage.Disk.WalSegmentBoundedOpen
import Alvoki.Storage.Disk.WalSegmentReplayStability

namespace Alvoki.Storage.WalSegmentRepair

open System

/-- Under a stable file observation, the loaded keeper prefix is the exact
portion of the full visible file that the marker selects. Reading the rest
would give the same replay decision, selected bytes, and table. -/
theorem recoverMarkedWalSegments_keeperPrefix (base : PackedTable) (length : UInt64)
    (sealed : List (Nat × ByteArray)) (keeper : Nat) (full : ByteArray)
    (aligned : length.toNat % WAL.frameSize = 0)
    (enough : (length.toNat / WAL.frameSize - keeper) * WAL.frameSize ≤ full.size)
    (checked : checkSelectedWalSegmentSpans (length.toNat / WAL.frameSize) (sealed ++ [(keeper, full)]) = true) :
    recoverMarkedWalSegments base length
        (sealed ++ [(keeper, full.extract 0 ((length.toNat / WAL.frameSize - keeper) * WAL.frameSize))]) =
      recoverMarkedWalSegments base length (sealed ++ [(keeper, full)]) := by
  let count := (length.toNat / WAL.frameSize - keeper) * WAL.frameSize
  have bound : count ≤ full.size := enough
  let kept := full.extract 0 count
  let tail := full.extract count full.size
  have split : kept ++ tail = full := by
    dsimp only [kept, tail]
    simp [ByteArray.extract_append_extract, Nat.max_eq_right bound]
  have size : kept.size = count := by simp [kept, Nat.min_eq_left bound]
  have original := recoverMarkedWalSegments_removeKeeperTail base length sealed keeper kept tail aligned
    (Nat.le_of_eq size.symm) (by rwa [split])
  rw [split] at original
  exact original.symm

/-- Forgetting the unread tail leaves the exact filesystem action, including
staged replacement bytes, unchanged when the observed physical size agrees
with the full file and the new payload is its checked prefix. -/
theorem finishBoundedMarkedOpen_eq_full [Monad m] [LawfulMonad m] [MonadExceptOf IO.Error m]
    (dir : DiskDirectory) (full : Plan) (valid : full.valid = true)
    (removeFile : FilePath → m (Except IO.Error Unit)) (write : FilePath → ByteArray → m Unit)
    (sync : Array FilePath → m Unit) (renameFile : FilePath → FilePath → m Unit) :
    finishBoundedMarkedOpen dir { full with keeperBytes := full.keeperBytes.extract 0 full.keeperSize }
        full.keeperBytes.size removeFile write sync renameFile =
      finishMarkedOpen dir full removeFile write sync renameFile := by
  let bounded : Plan := { full with keeperBytes := full.keeperBytes.extract 0 full.keeperSize }
  have agrees : bounded.keeperSize = full.keeperSize := rfl
  obtain ⟨covers, enough, later⟩ := (Plan.valid_iff _).mp valid
  have size : bounded.keeperBytes.size = full.keeperSize := by
    change (full.keeperBytes.extract 0 full.keeperSize).size = full.keeperSize
    simp [Nat.min_eq_left enough]
  have boundedValid : bounded.valid = true := (Plan.valid_iff _).mpr
    ⟨covers, by simp only [agrees, size, Nat.le_refl], later⟩
  have sameSelected : bounded.keeperBytes.extract 0 bounded.keeperSize =
      full.keeperBytes.extract 0 full.keeperSize := by
    change (full.keeperBytes.extract 0 full.keeperSize).extract 0 full.keeperSize = _
    simp [ByteArray.extract_extract]
  have samePaths : performPaths dir bounded removeFile throw write sync renameFile =
      performPaths dir full removeFile throw write sync renameFile := by
    funext step
    cases step with
    | unlink first => rfl
    | syncPruned => rfl
    | syncKeeper => rfl
    | replace step =>
      simp only [performPaths, sameSelected]
      rfl
  have names : bounded.newer = full.newer := rfl
  have first : bounded.keeper = full.keeper := rfl
  change finishBoundedMarkedOpen dir bounded full.keeperBytes.size removeFile write sync renameFile = _
  simp only [finishBoundedMarkedOpen, finishMarkedOpen, Plan.alignedWithoutPrune, boundedValid, valid, size,
    agrees, names, first, beq_self_eq_true, Bool.true_and, decide_eq_true enough, ite_true]
  split
  · rfl
  · simp only [runAt, pure_bind, valid, ite_true, runRepairPlan, samePaths, names]

end Alvoki.Storage.WalSegmentRepair
