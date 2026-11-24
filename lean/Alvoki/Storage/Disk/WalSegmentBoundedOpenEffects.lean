import Alvoki.Storage.Disk.WalSegmentBoundedOpen
import Alvoki.Storage.Disk.WalSegmentReplayStability
import Alvoki.Storage.Disk.WalSegmentRetryReadEffects

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

private theorem readSelectedWithPrefix_liftReports {state : Type} (dir : DiskDirectory)
    (watermark : Nat) (length : UInt64) (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata)) (readBin : FilePath → Except IO.Error ByteArray)
    (readPrefix : FilePath → Nat → Except IO.Error KeeperPrefix) :
    (readSelectedWithPrefix dir watermark length (fun path => liftExcept (list path))
      (fun path => liftExcept (lstat path)) (fun path => liftExcept (readBin path))
      (fun path count => liftExcept (readPrefix path count)) : EStateM IO.Error state (WalSegmentMarkerReads × Nat)) =
      liftExcept (readSelectedWithPrefix dir watermark length list lstat readBin readPrefix) := by
  unfold readSelectedWithPrefix
  dsimp only
  by_cases valid : length.toNat % WAL.frameSize = 0 ∧ watermark ≤ length.toNat / WAL.frameSize
  · simp only [ite_eq_left valid]
    rw [← bind_readReport (list dir.path)]
    congr 1
    funext entries
    rw [scanWalSegmentOffsets_liftReports, ← bind_readReport
      (scanWalSegmentOffsets (probeWalSegmentWith dir lstat) (entries.toList.map (·.fileName)))]
    congr 1
    funext offsets
    cases selectWalSegmentReadsThrough offsets watermark (length.toNat / WAL.frameSize) with
    | none => rfl
    | some selection =>
      obtain ⟨required, newer⟩ := selection
      dsimp only
      cases required.getLast? with
      | none => rfl
      | some keeper =>
        simp only [readWalSegmentPayloadsWith, mapM_readReport]
        rw [← bind_readReport (required.dropLast.mapM (fun item => readBin (dir.file (.walSegment item))))]
        congr 1
        funext files
        rw [← bind_readReport (readPrefix (dir.file (.walSegment keeper))
          ((length.toNat / WAL.frameSize - keeper) * WAL.frameSize))]
        congr 1
        funext kept
        by_cases enough : kept.bytes.size = (length.toNat / WAL.frameSize - keeper) * WAL.frameSize ∧
            (length.toNat / WAL.frameSize - keeper) * WAL.frameSize ≤ kept.fileSize
        · rw [ite_eq_left enough, ite_eq_left enough]; rfl
        · rw [ite_eq_right enough, ite_eq_right enough]; rfl
  · simp only [ite_eq_right valid]
    rfl

/-- The bounded preparation phase merely reports the read-only observations.
It does not discard or update the repair interpreter state on error. -/
theorem prepareBoundedMarkedWith_liftReports {state : Type} (dir : DiskDirectory)
    (readOptional : FilePath → Except IO.Error (Option ByteArray)) (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata)) (readBin : FilePath → Except IO.Error ByteArray)
    (readPrefix : FilePath → Nat → Except IO.Error KeeperPrefix) :
    (prepareBoundedMarkedWith dir (fun path => liftExcept (readOptional path)) (fun path => liftExcept (list path))
      (fun path => liftExcept (lstat path)) (fun path => liftExcept (readBin path))
      (fun path count => liftExcept (readPrefix path count)) : EStateM IO.Error state (Plan × Reopened × Nat)) =
      liftExcept (prepareBoundedMarkedWith dir readOptional list lstat readBin readPrefix) := by
  unfold prepareBoundedMarkedWith
  rw [readCheckpoint_liftReports]
  · rw [← bind_readReport]
    congr 1
    funext checkpoint
    generalize checkpoint.getD (.empty, 0) = loaded
    obtain ⟨base, generation⟩ := loaded
    dsimp only
    rw [← bind_readReport (readOptional (dir.file .walBoundary))]
    congr 1
    funext marker
    cases marker with
    | none => rfl
    | some marker =>
      dsimp only
      generalize WAL.Boundary.decode marker = decoded
      cases decoded with
      | error cause => rfl
      | ok length =>
        simp only [readSelectedWithPrefix_liftReports]
        let reported := readSelectedWithPrefix dir base.committed.toNat length list lstat readBin readPrefix
        change ((liftExcept reported : EStateM IO.Error state (WalSegmentMarkerReads × Nat)) >>= _) =
          liftExcept (reported >>= _)
        rw [← bind_readReport reported]
        congr 1
        funext result
        obtain ⟨reads, keeperFileSize⟩ := result
        dsimp only
        generalize recoverMarkedWalSegments base length reads.files = recovered
        cases recovered with
        | error cause => rfl
        | ok recovered =>
          cases recovered
          cases reads.files.getLast? <;> rfl
  · intro α report
    cases report <;> rfl

/-- When the full and bounded read-only preparations report the same
selected layout (with exactly the keeper prefix loaded), the actual marked
worker has the same effectful result, including failures after effects. -/
theorem reopenMarkedBoundedWith_eq_full {σ : Type} (dir : DiskDirectory)
    (readOptional : FilePath → Except IO.Error (Option ByteArray)) (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata)) (readBin : FilePath → Except IO.Error ByteArray)
    (readPrefix : FilePath → Nat → Except IO.Error KeeperPrefix)
    (removeFile : FilePath → EStateM IO.Error σ (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error σ Unit)
    (sync : Array FilePath → EStateM IO.Error σ Unit) (renameFile : FilePath → FilePath → EStateM IO.Error σ Unit)
    {plan : Plan} {opened : Reopened} (valid : plan.valid = true)
    (fullRead : prepareMarkedWith dir readOptional list lstat readBin = .ok (plan, opened))
    (boundedRead : prepareBoundedMarkedWith dir readOptional list lstat readBin readPrefix =
      .ok ({ plan with keeperBytes := plan.keeperBytes.extract 0 plan.keeperSize }, opened, plan.keeperBytes.size)) :
    reopenMarkedBoundedWith dir (fun path => liftExcept (readOptional path)) (fun path => liftExcept (list path))
        (fun path => liftExcept (lstat path)) (fun path => liftExcept (readBin path))
        (fun path count => liftExcept (readPrefix path count)) removeFile write sync renameFile =
      reopenMarkedFastWith dir (fun path => liftExcept (readOptional path)) (fun path => liftExcept (list path))
        (fun path => liftExcept (lstat path)) (fun path => liftExcept (readBin path)) removeFile write sync renameFile := by
  unfold reopenMarkedBoundedWith reopenMarkedFastWith
  rw [prepareBoundedMarkedWith_liftReports, prepareMarkedWith_liftReports, fullRead, boundedRead]
  simp only [liftExcept, pure_bind]
  rw [finishBoundedMarkedOpen_eq_full dir plan valid]

end Alvoki.Storage.WalSegmentRepair
