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

/-- Both repair routes stop at a reported error from the first directory
barrier and keep its exact reached state. -/
theorem finishBoundedMarkedOpen_authorizationError {state : Type} (directory : DiskDirectory) (full : Plan)
    (valid : full.valid = true)
    (removeFile : FilePath → EStateM IO.Error state (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error state Unit)
    (sync : Array FilePath → EStateM IO.Error state Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error state Unit)
    {initial after : state} {cause : IO.Error} (failed : sync #[directory.path] initial = .error cause after) :
    finishBoundedMarkedOpen directory { full with keeperBytes := full.keeperBytes.extract 0 full.keeperSize }
      full.keeperBytes.size removeFile write sync renameFile initial = .error cause after := by
  rw [finishBoundedMarkedOpen_eq_full _ _ valid]
  by_cases aligned : full.alignedWithoutPrune = true
  · simp only [finishMarkedOpen, aligned, ite_true, Bind.bind, EStateM.bind, failed]
  · simp only [finishMarkedOpen, ite_eq_right aligned, runAt, runRepairPlan, Bind.bind, EStateM.bind, Pure.pure,
      EStateM.pure, valid, ite_true, failed]

theorem readSelectedWithPrefix_liftReports {state : Type} (dir : DiskDirectory)
    (watermark : Nat) (length : UInt64) (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata)) (readBin : FilePath → Except IO.Error ByteArray)
    (readPrefix : FilePath → Nat → Except IO.Error KeeperPrefix) :
    (readSelectedWithPrefix dir watermark length (fun path => liftExcept (list path))
      (fun path => liftExcept (lstat path)) (fun path => liftExcept (readBin path))
      (fun path count => liftExcept (readPrefix path count)) : EStateM IO.Error state (WalSegmentMarkerReads × Nat)) =
      liftExcept (readSelectedWithPrefix dir watermark length list lstat readBin readPrefix) := by
  unfold readSelectedWithPrefix withAbsoluteWalCutoff
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
  unfold prepareBoundedMarkedWith prepareBoundedMarkedFromCheckpoint prepareBoundedMarkedFromReaders
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

private theorem mapM_report_length {α β ε : Type} (read : α → Except ε β) (inputs : List α)
    {outputs : List β} (reports : inputs.mapM read = .ok outputs) : inputs.length = outputs.length := by
  induction inputs generalizing outputs with
  | nil => cases reports; rfl
  | cons first rest ih =>
    simp only [List.mapM_cons, Bind.bind, Except.bind] at reports
    cases head : read first with
    | error error => rw [head] at reports; contradiction
    | ok headValue =>
      rw [head] at reports
      cases tail : rest.mapM read with
      | error error => simp [tail] at reports
      | ok remaining =>
        have same : headValue :: remaining = outputs := by
          simpa [tail, Bind.bind, Except.bind, Pure.pure, Except.pure] using reports
        simp [← same, ih tail]

/-- Matching prefix and physical-size reports at the actual keeper path
transport a complete-payload observation to the bounded read worker. -/
theorem readSelectedWithPrefix_from_full (dir : DiskDirectory) (watermark : Nat) (length : UInt64)
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata)) (readBin : FilePath → Except IO.Error ByteArray)
    (readPrefix : FilePath → Nat → Except IO.Error KeeperPrefix)
    {sealed : List (Nat × ByteArray)} {keeper : Nat} {bytes : ByteArray} {newer : List Nat}
    (complete : readWalSegmentsThroughWith dir watermark length list lstat readBin =
      .ok ⟨sealed ++ [(keeper, bytes)], newer⟩)
    (enough : (length.toNat / WAL.frameSize - keeper) * WAL.frameSize ≤ bytes.size)
    (prefixRead : readPrefix (dir.file (.walSegment keeper)) ((length.toNat / WAL.frameSize - keeper) * WAL.frameSize) =
      .ok ⟨bytes.extract 0 ((length.toNat / WAL.frameSize - keeper) * WAL.frameSize), bytes.size⟩) :
    readSelectedWithPrefix dir watermark length list lstat readBin readPrefix =
      .ok (⟨sealed ++ [(keeper, bytes.extract 0 ((length.toNat / WAL.frameSize - keeper) * WAL.frameSize))], newer⟩,
        bytes.size) := by
  have checked : length.toNat % WAL.frameSize = 0 ∧ watermark ≤ length.toNat / WAL.frameSize := by
    by_cases ok : length.toNat % WAL.frameSize = 0 ∧ watermark ≤ length.toNat / WAL.frameSize
    · exact ok
    · simp [readWalSegmentsThroughWith, ok, throw] at complete
  change readWalSegmentsThroughWith dir watermark length list lstat readBin = _ at complete
  simp only [readWalSegmentsThroughWith, ite_eq_left checked, Bind.bind, Except.bind] at complete
  cases listed : list dir.path with
  | error error => simp [listed] at complete
  | ok entries =>
    simp only [listed] at complete
    cases scanned : scanWalSegmentOffsets (probeWalSegmentWith dir lstat) (entries.toList.map (·.fileName)) with
    | error error => simp [scanned] at complete
    | ok offsets =>
      simp only [scanned] at complete
      cases addresses : selectWalSegmentReadsThrough offsets watermark (length.toNat / WAL.frameSize) with
      | none => simp [addresses, throw] at complete
      | some chosen =>
        obtain ⟨required, later⟩ := chosen
        simp only [addresses] at complete
        have nonempty : required ≠ [] := by
          intro empty
          subst required
          simp [readWalSegmentPayloadsWith, Pure.pure, Except.pure] at complete
        let earlier := required.dropLast
        let last := required.getLast nonempty
        have split : earlier ++ [last] = required := List.dropLast_concat_getLast nonempty
        rw [← split] at addresses complete
        have splitRead : readWalSegmentPayloadsWith dir readBin (earlier ++ [last]) =
            (do let rest ← readWalSegmentPayloadsWith dir readBin earlier
                let bytes ← readBin (dir.file (.walSegment last))
                pure (rest ++ [bytes])) := by
          simp [readWalSegmentPayloadsWith, List.mapM_append, List.mapM_cons]
        rw [splitRead] at complete
        cases readEarlier : readWalSegmentPayloadsWith dir readBin earlier with
        | error error => simp [readEarlier, Bind.bind, Except.bind] at complete
        | ok payloads =>
          cases lastRead : readBin (dir.file (.walSegment last)) with
          | error error => simp [readEarlier, lastRead, Bind.bind, Except.bind] at complete
          | ok raw =>
            have sizes : earlier.length = payloads.length := mapM_report_length _ earlier readEarlier
            have pair : (⟨earlier.zip payloads ++ [(last, raw)], later⟩ : WalSegmentMarkerReads) =
                ⟨sealed ++ [(keeper, bytes)], newer⟩ := by
              apply Except.ok.inj
              simpa only [readEarlier, lastRead, Bind.bind, Except.bind, Pure.pure, Except.pure,
                List.zip_append sizes, List.zip_cons_cons, List.zip_nil_left] using complete
            have files := congrArg WalSegmentMarkerReads.files pair
            have laterEq : later = newer := congrArg WalSegmentMarkerReads.newer pair
            have lastEq : (last, raw) = (keeper, bytes) := by
              simpa using congrArg List.getLast? files
            have sameKeeper : last = keeper := congrArg Prod.fst lastEq
            have sameBytes : raw = bytes := congrArg Prod.snd lastEq
            rw [lastEq] at files
            have earlierEq : earlier.zip payloads = sealed := List.append_cancel_right files
            have boundedEnough : (length.toNat / WAL.frameSize - last) * WAL.frameSize ≤ raw.size := by
              rwa [sameKeeper, sameBytes]
            have read : readPrefix (dir.file (.walSegment last)) ((length.toNat / WAL.frameSize - last) * WAL.frameSize) =
                .ok ⟨raw.extract 0 ((length.toNat / WAL.frameSize - last) * WAL.frameSize), raw.size⟩ := by
              simpa only [sameKeeper, sameBytes] using prefixRead
            have result := readSelectedWithPrefix_reported dir watermark length list lstat readBin readPrefix
              checked listed scanned addresses readEarlier read
              (by simp [Nat.min_eq_left boundedEnough]) boundedEnough
            simpa [earlierEq, laterEq, sameKeeper, sameBytes] using result

/-- Use the accepted full preparation and its exact selected keeper
observation to derive bounded preparation. The prefix report supplies the
physical length and only the selected byte interval. -/
theorem prepareBoundedMarkedWith_from_full (dir : DiskDirectory)
    (readOptional : FilePath → Except IO.Error (Option ByteArray))
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata)) (readBin : FilePath → Except IO.Error ByteArray)
    (readPrefix : FilePath → Nat → Except IO.Error KeeperPrefix)
    {plan : Plan} {opened : Reopened} (valid : plan.valid = true)
    (prepared : prepareMarkedWith dir readOptional list lstat readBin = .ok (plan, opened))
    (prefixRead : readPrefix (dir.file (.walSegment plan.keeper)) plan.keeperSize =
      .ok ⟨plan.keeperBytes.extract 0 plan.keeperSize, plan.keeperBytes.size⟩) :
    prepareBoundedMarkedWith dir readOptional list lstat readBin readPrefix =
      .ok ({ plan with keeperBytes := plan.keeperBytes.extract 0 plan.keeperSize }, opened, plan.keeperBytes.size) := by
  obtain ⟨checkpoint, marker, length, reads, selected, table, keeper, bytes, checkpointRead, markerRead, decoded,
    walRead, replayed, lastRead, planned, reopened⟩ := prepareMarkedWith_readReports dir readOptional list lstat readBin prepared
  subst plan opened
  obtain ⟨sealed, fileList⟩ := List.getLast?_eq_some_iff.mp lastRead
  let kept := bytes.extract 0 ((length.toNat / WAL.frameSize - keeper) * WAL.frameSize)
  let bounded : WalSegmentMarkerReads := ⟨sealed ++ [(keeper, kept)], reads.newer⟩
  have enough : (length.toNat / WAL.frameSize - keeper) * WAL.frameSize ≤ bytes.size :=
    ((Plan.valid_iff _).mp valid).2.1
  have boundedRead : readSelectedWithPrefix dir (checkpoint.getD (.empty, 0)).1.committed.toNat length list lstat
      readBin readPrefix = .ok (bounded, bytes.size) :=
    readSelectedWithPrefix_from_full dir _ _ list lstat readBin readPrefix (by
      have equal : reads = ⟨sealed ++ [(keeper, bytes)], reads.newer⟩ := by cases reads; simp_all
      rw [← equal]; exact walRead) enough prefixRead
  have aligned : length.toNat % WAL.frameSize = 0 := by
    by_cases aligned : length.toNat % WAL.frameSize = 0
    · exact aligned
    · simp [readWalSegmentsThroughWith, aligned, throw] at walRead
  have checked : checkSelectedWalSegmentSpans (length.toNat / WAL.frameSize) reads.files = true := by
    cases found : reads.files with
    | nil => simp [found, recoverMarkedWalSegments] at replayed
    | cons first rest =>
      obtain ⟨offset, content⟩ := first
      by_cases valid : checkSelectedWalSegmentSpans (length.toNat / WAL.frameSize) ((offset, content) :: rest) = true
      · exact valid
      · simp [found, recoverMarkedWalSegments, valid] at replayed
  rw [fileList] at checked replayed
  have replay : recoverMarkedWalSegments (checkpoint.getD (.empty, 0)).1 length bounded.files =
      .ok (selected, table) :=
    (recoverMarkedWalSegments_keeperPrefix _ length sealed keeper bytes aligned enough checked).trans replayed
  have lastBound : bounded.files.getLast? = some (keeper, kept) := by simp [bounded]
  simpa only [bounded, kept, Plan.keeperSize] using
    prepareBoundedMarkedWith_reported dir readOptional list lstat readBin readPrefix checkpointRead markerRead
      decoded boundedRead replay lastBound

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
