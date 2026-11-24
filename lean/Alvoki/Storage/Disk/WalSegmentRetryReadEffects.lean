import Alvoki.Storage.Disk.WalSegmentRetryReads
import Alvoki.Storage.Disk.WalSegmentOpenFastEffects

namespace Alvoki.Storage.WalSegmentRepair

open System

theorem bind_readReport {ε σ α β : Type} (report : Except ε α) (next : α → Except ε β) :
    ((liftExcept report : EStateM ε σ α) >>= fun value => liftExcept (next value)) =
      liftExcept (report >>= next) := by
  cases report <;> rfl

private theorem map_readReport {ε σ α β : Type} (report : Except ε α) (transform : α → β) :
    transform <$> (liftExcept report : EStateM ε σ α) = liftExcept (transform <$> report) := by
  cases report <;> rfl

theorem mapM_readReport {ε σ α β : Type} (items : List α) (read : α → Except ε β) :
    (items.mapM (fun item => liftExcept (read item)) : EStateM ε σ (List β)) =
      liftExcept (items.mapM read) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [List.mapM_cons, ih, bind_pure_comp, map_readReport, bind_readReport]

theorem filterMapM_readReport {ε σ α β : Type} (items : List α) (read : α → Except ε (Option β)) :
    (items.filterMapM (fun item => liftExcept (read item)) : EStateM ε σ (List β)) =
      liftExcept (items.filterMapM read) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [List.filterMapM_cons, ih, bind_pure_comp, map_readReport]
    rw [← bind_readReport (read item)]
    congr 1
    funext result
    cases result <;> rfl

theorem readCheckpoint_liftReports {state : Type}
    (manifest : Except IO.Error (Option ByteArray)) (readRun : UInt64 → Nat → Except IO.Error ByteArray)
    {validateState : {α : Type} → Except String α → EStateM IO.Error state α}
    {validateReport : {α : Type} → Except String α → Except IO.Error α}
    (validate : ∀ {α : Type} (result : Except String α), validateState result = liftExcept (validateReport result)) :
    readIntegrityCheckpoint (liftExcept manifest) (fun generation index => liftExcept (readRun generation index))
      @validateState = liftExcept (readIntegrityCheckpoint manifest readRun @validateReport) := by
  simp only [readIntegrityCheckpoint, readCheckpointRunBytes_eq_mapM, mapM_readReport]
  rw [← bind_readReport manifest]
  congr 1
  funext value
  cases value with
  | none => rfl
  | some bytes =>
    simp only [validate]
    rw [← bind_readReport (validateReport (Manifest.IntegrityCheckpoint.decode bytes))]
    congr 1
    funext manifest
    rw [← bind_readReport ((List.range manifest.header.runCount.toNat).mapM (readRun manifest.header.generation))]
    congr 1
    funext files
    rw [← bind_readReport (validateReport (loadIntegrityRunSet manifest files))]
    rfl

theorem scanWalSegmentOffsets_liftReports {state : Type} (dir : DiskDirectory)
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata)) (names : List String) :
    (scanWalSegmentOffsets (probeWalSegmentWith dir (fun path => liftExcept (lstat path))) names :
      EStateM IO.Error state (List Nat)) = liftExcept (scanWalSegmentOffsets (probeWalSegmentWith dir lstat) names) := by
  have probe (offset : Nat) :
      (probeWalSegmentWith dir (fun path => liftExcept (lstat path)) offset : EStateM IO.Error state (Option Nat)) =
        liftExcept (probeWalSegmentWith dir lstat offset) := by
    unfold probeWalSegmentWith
    rw [← bind_readReport (lstat (dir.file (.walSegment offset)))]
    apply congrArg (fun next => (liftExcept (lstat (dir.file (.walSegment offset))) :
      EStateM IO.Error state (Except IO.Error IO.FS.Metadata)) >>= next)
    funext metadata
    cases classifyWalSegmentLookup (dir.file (.walSegment offset)) offset metadata <;> rfl
  have listed (name : String) :
      (probeListedWalSegment (probeWalSegmentWith dir (fun path => liftExcept (lstat path))) name :
        EStateM IO.Error state (Option Nat)) =
      liftExcept (probeListedWalSegment (probeWalSegmentWith dir lstat) name) := by
    unfold probeListedWalSegment
    cases parseWalSegmentName name with
    | none => rfl
    | some offset => exact probe offset
  simp only [scanWalSegmentOffsets, show
    probeListedWalSegment (probeWalSegmentWith dir (fun path => liftExcept (lstat path))) =
      (fun name => liftExcept (probeListedWalSegment (probeWalSegmentWith dir lstat) name)) from funext listed,
    filterMapM_readReport, map_readReport]

private theorem readWalSegments_liftReports {state : Type} (dir : DiskDirectory) (watermark : Nat) (length : UInt64)
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata)) (readBin : FilePath → Except IO.Error ByteArray) :
    (readWalSegmentsThroughWith dir watermark length (fun path => liftExcept (list path))
      (fun path => liftExcept (lstat path)) (fun path => liftExcept (readBin path)) :
      EStateM IO.Error state WalSegmentMarkerReads) =
      liftExcept (readWalSegmentsThroughWith dir watermark length list lstat readBin) := by
  unfold readWalSegmentsThroughWith
  dsimp only
  by_cases allowed : length.toNat % WAL.frameSize = 0 ∧ watermark ≤ length.toNat / WAL.frameSize
  · simp only [ite_eq_left allowed]
    rw [← bind_readReport (list dir.path)]
    congr 1
    funext entries
    rw [scanWalSegmentOffsets_liftReports, ← bind_readReport (scanWalSegmentOffsets (probeWalSegmentWith dir lstat) (entries.toList.map (·.fileName)))]
    congr 1
    funext offsets
    cases selectWalSegmentReadsThrough offsets watermark (length.toNat / WAL.frameSize) with
    | none => rfl
    | some plan =>
      rcases plan with ⟨required, newer⟩
      simp only [readWalSegmentPayloadsWith, mapM_readReport, bind_pure_comp, map_readReport]
  · simp only [ite_eq_right allowed]
    rfl

/-- Read-only primitive reports produce the same exact preparation result in
an effectful interpreter. Success and failure both leave its state intact. -/
theorem prepareMarkedWith_liftReports {state : Type} (directory : DiskDirectory)
    (readOptional : FilePath → Except IO.Error (Option ByteArray))
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → Except IO.Error ByteArray) :
    (prepareMarkedWith directory (fun path => liftExcept (readOptional path)) (fun path => liftExcept (list path))
      (fun path => liftExcept (lstat path)) (fun path => liftExcept (readBin path)) :
      EStateM IO.Error state (Plan × Reopened)) =
      liftExcept (prepareMarkedWith directory readOptional list lstat readBin) := by
  unfold prepareMarkedWith
  rw [readCheckpoint_liftReports]
  · rw [← bind_readReport]
    congr 1
    funext checkpoint
    generalize checkpoint.getD (.empty, 0) = loaded
    obtain ⟨base, generation⟩ := loaded
    dsimp only
    rw [← bind_readReport (readOptional (directory.file .walBoundary))]
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
        simp only [readWalSegments_liftReports]
        let reported := readWalSegmentsThroughWith directory base.committed.toNat length list lstat readBin
        change ((liftExcept reported : EStateM IO.Error state WalSegmentMarkerReads) >>= _) =
          liftExcept (reported >>= _)
        rw [← bind_readReport reported]
        congr 1
        funext reads
        generalize recoverMarkedWalSegments base length reads.files = recovered
        cases recovered with
        | error cause => rfl
        | ok recovered =>
          cases recovered
          cases reads.files.getLast? <;> rfl
  · intro α report
    cases report <;> rfl

/-- From one healthy canonical retry observation, the same strict worker
returns the original selected replay and a durably repaired file image.
Healthy effect reports are needed only for the prepared schedule. -/
theorem EffectTrace.completesObservedRetry {directory : DiskDirectory} {target : Target}
    {initial retry : FileImage} {oldPlan : Plan} (trace : EffectTrace target initial retry)
    (old : Prepared initial target oldPlan) (observed : RetryInventory directory retry target)
    {scanned : List Nat} (scan : observed.listing.offsets = .ok scanned)
    (first : Nat) (required : List Nat)
    (needed : observed.sealed.map Prod.fst ++ [target.first] = first :: required)
    (covers : first ≤ target.range.watermark)
    (olderBefore : ∀ start ∈ observed.older, start < first)
    (requiredBounds : ∀ start ∈ required, target.range.watermark < start ∧ start ≤ target.range.through)
    {durable : CheckpointPublication.RunFiles} {checkpoint : Option (PackedTable × UInt64)}
    (selectedCheckpoint : SelectedIntegrityCheckpoint durable target.pair.manifest checkpoint)
    (manifestRead : observed.listing.reports.readOptional (directory.file .manifest) =
      .ok retry.directory.active.manifest)
    (runReads : ∀ bytes manifest, target.pair.manifest = some bytes →
      Manifest.IntegrityCheckpoint.decode bytes = .ok manifest → ∀ index, index < manifest.header.runCount.toNat →
        (observed.listing.reports.readBin (directory.file (.run manifest.header.generation index))).toOption =
          durable manifest.header.generation index)
    (markerRead : observed.listing.reports.readOptional (directory.file .walBoundary) =
      .ok retry.directory.active.walBoundary)
    {count : UInt64} {selected : ByteArray} {table : PackedTable}
    (oldCount : count.toNat = target.range.through * WAL.frameSize)
    (replayed : recoverMarkedWalSegments (checkpoint.getD (.empty, 0)).1 count
      (observed.sealed ++ [(target.first, oldPlan.keeperBytes)]) = .ok (selected, table))
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (rename : FilePath → FilePath → EStateM IO.Error FileImage Unit)
    (settles : sync #[directory.path] retry = .ok () retry.syncDirectory)
    (healthy : ∀ plan, Prepared retry target plan → ∀ action before next,
      ReachesAction target retry.syncDirectory plan.finishActions action before →
        before.effect target action = some next →
          performPaths directory plan removeFile throw write sync rename action before = .ok () next) :
    ∃ plan after, Prepared retry target plan ∧ after.Ready target ∧
      reopenMarkedFastWith directory
        (fun path => liftExcept (observed.listing.reports.readOptional path)) (fun _ => pure observed.entries)
        (fun path => pure (observed.listing.reports.lstat path))
        (fun path => liftExcept (observed.listing.reports.readBin path)) removeFile write sync rename retry =
        .ok ⟨table, (checkpoint.getD (.empty, 0)).2, count, target.first⟩ after ∧
      recoverMarkedWalSegments (checkpoint.getD (.empty, 0)).1 count
        (observed.sealed ++ [(target.first, plan.keeperBytes)]) = .ok (selected, table) := by
  obtain ⟨plan, prepared, reported, replay⟩ := trace.prepareObservedRetry old observed scan first required
    needed covers olderBefore requiredBounds selectedCheckpoint manifestRead runReads markerRead oldCount replayed
  let readOptional := observed.listing.reports.readOptional
  let list : FilePath → Except IO.Error (Array IO.FS.DirEntry) := fun _ => .ok observed.entries
  let lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata) :=
    fun path => .ok (observed.listing.reports.lstat path)
  let readBin := observed.listing.reports.readBin
  have lifted := prepareMarkedWith_liftReports (state := FileImage) directory readOptional list lstat readBin
  change prepareMarkedWith directory readOptional list lstat readBin = _ at reported
  rw [reported] at lifted
  obtain ⟨after, opened, ready⟩ := reopenMarkedFastWith_completes prepared directory
    (fun path => liftExcept (readOptional path)) (fun path => liftExcept (list path))
    (fun path => liftExcept (lstat path)) (fun path => liftExcept (readBin path)) removeFile write sync rename
    (congrFun lifted retry) settles (healthy plan prepared)
  exact ⟨plan, after, prepared, ready, opened, replay⟩

end Alvoki.Storage.WalSegmentRepair
