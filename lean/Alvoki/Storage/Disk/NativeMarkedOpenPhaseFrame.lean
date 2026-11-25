import Alvoki.Storage.Disk.NativeRawOpenPhaseFrame

namespace Alvoki.Storage.DiskSession.KeepsPhase

open System WalSegmentRepair

variable {heap α : Type} {observe : heap → Option (Phase Installed)}

private theorem fromExcept (result : Except IO.Error α) :
    KeepsPhase observe (liftExcept result : EStateM IO.Error heap α) := by
  cases result with
  | ok value => exact .pure value
  | error cause => exact .throw cause

private theorem forM (items : List α) {perform : α → EStateM IO.Error heap Unit}
    (kept : ∀ item, KeepsPhase observe (perform item)) : KeepsPhase observe (items.forM perform) := by
  induction items with
  | nil => exact .pure ()
  | cons item rest earlier => exact (kept item).bind fun _ => earlier

/-- The native held route and only its selected worker can affect a
reached heap. Preserve the old cell across both choices and their guards. -/
theorem recoverSegmented
    {rejectFlat : EStateM IO.Error heap Unit} {marker : EStateM IO.Error heap (Option IO.FS.Metadata)}
    {marked bootstrap : EStateM IO.Error heap Reopened}
    (flat : KeepsPhase observe rejectFlat) (probe : KeepsPhase observe marker)
    (markedFrame : KeepsPhase observe marked) (bootstrapFrame : KeepsPhase observe bootstrap) :
    KeepsPhase observe (recoverSegmentedWalWith rejectFlat marker marked bootstrap) := by
  unfold recoverSegmentedWalWith
  apply flat.bind
  intro _
  apply probe.bind
  intro found
  cases found
  · exact bootstrapFrame
  · exact markedFrame

/-- Preparation reads the selected checkpoint, marker and WAL. Its
pure validation, replay and error branches cannot write a phase cell. -/
theorem preparesMarked (directory : DiskDirectory)
    {checkpoint : EStateM IO.Error heap (Option (PackedTable × UInt64))}
    {readOptional : FilePath → EStateM IO.Error heap (Option ByteArray)}
    {readWal : Nat → UInt64 → EStateM IO.Error heap (WalSegmentMarkerReads × Nat)}
    (checkpointFrame : KeepsPhase observe checkpoint)
    (markerFrame : KeepsPhase observe (readOptional (directory.file .walBoundary)))
    (walFrame : ∀ watermark length, KeepsPhase observe (readWal watermark length)) :
    KeepsPhase observe (prepareBoundedMarkedFromReaders directory checkpoint readOptional readWal) := by
  unfold prepareBoundedMarkedFromReaders
  apply checkpointFrame.bind
  intro selected
  apply markerFrame.bind
  intro marker
  cases marker with
  | none => exact .throw _
  | some bytes =>
    apply (fromExcept ((WAL.Boundary.decode bytes).mapError IO.userError)).bind
    intro length
    apply (walFrame (selected.getD (.empty, 0)).1.committed.toNat length).bind
    rintro ⟨reads, keeperSize⟩
    apply (fromExcept ((recoverMarkedWalSegments (selected.getD (.empty, 0)).1 length reads.files).mapError IO.userError)).bind
    rintro ⟨_, table⟩
    cases found : reads.files.getLast? with
    | none =>
      simpa only [MonadExcept.throw, throwThe] using (KeepsPhase.throw (observe := observe)
        (α := Plan × Reopened × Nat) (IO.userError "no WAL segment covers the commit marker"))
    | some last =>
      obtain ⟨keeper, bytes⟩ := last
      exact .pure _

/-- All reached replacement or prune steps keep the old cell when the
actual remove, write, sync and rename callbacks keep it. -/
theorem repairsMarked (directory : DiskDirectory) (plan : Plan) (replace : Bool)
    {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)}
    {write : FilePath → ByteArray → EStateM IO.Error heap Unit}
    {sync : Array FilePath → EStateM IO.Error heap Unit}
    {rename : FilePath → FilePath → EStateM IO.Error heap Unit}
    (removes : ∀ path, KeepsPhase observe (remove path))
    (writes : ∀ path bytes, KeepsPhase observe (write path bytes))
    (syncs : ∀ paths, KeepsPhase observe (sync paths))
    (renames : ∀ source target, KeepsPhase observe (rename source target)) :
    KeepsPhase observe (runRepairPlan directory plan replace remove write sync rename) := by
  unfold runRepairPlan
  apply (syncs #[directory.path]).bind
  intro _
  apply KeepsPhase.forM
  intro step
  cases step with
  | unlink first =>
    change KeepsPhase observe (do
      match RunCollection.ownedUnlinkResult (← remove (directory.file (.walSegment first))) with
      | .ok () => Pure.pure ()
      | .error cause => MonadExceptOf.throw cause)
    apply (removes (directory.file (.walSegment first))).bind
    intro returned
    split
    · exact .pure _
    · exact .throw _
  | syncPruned | syncKeeper => exact syncs _
  | replace step =>
    cases step with
    | writeStaged => exact writes _ _
    | syncStaged | syncDirectory => exact syncs _
    | renameStaged => exact renames _ _

/-- The bounded finisher also preserves the old cell on its invalid
plan and aligned fast paths, under the same callback contracts. -/
theorem finishesMarked (directory : DiskDirectory) (plan : Plan) (extent : Nat)
    {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)}
    {write : FilePath → ByteArray → EStateM IO.Error heap Unit}
    {sync : Array FilePath → EStateM IO.Error heap Unit}
    {rename : FilePath → FilePath → EStateM IO.Error heap Unit}
    (removes : ∀ path, KeepsPhase observe (remove path))
    (writes : ∀ path bytes, KeepsPhase observe (write path bytes))
    (syncs : ∀ paths, KeepsPhase observe (sync paths))
    (renames : ∀ source target, KeepsPhase observe (rename source target)) :
    KeepsPhase observe (finishBoundedMarkedOpen directory plan extent remove write sync rename) := by
  have repair : KeepsPhase observe (if plan.newer.isEmpty && extent == plan.keeperSize then do
      sync #[directory.path]
      sync #[directory.file (.walSegment plan.keeper)]
    else runRepairPlan directory plan (decide (plan.keeperSize < extent)) remove write sync rename) := by
    split
    · exact (syncs _).bind fun _ => syncs _
    · exact repairsMarked directory plan _ removes writes syncs renames
  by_cases valid : (plan.valid && plan.keeperBytes.size == plan.keeperSize && decide (plan.keeperSize ≤ extent)) = true
  · simpa [finishBoundedMarkedOpen, valid] using repair
  · intro before
    simp [finishBoundedMarkedOpen, valid, Bind.bind, EStateM.bind, MonadExcept.throw, throwThe,
      MonadExceptOf.throw, EStateM.throw]

/-- The production cached marked worker preserves the original phase
across all ordinary results if the selected readers and repair
callbacks preserve it. Its real preparation determines the finisher. -/
theorem reopensMarkedWithCachedExtents (directory : DiskDirectory)
    {readOptional : FilePath → EStateM IO.Error heap (Option ByteArray)}
    {readRunSize : FilePath → EStateM IO.Error heap Nat}
    {readRunPrefix : FilePath → Nat → EStateM IO.Error heap ByteArray}
    {list : FilePath → EStateM IO.Error heap (Array IO.FS.DirEntry)}
    {stat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata)}
    {readSeal : FilePath → Nat → EStateM IO.Error heap ByteArray}
    {readKeeper : FilePath → Nat → Nat → EStateM IO.Error heap ByteArray}
    {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)}
    {write : FilePath → ByteArray → EStateM IO.Error heap Unit}
    {sync : Array FilePath → EStateM IO.Error heap Unit}
    {rename : FilePath → FilePath → EStateM IO.Error heap Unit}
    (checkpoint : KeepsPhase observe
      (readIntegrityCheckpointSized directory (readOptional (directory.file .manifest)) readRunSize readRunPrefix))
    (marker : KeepsPhase observe (readOptional (directory.file .walBoundary)))
    (wal : ∀ watermark length, KeepsPhase observe
      (readSelectedWithCachedExtents directory watermark length list stat readSeal readKeeper))
    (removes : ∀ path, KeepsPhase observe (remove path))
    (writes : ∀ path bytes, KeepsPhase observe (write path bytes))
    (syncs : ∀ paths, KeepsPhase observe (sync paths))
    (renames : ∀ source target, KeepsPhase observe (rename source target)) :
    KeepsPhase observe (reopenMarkedBoundedWithCachedExtents directory readOptional readRunSize readRunPrefix
      list stat readSeal readKeeper remove write sync rename) := by
  unfold reopenMarkedBoundedWithCachedExtents
  apply (preparesMarked directory checkpoint marker wal).bind
  rintro ⟨plan, opened, extent⟩
  exact (finishesMarked directory plan extent removes writes syncs renames).bind fun _ => .pure opened

end Alvoki.Storage.DiskSession.KeepsPhase
