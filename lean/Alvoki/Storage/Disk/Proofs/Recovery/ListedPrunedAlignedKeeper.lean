import Alvoki.Storage.Disk.Proofs.Recovery.HeldLaterWalPrune

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

variable {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout before.image history}
  {operations : MarkedRetryChunkOperations (Cache (DescriptorInventory × DescriptorSlot × Nat)) directory layout}
  {published : CheckpointPublication.Image}
  {held : HeldDirectoryMarkedRetryReports operations published}
  {authorization : ListedDirectoryAuthorization held}

private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat

private def owned (before : LockedFileState FileImage) (directory : DiskDirectory)
    (slot : DescriptorSlot) (image : FileImage) : LockedFileState FileImage :=
  { before with image, owners := before.owners.set (directory.file .lock) (some slot.description) }

private abbrev captured (authorization : ListedDirectoryAuthorization held) : Handle :=
  (authorization.keeper.inventory, authorization.keeper.slot, 0)

private abbrev grouped (authorization : ListedDirectoryAuthorization held) :=
  SyncPathGroup.run (sync directory.path authorization.openRead authorization.fsync)

/-- An aligned keeper remains pending through both directory barriers.
After the reported later-name pass, the original keeper description
supplies the file sync without a staged replacement. -/
structure ListedPrunedAlignedKeeper (prune : ListedLaterWalPrune authorization) where
  aligned : layout.keeper.bytes.size = authorization.keeper.metadata.byteSize.toNat
  nonempty : before.image.later.visible ≠ []
  beforeKeeper : List LockReferenceDrop
  beforeAuthorization : List LockReferenceDrop
  firstDrops : authorization.afterListing = beforeKeeper ++ beforeAuthorization
  available : ∀ old ∈ (held.listing.afterClose.afterDrops beforeKeeper).slots,
    old.address ≠ authorization.keeper.slot.address
  fresh : (held.listing.afterClose.afterDrops beforeKeeper).references authorization.keeper.slot.description = []
  opened : authorization.keeper.inventory =
    (held.listing.afterClose.afterDrops beforeKeeper).insert authorization.keeper.slot available
  afterSuffix : List LockReferenceDrop
  keeperRetained : authorization.keeper.slot ∈
    (authorization.keeper.inventory.afterDrops
      (beforeAuthorization ++ prune.afterAuthorization ++ afterSuffix)).slots
  lockRetained : operations.slot ∈
    (authorization.keeper.inventory.afterDrops
      (beforeAuthorization ++ prune.afterAuthorization ++ afterSuffix)).slots
  keeperBound : prune.bindings (directory.file (.walSegment layout.keeper.first)) = some authorization.keeper.object
  effective : Bool
  outcome :
    let after := owned before directory operations.slot before.image.unlinkVisibleSuffix.syncDirectory
    FsyncResult after { after with image := after.image.syncKeeper } effective (authorization.fsync (captured authorization) after)
  projected :
    let path := directory.file (.walSegment layout.keeper.first)
    let after := owned before directory operations.slot before.image.unlinkVisibleSuffix.syncDirectory
    let remembered := operations.cache.remember path (captured authorization)
    operations.sync operations.cache #[path] after.image = projectDirectorySync (grouped authorization #[path] (remembered, after))

namespace ListedPrunedAlignedKeeper

variable {prune : ListedLaterWalPrune authorization}

private theorem keeperPath_ne_directory (directory : DiskDirectory) (first : Nat) :
    directory.file (.walSegment first) ≠ directory.path := by
  intro same
  have lengths := congrArg (fun path : FilePath => path.toString.length) same
  rw [directory.walSegment_path] at lengths
  simp [String.length_append] at lengths
  have slash : "/".length = 1 := by decide
  rw [slash] at lengths
  omega

/-- Inserting the keeper slot extends the original held census. Both
directory barriers retain the same directory, keeper and lock slots. -/
theorem barrierCensus (repair : ListedPrunedAlignedKeeper prune) :
    let inventory := authorization.keeper.inventory
    let first := inventory.afterDrops repair.beforeAuthorization
    let suffix := inventory.afterDrops (repair.beforeAuthorization ++ prune.afterAuthorization)
    authorization.keeper.slot ∈ first.slots ∧ operations.slot ∈ first.slots ∧ held.lifetime.directorySlot ∈ first.slots ∧
    authorization.keeper.slot ∈ suffix.slots ∧ operations.slot ∈ suffix.slots ∧ held.lifetime.directorySlot ∈ suffix.slots := by
  intro inventory first suffix
  have livePrefix {slot : DescriptorSlot} {early late : List LockReferenceDrop}
      (live : slot ∈ (inventory.afterDrops (early ++ late)).slots) :
      slot ∈ (inventory.afterDrops early).slots := by
    obtain ⟨present, kept⟩ := List.mem_filter.mp live
    exact List.mem_filter.mpr ⟨present, List.all_eq_true.mpr fun event member =>
      List.all_eq_true.mp kept event (List.mem_append_left _ member)⟩
  have keeper : authorization.keeper.slot ∈ suffix.slots := livePrefix repair.keeperRetained
  have lock : operations.slot ∈ suffix.slots := livePrefix repair.lockRetained
  have directoryLive := prune.directoryRetained
  rw [repair.firstDrops, List.append_assoc, ← DescriptorInventory.afterDrops_append] at directoryLive
  obtain ⟨present, kept⟩ := List.mem_filter.mp directoryLive
  have directorySlot : held.lifetime.directorySlot ∈ suffix.slots := by
    change held.lifetime.directorySlot ∈
      (authorization.keeper.inventory.afterDrops (repair.beforeAuthorization ++ prune.afterAuthorization)).slots
    rw [repair.opened]
    exact List.mem_filter.mpr ⟨List.mem_cons_of_mem _ present, kept⟩
  exact ⟨livePrefix keeper, livePrefix lock, livePrefix directorySlot, keeper, lock, directorySlot⟩

/-- The keeper remains pending at authorization and at the second
directory barrier. Its grouped file sync consumes the same description. -/
theorem barriers (repair : ListedPrunedAlignedKeeper prune) :
    let path := directory.file (.walSegment layout.keeper.first)
    let initial := owned before directory operations.slot before.image
    let authorized := owned before directory operations.slot before.image.syncDirectory
    let unlinked := owned before directory operations.slot before.image.unlinkVisibleSuffix
    let after := owned before directory operations.slot before.image.unlinkVisibleSuffix.syncDirectory
    let remembered := operations.cache.remember path (captured authorization)
    readWalKeeperWithChunks operations.reads path layout.keeper.bytes.size
      authorization.keeper.metadata.byteSize.toNat (operations.cache, initial) =
        .ok layout.keeper.bytes (remembered, initial) ∧
    grouped authorization #[directory.path] (remembered, initial) = .ok () (remembered, authorized) ∧
    grouped authorization #[directory.path] (remembered, unlinked) = .ok () (remembered, after) ∧
    grouped authorization #[path] (remembered, after) =
      match authorization.fsync (captured authorization) after with
      | .ok () reached => .ok () (operations.cache.consume path, reached)
      | .error cause reached => .error (IO.userError s!"sync failed for '{path}': {cause}")
          (operations.cache.consume path, reached) := by
  intro path initial authorized unlinked after remembered
  obtain ⟨read, routed⟩ := held.keeperRead_syncListedDirectory authorization.keeper authorization.fits
    authorization.afterListing authorization.directoryRetained authorization.bindings authorization.bound
    authorization.outcome initial authorization.openRead authorization.fsync authorization.effect
  have exactRead : readWalKeeperWithChunks operations.reads path layout.keeper.bytes.size
      authorization.keeper.metadata.byteSize.toNat (operations.cache, initial) =
        .ok layout.keeper.bytes (remembered, initial) := by
    simpa only [Cache.captureKeeper, repair.aligned, ite_true, remembered, path, captured] using read
  have first : sync directory.path authorization.openRead authorization.fsync directory.path (remembered, initial) =
      .ok () (remembered, authorized) := by
    simpa [Cache.captureKeeper, repair.aligned, remembered, path, captured,
      HeldDirectoryMarkedRetryReports.directoryBarrier, DescriptorInventory.delayedDirectorySync,
      DelayedDirectorySync.run, prune.authorized, withCache, authorized, initial, owned] using routed
  refine ⟨exactRead, ?_, ?_, ?_⟩
  · rw [grouped, SyncPathGroup.run_single, first]
  · rw [grouped, SyncPathGroup.run_single]
    have routedSuffix : sync directory.path authorization.openRead authorization.fsync directory.path
        (remembered, unlinked) =
        withCache remembered (authorization.fsync (operations.descriptors, held.lifetime.directorySlot, 0) unlinked) := by
      simp [sync, Cache.resolve, remembered, Cache.remember, held.capturedDirectory]
    have effect := prune.effect
    change authorization.fsync (operations.descriptors, held.lifetime.directorySlot, 0) unlinked = .ok () after at effect
    rw [routedSuffix, effect]
    rfl
  · rw [grouped, SyncPathGroup.run_single]
    dsimp only [remembered]
    rw [syncRemembered (keeperPath_ne_directory directory layout.keeper.first)
      (captured authorization) authorization.openRead authorization.fsync after]
    cases authorization.fsync (captured authorization) after with
    | ok value reached => cases value; rfl
    | error => rfl

/-- The original lock and aligned keeper still refer to live
descriptions in the census at the final file barrier. The later unlink
pass has preserved the exact inode at the selected keeper path. -/
theorem keeperCustody (repair : ListedPrunedAlignedKeeper prune)
    (later : ∀ first ∈ before.image.later.visible, layout.range.through < first) :
    let inventory := authorization.keeper.inventory
    let after := owned before directory operations.slot before.image.unlinkVisibleSuffix.syncDirectory
    let drops := repair.beforeAuthorization ++ prune.afterAuthorization ++ repair.afterSuffix
    let path := directory.file (.walSegment layout.keeper.first)
    prune.reached (directory.file .lock) = some (inventory.inode operations.slot.description) ∧
    (∃ refs : HeldLockReferences operations.slot.description,
      refs.live = inventory.references operations.slot.description ∧
      (refs.afterFileDrops drops directory after).owners.Owns directory operations.slot.description) ∧
    ∃ observed : FsyncObservation (fun handle : Handle => handle.2.1.description)
        (fun handle => handle.1.inode handle.2.1.description) (captured authorization) after
        (fun _ files => { files with image := files.image.syncKeeper }) (authorization.fsync (captured authorization) after),
      observed.issuer = authorization.keeper.slot.reference ∧ observed.effective = repair.effective ∧
      prune.reached path = some observed.effectInode := by
  intro inventory after drops path
  have keeperLive : authorization.keeper.slot.reference ∈
      (inventory.afterDrops drops).references authorization.keeper.slot.description :=
    (inventory.afterDrops drops).mem_references.mpr ⟨_, repair.keeperRetained, rfl, rfl⟩
  have lockLive : operations.slot.reference ∈ (inventory.afterDrops drops).references operations.slot.description :=
    (inventory.afterDrops drops).mem_references.mpr ⟨_, repair.lockRetained, rfl, rfl⟩
  let refs := inventory.held operations.slot.description (DescriptorInventory.wasLive lockLive)
  have remains : refs.remaining drops ≠ [] := by
    rw [inventory.held_remaining]
    exact List.ne_nil_of_mem lockLive
  let observed := FsyncObservation.ofInventory inventory drops (fun handle : Handle => handle.2.1.description)
    (fun handle => handle.1.inode handle.2.1.description) (captured authorization) authorization.keeper.slot.reference
    keeperLive rfl after (fun _ files => { files with image := files.image.syncKeeper }) repair.outcome
  refine ⟨?_, ⟨refs, rfl, ?_⟩, observed, rfl, rfl, ?_⟩
  · change _ = some (authorization.keeper.inventory.inode operations.slot.description)
    rw [repair.opened]
    exact prune.lockBound
  · rw [refs.afterFileDrops_surviving remains]
    simp [after, owned, LockOwners.Owns, LockOwners.set]
  · change prune.reached path = some (inventory.inode authorization.keeper.slot.description)
    rw [authorization.keeper.sameObject]
    have kept := (prune.selectedBindings later).2.1 layout.keeper (List.mem_append_right _ (by simp))
    exact kept.trans repair.keeperBound

/-- The exact grouped keeper result is projected after the reached
suffix barrier, preserving the distinct before and after effect errors. -/
theorem syncResult (repair : ListedPrunedAlignedKeeper prune) :
    let path := directory.file (.walSegment layout.keeper.first)
    let after := owned before directory operations.slot before.image.unlinkVisibleSuffix.syncDirectory
    operations.sync operations.cache #[path] after.image =
      match authorization.fsync (captured authorization) after with
      | .ok () _ => .ok () after.image.syncKeeper
      | .error cause _ => .error (IO.userError s!"sync failed for '{path}': {cause}")
          (if repair.effective then after.image.syncKeeper else after.image) := by
  intro path after
  have routed := repair.barriers.2.2.2
  rw [repair.projected, routed]
  have outcome := repair.outcome
  change FsyncResult after { after with image := after.image.syncKeeper } repair.effective
    (authorization.fsync (captured authorization) after) at outcome
  change _ = match authorization.fsync (captured authorization) after with
    | .ok () _ => EStateM.Result.ok () after.image.syncKeeper
    | .error cause _ => EStateM.Result.error (IO.userError s!"sync failed for '{path}': {cause}")
        (if repair.effective then after.image.syncKeeper else after.image)
  generalize authorization.fsync (captured authorization) after = result at outcome ⊢
  generalize repair.effective = effective at outcome ⊢
  cases outcome <;> rfl

private theorem exactPlanSize (repair : ListedPrunedAlignedKeeper prune) :
    layout.plan.keeperBytes.size = layout.plan.keeperSize :=
  authorization.keeper.extent.symm.trans (repair.aligned.symm.trans layout.target.trimmedSize)

/-- The actual bounded worker takes the full repair schedule because
later names are visible, and goes directly from the suffix directory
barrier to the retained keeper sync. -/
theorem finishResult (repair : ListedPrunedAlignedKeeper prune)
    (later : ∀ first ∈ before.image.later.visible, layout.range.through < first) :
    finishBoundedMarkedOpen directory layout.boundedPlan authorization.keeper.metadata.byteSize.toNat
      operations.removeFile (operations.write operations.cache) (operations.sync operations.cache)
      operations.renameFile before.image =
    operations.sync operations.cache #[directory.file (.walSegment layout.keeper.first)]
      before.image.unlinkVisibleSuffix.syncDirectory := by
  have size : layout.boundedPlan.keeperBytes.size = layout.boundedPlan.keeperSize := layout.target.trimmedSize
  have physical : authorization.keeper.metadata.byteSize.toNat = layout.boundedPlan.keeperSize :=
    repair.aligned.symm.trans size
  have valid := layout.boundedPlan_valid later
  have newer : layout.boundedPlan.newer.isEmpty = false := List.isEmpty_eq_false_iff.mpr repair.nonempty
  let run := performPaths directory layout.boundedPlan operations.removeFile throw
    (operations.write operations.cache) (operations.sync operations.cache) operations.renameFile
  have unlinks :
      (layout.boundedPlan.newer.map Step.unlink).forM run before.image.syncDirectory =
        .ok () before.image.unlinkVisibleSuffix := prune.unlinks.returned layout.boundedPlan
  have suffix := prune.suffixBarrier.2.2.2.2
  simp only [finishBoundedMarkedOpen, valid, size, physical, Bool.true_and, beq_self_eq_true, Nat.le_refl,
    decide_true, newer, Bool.false_and, Bool.false_eq_true, Nat.lt_irrefl, decide_false, ↓reduceIte,
    runRepairPlan, steps, List.append_assoc, Bind.bind, EStateM.bind, authorization.settles prune.authorized]
  rw [List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM]
  change ((layout.boundedPlan.newer.map Step.unlink).forM run >>= fun _ =>
    ([Step.syncPruned] ++ [Step.syncKeeper]).forM run) before.image.syncDirectory = _
  simp only [Bind.bind, EStateM.bind, unlinks, List.cons_append, List.nil_append, List.forM_eq_forM,
    List.forM_cons, List.forM_nil, run, performPaths, suffix, Pure.pure, EStateM.pure]
  have keeper : layout.boundedPlan.keeper = layout.keeper.first := rfl
  rw [keeper]
  cases operations.sync operations.cache #[directory.file (.walSegment layout.keeper.first)]
    before.image.unlinkVisibleSuffix.syncDirectory with
  | ok value reached => cases value; rfl
  | error => rfl

/-- Exact reported unlink, directory sync and keeper sync supply the
whole per-operation contract of the slow aligned route. -/
theorem healthyFinish (repair : ListedPrunedAlignedKeeper prune)
    (succeeded : authorization.fsync (captured authorization)
      (owned before directory operations.slot before.image.unlinkVisibleSuffix.syncDirectory) =
        .ok () (owned before directory operations.slot before.image.unlinkVisibleSuffix.syncDirectory.syncKeeper)) :
    operations.HealthyFinish := by
  have declined : layout.plan.alignedWithoutPrune = false := by
    have newer : layout.plan.newer.isEmpty = false := List.isEmpty_eq_false_iff.mpr repair.nonempty
    simp [Plan.alignedWithoutPrune, newer]
  have schedule : layout.plan.finishActions = before.image.later.visible.map Step.unlink ++ [.syncPruned, .syncKeeper] := by
    simp [Plan.finishActions, declined, Plan.actions, steps, repair.exactPlanSize]
    rfl
  have keeper := repair.syncResult
  dsimp only at keeper
  rw [succeeded] at keeper
  unfold MarkedRetryChunkOperations.HealthyFinish
  rw [schedule]
  refine prune.unlinks.prependHealthy layout.plan ?_
  refine ReachesAction.prependHealthy (next := before.image.unlinkVisibleSuffix.syncDirectory)
    rfl prune.suffixBarrier.2.2.2.2 ?_
  refine ReachesAction.prependHealthy (next := before.image.unlinkVisibleSuffix.syncDirectory.syncKeeper) rfl keeper ?_
  intro action prior next reached _
  obtain ⟨earlier, later, ordered, _⟩ := reached
  have size := congrArg List.length ordered
  simp at size

/-- The raw keeper fsync after settling the reported later-name removals. -/
abbrev keeperFsyncReturn (_repair : ListedPrunedAlignedKeeper prune) :
    EStateM.Result IO.Error (LockedFileState FileImage) Unit :=
  authorization.fsync (captured authorization)
    (owned before directory operations.slot before.image.unlinkVisibleSuffix.syncDirectory)

/-- The raw keeper return determines its settled state after this prune. -/
theorem healthyFinishOfKeeperReturn (repair : ListedPrunedAlignedKeeper prune)
    (succeeded : ∃ reached, repair.keeperFsyncReturn = .ok () reached) :
    operations.HealthyFinish :=
  repair.healthyFinish (repair.outcome.completed_of_return succeeded)

/-- The exact kept bytes are installed by the admitted marked opener
after the ordered suffix removal and the retained keeper's sync. -/
theorem installs {input : FilePath} (repair : ListedPrunedAlignedKeeper prune) (metadata : HeldMarkedMetadata held)
    (succeeded : authorization.fsync (captured authorization)
      (owned before directory operations.slot before.image.unlinkVisibleSuffix.syncDirectory) =
        .ok () (owned before directory operations.slot before.image.unlinkVisibleSuffix.syncDirectory.syncKeeper))
    (admission : OpenAdmissionReports input directory operations.slot)
    (keeperValid : before.image.keeper.Valid layout.target.Accepts)
    (laterValid : before.image.later.Beyond layout.range.through)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      before.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    CachedRetryInstalled (before := before) operations.reported operations.descriptors operations.slot operations.bindings
      published operations.liveRefs (operations.runWithAdmission admission) :=
  authorization.installs metadata prune.authorized (repair.healthyFinish succeeded) admission keeperValid laterValid
    following accepted ordered

end ListedPrunedAlignedKeeper

end Alvoki.Storage.DiskSession
