import Alvoki.Storage.Disk.Proofs.Recovery.ListedDirectoryAuthorization
import Alvoki.Storage.Disk.AlignedWalChunkSync

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

variable {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout before.image history}
  {operations : MarkedRetryChunkOperations (Cache (DescriptorInventory × DescriptorSlot × Nat)) directory layout}
  {published : CheckpointPublication.Image}

private abbrev OpenHandle := DescriptorInventory × DescriptorSlot × Nat

private def acquiredState (before : LockedFileState FileImage) (directory : DiskDirectory)
    (slot : DescriptorSlot) : LockedFileState FileImage :=
  { before with owners := before.owners.set (directory.file .lock) (some slot.description) }

private def authorizeFiles (files : LockedFileState FileImage) : LockedFileState FileImage :=
  { files with image := files.image.syncDirectory }

private def settleKeeper (files : LockedFileState FileImage) : LockedFileState FileImage :=
  { files with image := files.image.syncKeeper }

/-- The selected keeper is opened after the listing closes and stays live
through both barriers. The slot table tracks the retained lock and directory
handles and this keeper. The observation supplies drops, effect-time
bindings, the syscall outcome and the projection of the same grouped
callback used by the marked worker. -/
structure ListedAlignedKeeperRepair {report : HeldDirectoryMarkedRetryReports operations published}
    (authorization : ListedDirectoryAuthorization report) where
  completed : authorization.outcome = .completed
  aligned : layout.keeper.bytes.size = authorization.keeper.metadata.byteSize.toNat
  noLater : before.image.later.visible = []
  beforeKeeper : List LockReferenceDrop
  beforeAuthorization : List LockReferenceDrop
  afterAuthorization : List LockReferenceDrop
  firstDrops : authorization.afterListing = beforeKeeper ++ beforeAuthorization
  available : ∀ old ∈ (report.listing.afterClose.afterDrops beforeKeeper).slots,
    old.address ≠ authorization.keeper.slot.address
  fresh : (report.listing.afterClose.afterDrops beforeKeeper).references authorization.keeper.slot.description = []
  opened : authorization.keeper.inventory =
    (report.listing.afterClose.afterDrops beforeKeeper).insert authorization.keeper.slot available
  keeperRetained : authorization.keeper.slot ∈
    (authorization.keeper.inventory.afterDrops (beforeAuthorization ++ afterAuthorization)).slots
  lockRetained : operations.slot ∈
    (authorization.keeper.inventory.afterDrops (beforeAuthorization ++ afterAuthorization)).slots
  bindings : FilePath → Option Nat
  keeperBound : bindings (directory.file (.walSegment layout.keeper.first)) = some authorization.keeper.object
  lockBound : bindings (directory.file .lock) = some (operations.descriptors.inode operations.slot.description)
  effective : Bool
  outcome :
    let captured : OpenHandle := (authorization.keeper.inventory, authorization.keeper.slot, 0)
    let authorized := authorizeFiles (acquiredState before directory operations.slot)
    FsyncResult authorized (settleKeeper authorized) effective (authorization.fsync captured authorized)
  projected : ∀ reached,
    let initial := acquiredState before directory operations.slot
    let authorized := authorizeFiles initial
    let path := directory.file (.walSegment layout.keeper.first)
    let grouped := SyncPathGroup.run (sync directory.path authorization.openRead authorization.fsync)
    readWalKeeperWithChunks operations.reads path layout.keeper.bytes.size
      authorization.keeper.metadata.byteSize.toNat (operations.cache, initial) =
        .ok layout.keeper.bytes (reached, initial) →
    grouped #[directory.path] (reached, initial) = .ok () (reached, authorized) →
    operations.sync operations.cache #[path] authorized.image =
      projectDirectorySync (grouped #[path] (reached, authorized))

namespace ListedAlignedKeeperRepair

variable {report : HeldDirectoryMarkedRetryReports operations published}
  {authorization : ListedDirectoryAuthorization report}

private theorem keeperPath_ne_directory (directory : DiskDirectory) (first : Nat) :
    directory.file (.walSegment first) ≠ directory.path := by
  intro same
  have lengths := congrArg (fun path : FilePath => path.toString.length) same
  rw [directory.walSegment_path] at lengths
  simp [String.length_append] at lengths
  have slash : "/".length = 1 := by decide
  rw [slash] at lengths
  omega

/-- The same opened keeper is live at the first and second barriers.
The first barrier also retains the captured directory and lock slots. -/
theorem barrierCensus (repair : ListedAlignedKeeperRepair authorization) :
    let atFirst := authorization.keeper.inventory.afterDrops repair.beforeAuthorization
    let atKeeper := authorization.keeper.inventory.afterDrops (repair.beforeAuthorization ++ repair.afterAuthorization)
    authorization.keeper.slot ∈ atFirst.slots ∧
    operations.slot ∈ atFirst.slots ∧ report.lifetime.directorySlot ∈ atFirst.slots ∧
    authorization.keeper.slot ∈ atKeeper.slots ∧ operations.slot ∈ atKeeper.slots := by
  intro atFirst atKeeper
  have retained {slot : DescriptorSlot} (survives : slot ∈ atKeeper.slots) : slot ∈ atFirst.slots := by
    obtain ⟨present, kept⟩ := List.mem_filter.mp survives
    exact List.mem_filter.mpr ⟨present, List.all_eq_true.mpr fun event member =>
      List.all_eq_true.mp kept event (List.mem_append_left _ member)⟩
  refine ⟨retained repair.keeperRetained, retained repair.lockRetained, ?_,
    repair.keeperRetained, repair.lockRetained⟩
  have directoryLive := authorization.directoryRetained
  rw [repair.firstDrops, ← DescriptorInventory.afterDrops_append] at directoryLive
  obtain ⟨present, kept⟩ := List.mem_filter.mp directoryLive
  change report.lifetime.directorySlot ∈
    (authorization.keeper.inventory.afterDrops repair.beforeAuthorization).slots
  rw [repair.opened]
  exact List.mem_filter.mpr ⟨List.mem_cons_of_mem _ present, kept⟩

/-- The issuing keeper slot and the original lock share the reached
census. The syscall report ties the keeper effect to the captured inode
and the effect-time binding of its canonical path. -/
theorem keeperCustody (repair : ListedAlignedKeeperRepair authorization) :
    let inventory := authorization.keeper.inventory
    let drops := repair.beforeAuthorization ++ repair.afterAuthorization
    let captured : OpenHandle := (inventory, authorization.keeper.slot, 0)
    let authorized := authorizeFiles (acquiredState before directory operations.slot)
    repair.bindings (directory.file .lock) = some (inventory.inode operations.slot.description) ∧
    (∃ refs : HeldLockReferences operations.slot.description,
      refs.live = inventory.references operations.slot.description ∧
      (refs.afterFileDrops drops directory authorized).owners.Owns directory operations.slot.description) ∧
    ∃ observed : FsyncObservation (fun handle => handle.2.1.description)
        (fun handle => handle.1.inode handle.2.1.description) captured authorized
        (fun _ files => settleKeeper files) (authorization.fsync captured authorized),
      observed.issuer = authorization.keeper.slot.reference ∧ observed.effective = repair.effective ∧
      repair.bindings (directory.file (.walSegment layout.keeper.first)) = some observed.effectInode := by
  intro inventory drops captured authorized
  have lockInode : inventory.inode operations.slot.description = operations.descriptors.inode operations.slot.description := by
    change authorization.keeper.inventory.inode operations.slot.description = _
    rw [repair.opened]
    rfl
  have keeperLive : authorization.keeper.slot.reference ∈
      (inventory.afterDrops drops).references authorization.keeper.slot.description :=
    (inventory.afterDrops drops).mem_references.mpr ⟨_, repair.keeperRetained, rfl, rfl⟩
  have lockLive : operations.slot.reference ∈ (inventory.afterDrops drops).references operations.slot.description :=
    (inventory.afterDrops drops).mem_references.mpr ⟨_, repair.lockRetained, rfl, rfl⟩
  let refs := inventory.held operations.slot.description (DescriptorInventory.wasLive lockLive)
  have remains : refs.remaining drops ≠ [] := by
    rw [inventory.held_remaining]
    exact List.ne_nil_of_mem lockLive
  let observed := FsyncObservation.ofInventory inventory drops
    (fun handle : OpenHandle => handle.2.1.description) (fun handle => handle.1.inode handle.2.1.description)
    captured authorization.keeper.slot.reference keeperLive rfl authorized
    (fun _ files => settleKeeper files) repair.outcome
  refine ⟨lockInode ▸ repair.lockBound, ⟨refs, rfl, ?_⟩, observed, rfl, rfl, ?_⟩
  · rw [refs.afterFileDrops_surviving remains]
    simp [authorized, authorizeFiles, acquiredState, LockOwners.Owns, LockOwners.set]
  · change repair.bindings (directory.file (.walSegment layout.keeper.first)) =
      some (authorization.keeper.inventory.inode authorization.keeper.slot.description)
    rw [authorization.keeper.sameObject]
    exact repair.keeperBound

/-- The same read and authorization select the later keeper fsync.
The directory barrier preserves its pending entry. The keeper barrier
consumes that entry on success and on error. -/
theorem keeperBarriers (repair : ListedAlignedKeeperRepair authorization) :
    let path := directory.file (.walSegment layout.keeper.first)
    let initial := acquiredState before directory operations.slot
    let authorized := authorizeFiles initial
    let captured : OpenHandle := (authorization.keeper.inventory, authorization.keeper.slot, 0)
    let remembered := operations.cache.remember path captured
    let grouped := SyncPathGroup.run (sync directory.path authorization.openRead authorization.fsync)
    readWalKeeperWithChunks operations.reads path layout.keeper.bytes.size
      authorization.keeper.metadata.byteSize.toNat (operations.cache, initial) =
        .ok layout.keeper.bytes (remembered, initial) ∧
    grouped #[directory.path] (remembered, initial) = .ok () (remembered, authorized) ∧
    grouped #[path] (remembered, authorized) =
      match authorization.fsync captured authorized with
      | .ok () after => .ok () (operations.cache.consume path, after)
      | .error cause after => .error (IO.userError s!"sync failed for '{path}': {cause}")
          (operations.cache.consume path, after) := by
  intro path initial authorized captured remembered grouped
  obtain ⟨read, routed⟩ := report.keeperRead_syncListedDirectory authorization.keeper authorization.fits
    authorization.afterListing authorization.directoryRetained authorization.bindings authorization.bound
    authorization.outcome initial authorization.openRead authorization.fsync authorization.effect
  have readExact : readWalKeeperWithChunks operations.reads path layout.keeper.bytes.size
      authorization.keeper.metadata.byteSize.toNat (operations.cache, initial) =
      .ok layout.keeper.bytes (remembered, initial) := by
    simpa only [Cache.captureKeeper, repair.aligned, ite_true, remembered, path, captured] using read
  have routedExact : sync directory.path authorization.openRead authorization.fsync directory.path
      (remembered, initial) = .ok () (remembered, authorized) := by
    simpa [Cache.captureKeeper, repair.aligned, remembered, path, captured, HeldDirectoryMarkedRetryReports.directoryBarrier,
      DescriptorInventory.delayedDirectorySync, DelayedDirectorySync.run, repair.completed, withCache, authorized,
      authorizeFiles] using routed
  refine ⟨readExact, ?_, ?_⟩
  · dsimp only [grouped]
    rw [SyncPathGroup.run_single, routedExact]
  · dsimp only [grouped, remembered]
    rw [SyncPathGroup.run_single,
      syncRemembered (keeperPath_ne_directory directory layout.keeper.first)
        captured authorization.openRead authorization.fsync authorized]
    cases authorization.fsync captured authorized with
    | ok value _ =>
      cases value
      rfl
    | error cause reached => rfl

/-- The same grouped callback wraps the error and returns the file image
actually reached by the reported keeper syscall. -/
theorem syncResult (repair : ListedAlignedKeeperRepair authorization) :
    let path := directory.file (.walSegment layout.keeper.first)
    let authorized := authorizeFiles (acquiredState before directory operations.slot)
    let captured : OpenHandle := (authorization.keeper.inventory, authorization.keeper.slot, 0)
    operations.sync operations.cache #[path] authorized.image =
      match authorization.fsync captured authorized with
      | .ok () _ => .ok () authorized.image.syncKeeper
      | .error cause _ => .error (IO.userError s!"sync failed for '{path}': {cause}")
          (if repair.effective then authorized.image.syncKeeper else authorized.image) := by
  intro path authorized captured
  let remembered := operations.cache.remember path captured
  obtain ⟨read, authorizedResult, keeper⟩ := repair.keeperBarriers
  rw [repair.projected remembered read authorizedResult, keeper]
  have outcome := repair.outcome
  change FsyncResult authorized (settleKeeper authorized) repair.effective (authorization.fsync captured authorized) at outcome
  change _ = match authorization.fsync captured authorized with
    | .ok () _ => EStateM.Result.ok () authorized.image.syncKeeper
    | .error cause _ => EStateM.Result.error (IO.userError s!"sync failed for '{path}': {cause}")
        (if repair.effective then authorized.image.syncKeeper else authorized.image)
  generalize authorization.fsync captured authorized = result at outcome ⊢
  generalize repair.effective = effective at outcome ⊢
  cases outcome <;> rfl

/-- An error from the retained keeper description is the same error
reported by the second grouped callback, with the reached file image. -/
theorem syncError (repair : ListedAlignedKeeperRepair authorization) {cause : IO.Error}
    {nativeReached : LockedFileState FileImage}
    (failed : authorization.fsync (authorization.keeper.inventory, authorization.keeper.slot, 0)
      (authorizeFiles (acquiredState before directory operations.slot)) = .error cause nativeReached) :
    let path := directory.file (.walSegment layout.keeper.first)
    operations.sync operations.cache #[path] before.image.syncDirectory =
      .error (IO.userError s!"sync failed for '{path}': {cause}")
        (if repair.effective then before.image.syncDirectory.syncKeeper else before.image.syncDirectory) := by
  have result := repair.syncResult
  dsimp only at result
  rw [failed] at result
  exact result

private theorem tailEmpty (repair : ListedAlignedKeeperRepair authorization) : layout.tail = ByteArray.empty := by
  have measured := repair.aligned.trans authorization.keeper.extent
  rw [ByteArray.size_append] at measured
  exact ByteArray.size_eq_zero_iff.mp (by omega)

private theorem hasAlignedPlan (repair : ListedAlignedKeeperRepair authorization) :
    layout.plan.alignedWithoutPrune = true := by
  have size : layout.keeper.bytes.size = layout.plan.keeperSize := layout.target.trimmedSize
  have planSize : layout.plan.keeperBytes.size = layout.plan.keeperSize := by
    simpa [CanonicalKeeperLayout.plan, repair.tailEmpty] using size
  have covers : layout.plan.keeper ≤ layout.plan.through := layout.target.firstCovered
  have valid : layout.plan.valid = true :=
    (Plan.valid_iff layout.plan).mpr ⟨covers, Nat.le_of_eq planSize.symm, by simp [CanonicalKeeperLayout.plan, repair.noLater]⟩
  have newer : layout.plan.newer = [] := repair.noLater
  simp [Plan.alignedWithoutPrune, valid, newer, planSize]

/-- Both keeper error timings come after successful directory settlement.
Only an effective keeper sync settles the exact keeper bytes. -/
theorem effects (repair : ListedAlignedKeeperRepair authorization) :
    EffectTrace layout.target before.image
      (if repair.effective then before.image.syncDirectory.syncKeeper else before.image.syncDirectory) := by
  by_cases effective : repair.effective = true
  · have empty : before.image.syncDirectory.later.DurablyEmpty := by
      simp [FileImage.syncDirectory, LaterNames.syncDirectory, LaterNames.DurablyEmpty, LaterNames.settled, repair.noLater]
    have visible : before.image.syncDirectory.keeper.active = some layout.target.trimmed := by
      change before.image.keeper.active = some layout.keeper.bytes
      simpa only [repair.tailEmpty, ByteArray.append_empty] using layout.visible
    rw [ite_eq_left effective]
    exact EffectTrace.aligned .authorized empty visible
  · rw [ite_eq_right effective]
    exact EffectTrace.authorized

/-- The exact aligned finisher returns the later grouped outcome after
the authorized state, including errors that already settled the keeper. -/
theorem finishResult (repair : ListedAlignedKeeperRepair authorization) :
    finishBoundedMarkedOpen directory layout.boundedPlan layout.plan.keeperBytes.size
      operations.removeFile (operations.write operations.cache) (operations.sync operations.cache)
      operations.renameFile before.image =
    operations.sync operations.cache #[directory.file (.walSegment layout.keeper.first)] before.image.syncDirectory := by
  have valid := (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp repair.hasAlignedPlan).1).1
  rw [layout.boundedPlan_eq_extract, finishBoundedMarkedOpen_eq_full directory layout.plan valid]
  simp only [finishMarkedOpen, repair.hasAlignedPlan, ↓reduceIte, Bind.bind, EStateM.bind,
    authorization.settles repair.completed]
  rfl

/-- The raw keeper fsync chosen by the captured pending entry. -/
abbrev keeperFsyncReturn (_repair : ListedAlignedKeeperRepair authorization) :
    EStateM.Result IO.Error (LockedFileState FileImage) Unit :=
  authorization.fsync (authorization.keeper.inventory, authorization.keeper.slot, 0)
    (authorizeFiles (acquiredState before directory operations.slot))

/-- The native keeper return and effect report supply the entire aligned
finish schedule. No separate modeled success state is required. -/
theorem healthyFinish (repair : ListedAlignedKeeperRepair authorization)
    (succeeded : ∃ reached, repair.keeperFsyncReturn = .ok () reached) :
    operations.HealthyFinish := by
  have keeperSync := repair.syncResult
  dsimp only at keeperSync
  rw [repair.outcome.completed_of_return succeeded] at keeperSync
  exact finishActions_aligned_success repair.hasAlignedPlan
    operations.removeFile (operations.write operations.cache) operations.renameFile keeperSync

/-- The shared opener installs after the two reached syncs. The exact
projected keeper callback supplies the whole aligned finish contract. -/
theorem installs {input : FilePath} (repair : ListedAlignedKeeperRepair authorization)
    (metadata : HeldMarkedMetadata report)
    (succeeded : authorization.fsync (authorization.keeper.inventory, authorization.keeper.slot, 0)
      (authorizeFiles (acquiredState before directory operations.slot)) =
      .ok () (settleKeeper (authorizeFiles (acquiredState before directory operations.slot))))
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
  authorization.installs metadata repair.completed (repair.healthyFinish ⟨_, succeeded⟩) admission keeperValid
    laterValid following accepted ordered

end ListedAlignedKeeperRepair
end Alvoki.Storage.DiskSession
