import Alvoki.Storage.Disk.Proofs.Session.CapturedAlignedInstallation
import Alvoki.Storage.Disk.Proofs.Recovery.ListedPrunedAlignedKeeper

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {published : CheckpointPublication.Image}

/-- The selected keeper survives authorization and the checked suffix
prune in the pending cache. Its final sync and the reported release leave
the owner and cached directory live. -/
structure CapturedPrunedAlignedFinish (calls : CapturedAlignedCallbacks admission)
    (reads : CapturedMarkedReadReports admission layout published)
    (vacant : TryLockObserves retry.owners directory (.ok true))
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint) where
  authorization : ListedDirectoryAuthorization (calls.heldReport reads vacant selected)
  prune : ListedLaterWalPrune authorization
  repair : ListedPrunedAlignedKeeper prune
  succeeded : ∃ reached, repair.keeperFsyncReturn = .ok () reached
  afterKeeper : List LockReferenceDrop
  released : ∃ earlier, afterKeeper = earlier ++ [authorization.keeper.slot.closeEvent]
  lockRetained : admission.owner ∈ (authorization.keeper.inventory.afterDrops
    (repair.beforeAuthorization ++ prune.afterAuthorization ++ repair.afterSuffix ++ afterKeeper)).slots
  directoryRetained : admission.cached ∈ (authorization.keeper.inventory.afterDrops
    (repair.beforeAuthorization ++ prune.afterAuthorization ++ repair.afterSuffix ++ afterKeeper)).slots

namespace CapturedPrunedAlignedFinish

variable {calls : CapturedAlignedCallbacks admission} {reads : CapturedMarkedReadReports admission layout published}
  {vacant : TryLockObserves retry.owners directory (.ok true)} {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}

theorem sameKeeper (finish : CapturedPrunedAlignedFinish calls reads vacant selected) :
    finish.authorization.keeper = reads.wal.keeper.observesFile :=
  (calls.wal reads vacant).keeperObserved finish.authorization

def reader (finish : CapturedPrunedAlignedFinish calls reads vacant selected) : CapturedKeeperOpenReports reads := by
  refine {
    beforeOpen := finish.repair.beforeKeeper
    free := ?_
    fresh := ?_
    opened := ?_
    duringRead := finish.repair.beforeAuthorization
    keeperRetained := ?_
    ownerRetained := ?_
    directoryRetained := ?_ }
  · have available := finish.repair.available
    rw [finish.sameKeeper] at available
    exact available
  · have fresh := finish.repair.fresh
    rw [finish.sameKeeper] at fresh
    exact fresh
  · have allocated := finish.repair.opened
    simp only [finish.sameKeeper] at allocated
    exact allocated
  · have keeper := finish.repair.barrierCensus.1
    rw [finish.sameKeeper] at keeper
    exact keeper
  · have owner := finish.repair.barrierCensus.2.1
    rw [finish.sameKeeper] at owner
    exact owner
  · have cached := finish.repair.barrierCensus.2.2.1
    rw [finish.sameKeeper] at cached
    exact cached

private theorem aligned (finish : CapturedPrunedAlignedFinish calls reads vacant selected) :
    layout.keeper.bytes.size = reads.wal.keeper.calls.metadata.byteSize.toNat := by
  have exact := finish.repair.aligned
  rw [finish.sameKeeper] at exact
  exact exact

def census (finish : CapturedPrunedAlignedFinish calls reads vacant selected) : DescriptorInventory :=
  finish.authorization.keeper.inventory.afterDrops
    (finish.repair.beforeAuthorization ++ finish.prune.afterAuthorization ++ finish.repair.afterSuffix ++ finish.afterKeeper)

def settled (_finish : CapturedPrunedAlignedFinish calls reads vacant selected) : LockedFileState FileImage :=
  { admission.held with image := retry.image.unlinkVisibleSuffix.syncDirectory.syncKeeper }

/-- The keeper handle was fresh at the read and is released at the last
barrier. Its stable description no longer has a slot in the final census. -/
theorem keeperReleased (finish : CapturedPrunedAlignedFinish calls reads vacant selected) :
    finish.census.references reads.wal.keeper.calls.slot.description = [] := by
  obtain ⟨earlier, release⟩ := finish.released
  let events := finish.repair.beforeAuthorization ++ finish.prune.afterAuthorization ++ finish.repair.afterSuffix ++
    earlier
  have result : finish.census = finish.reader.atOpen.afterDrops (events ++ [reads.wal.keeper.calls.slot.closeEvent]) := by
    unfold census
    rw [release, finish.sameKeeper, ← List.append_assoc]
    change reads.wal.keeper.calls.inventory.afterDrops (events ++ [reads.wal.keeper.calls.slot.closeEvent]) = _
    rw [finish.reader.opened]
    exact DescriptorInventory.insert_thenClose _ _ _ _
  have fresh : finish.reader.atOpen.references reads.wal.keeper.calls.slot.description = [] := finish.reader.fresh
  rw [result, DescriptorInventory.references_afterDrops, fresh]
  rfl

/-- The ordered unlink pass preserves the opened keeper inode. The
pending slot and lock both remain live when the keeper sync is issued. -/
theorem keeperAtSync (finish : CapturedPrunedAlignedFinish calls reads vacant selected)
    (later : ∀ first ∈ retry.image.later.visible, layout.range.through < first) :
    let reached := finish.reader.afterRead.afterDrops (finish.prune.afterAuthorization ++ finish.repair.afterSuffix)
    reads.wal.keeper.calls.slot ∈ reached.slots ∧ admission.owner ∈ reached.slots ∧
    finish.prune.reached (directory.file (.walSegment layout.keeper.first)) =
      some (reached.inode reads.wal.keeper.calls.slot.description) := by
  intro reached
  have keeper := finish.repair.keeperRetained
  have owner := finish.repair.lockRetained
  rw [finish.sameKeeper] at keeper owner
  change reads.wal.keeper.calls.slot ∈ (reads.wal.keeper.calls.inventory.afterDrops
    (finish.repair.beforeAuthorization ++ finish.prune.afterAuthorization ++ finish.repair.afterSuffix)).slots at keeper
  change admission.owner ∈ (reads.wal.keeper.calls.inventory.afterDrops
    (finish.repair.beforeAuthorization ++ finish.prune.afterAuthorization ++ finish.repair.afterSuffix)).slots at owner
  have binding := ((finish.prune.selectedBindings later).2.1 layout.keeper
    (List.mem_append_right _ (List.mem_singleton_self _))).trans finish.repair.keeperBound
  rw [finish.sameKeeper, ← reads.wal.keeper.observesFile.sameObject] at binding
  refine ⟨?_, ?_, binding⟩
  · simpa only [reached, CapturedKeeperOpenReports.afterRead, reader, DescriptorInventory.afterDrops_append,
      List.append_assoc] using keeper
  · simpa only [reached, CapturedKeeperOpenReports.afterRead, reader, DescriptorInventory.afterDrops_append,
      List.append_assoc] using owner

private abbrev BarrierState := CensusOpenState × List (List LockReferenceDrop)
private abbrev RepairState := CensusDirectoryCache × BarrierState

private def fileAction {result : Type} (action : EStateM IO.Error FileImage result) :
    EStateM IO.Error RepairState result := fun (cache, (census, before), remaining) =>
  match action before.image with
  | .ok result after => .ok result (cache, (census, { before with image := after }), remaining)
  | .error cause after => .error cause (cache, (census, { before with image := after }), remaining)

private def openForSync (finish : CapturedPrunedAlignedFinish calls reads vacant selected) (path : FilePath) :
    EStateM IO.Error BarrierState (DescriptorInventory × DescriptorSlot × Nat) := fun ((census, before), remaining) =>
  match finish.authorization.openRead path before with
  | .ok handle reached => .ok handle ((census, reached), remaining)
  | .error cause reached => .error cause ((census, reached), remaining)

private def fsyncWithCensus (finish : CapturedPrunedAlignedFinish calls reads vacant selected)
    (handle : DescriptorInventory × DescriptorSlot × Nat) : EStateM IO.Error BarrierState Unit :=
  fun ((census, before), remaining) =>
    match finish.authorization.fsync handle before with
    | .ok () reached => .ok () ((census.afterDrops (remaining.headD []), reached), remaining.tail)
    | .error cause reached => .error cause ((census, reached), remaining)

private def syncAt (finish : CapturedPrunedAlignedFinish calls reads vacant selected) (resolved : DiskDirectory) :=
  SyncPathGroup.run (sync resolved.path finish.openForSync finish.fsyncWithCensus)

private def repairStep (finish : CapturedPrunedAlignedFinish calls reads vacant selected) :=
  performPaths directory layout.boundedPlan (fun path => fileAction (calls.removeFile path)) throw
    (fun path bytes state => fileAction (calls.write state.1 path bytes) state) (finish.syncAt directory)
    (fun source target => fileAction (calls.renameFile source target))

private def repairAt (finish : CapturedPrunedAlignedFinish calls reads vacant selected)
    (resolved : DiskDirectory) (plan : Plan) (size : Nat) : EStateM IO.Error RepairState Unit :=
  finishBoundedMarkedOpen resolved plan size (fun path => fileAction (calls.removeFile path))
    (fun path bytes state => fileAction (calls.write state.1 path bytes) state) (finish.syncAt resolved)
    (fun source target => fileAction (calls.renameFile source target))

private def syncDrops (finish : CapturedPrunedAlignedFinish calls reads vacant selected) : List (List LockReferenceDrop) :=
  [finish.prune.afterAuthorization, finish.repair.afterSuffix, finish.afterKeeper]

private theorem unlinksFromCensus (finish : CapturedPrunedAlignedFinish calls reads vacant selected)
    {initial : FileImage} {bindings final : FilePath → Option Nat} {names : List Nat}
    (reports : HeldLaterWalUnlinks (calls.heldReport reads vacant selected) initial bindings names final)
    (cache : CensusDirectoryCache) (census : DescriptorInventory) (files : LockedFileState FileImage)
    (remaining : List (List LockReferenceDrop)) :
    ((names.map Step.unlink).forM finish.repairStep) (cache, (census, { files with image := initial }), remaining) =
      .ok () (cache, (census, { files with image := names.foldl FileImage.unlinkLater initial }), remaining) := by
  induction reports with
  | done => rfl
  | @step first initial bindings reached rest final head _ ih =>
    have raw : calls.removeFile (directory.file (.walSegment first)) initial =
      .ok head.raw (initial.unlinkLater first) := head.returned
    simpa only [repairStep, List.map_cons, List.foldl_cons, List.forM_eq_forM, List.forM_cons, Bind.bind,
      EStateM.bind, Pure.pure, EStateM.pure, performPaths, RunCollection.performPaths, fileAction, raw, head.accepted] using ih

private theorem syncDirectory (finish : CapturedPrunedAlignedFinish calls reads vacant selected)
    {cache : CensusDirectoryCache} {before after : LockedFileState FileImage}
    {entered : DescriptorInventory} {drops : List LockReferenceDrop} {remaining : List (List LockReferenceDrop)}
    (directoryCached : cache.directory = some (admission.reached, admission.cached, 0))
    (returned : finish.authorization.fsync (admission.reached, admission.cached, 0) before = .ok () after) :
    finish.syncAt directory #[directory.path] (cache, (entered, before), drops :: remaining) =
      .ok () (cache, (entered.afterDrops drops, after), remaining) := by
  simp [syncAt, SyncPathGroup.run_single, sync, Cache.resolve, directoryCached, fsyncWithCensus, returned, withCache]

/-- The bounded finisher selects the original directory for both
barriers, prunes the checked suffix in order, and consumes the pending
keeper at the last file sync. Its close supplies the final census. -/
theorem repairAt_returns (finish : CapturedPrunedAlignedFinish calls reads vacant selected)
    (later : ∀ first ∈ retry.image.later.visible, layout.range.through < first) :
    let keeper := (reads.wal.keeper.calls.inventory, reads.wal.keeper.calls.slot, 0)
    let remembered := admission.cache.remember (directory.file (.walSegment layout.keeper.first)) keeper
    finish.repairAt directory layout.boundedPlan layout.plan.keeperBytes.size
      (remembered, (finish.reader.afterRead, admission.held), finish.syncDrops) =
      .ok () (admission.cache, (finish.census, finish.settled), []) := by
  intro keeper remembered
  let next := finish.afterKeeper
  let afterAuthorization := finish.reader.afterRead.afterDrops finish.prune.afterAuthorization
  let afterSuffix := afterAuthorization.afterDrops finish.repair.afterSuffix
  let authorized : LockedFileState FileImage := { admission.held with image := retry.image.syncDirectory }
  let unlinked : LockedFileState FileImage := { admission.held with image := retry.image.unlinkVisibleSuffix }
  let atKeeper : LockedFileState FileImage := { admission.held with image := retry.image.unlinkVisibleSuffix.syncDirectory }
  have firstEffect := finish.authorization.effect
  rw [finish.prune.authorized] at firstEffect
  have first : finish.syncAt directory #[directory.path]
      (remembered, (finish.reader.afterRead, admission.held), finish.syncDrops) =
      .ok () (remembered, (afterAuthorization, authorized), [finish.repair.afterSuffix, next]) :=
    finish.syncDirectory rfl firstEffect
  have unlinks : ((layout.boundedPlan.newer.map Step.unlink).forM finish.repairStep)
      (remembered, (afterAuthorization, authorized), [finish.repair.afterSuffix, next]) =
      .ok () (remembered, (afterAuthorization, unlinked), [finish.repair.afterSuffix, next]) :=
    finish.unlinksFromCensus finish.prune.unlinks remembered afterAuthorization admission.held _
  have suffix : finish.syncAt directory #[directory.path]
      (remembered, (afterAuthorization, unlinked), [finish.repair.afterSuffix, next]) =
      .ok () (remembered, (afterSuffix, atKeeper), [next]) :=
    finish.syncDirectory rfl finish.prune.effect
  have keeperEffect : finish.authorization.fsync keeper atKeeper = .ok () finish.settled := by
    have effect := finish.repair.outcome.completed_of_return finish.succeeded
    change finish.authorization.fsync (finish.authorization.keeper.inventory, finish.authorization.keeper.slot, 0)
      atKeeper = .ok () finish.settled at effect
    rw [finish.sameKeeper] at effect
    exact effect
  have finalSlot : afterSuffix.afterDrops next = finish.census := by
    simp only [afterSuffix, afterAuthorization, CapturedKeeperOpenReports.afterRead, reader, next, census,
      DescriptorInventory.afterDrops_append, finish.sameKeeper, List.append_assoc]
    rfl
  let keeperPath := directory.file (.walSegment layout.keeper.first)
  have last : finish.syncAt directory #[keeperPath] (remembered, (afterSuffix, atKeeper), [next]) =
      .ok () (admission.cache, (finish.census, finish.settled), []) := by
    unfold syncAt
    rw [SyncPathGroup.run_single]
    dsimp only [remembered]
    rw [syncRemembered (file_ne_directory directory (.walSegment layout.keeper.first))]
    simp only [fsyncWithCensus, keeperEffect, List.headD_cons, List.tail_cons, finalSlot]
    rfl
  have size : layout.boundedPlan.keeperBytes.size = layout.boundedPlan.keeperSize := layout.target.trimmedSize
  have physical : layout.plan.keeperBytes.size = layout.boundedPlan.keeperSize :=
    reads.wal.keeper.observesFile.extent.symm.trans (finish.aligned.symm.trans size)
  have valid := layout.boundedPlan_valid later
  have newer : layout.boundedPlan.newer.isEmpty = false := List.isEmpty_eq_false_iff.mpr finish.repair.nonempty
  rw [repairAt]
  simp only [finishBoundedMarkedOpen, valid, size, physical, Bool.true_and, beq_self_eq_true, Nat.le_refl,
    decide_true, newer, Bool.false_and, Bool.false_eq_true, Nat.lt_irrefl, decide_false, ↓reduceIte,
    runRepairPlan, steps, List.append_assoc, Bind.bind, EStateM.bind, first]
  rw [List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM]
  change ((layout.boundedPlan.newer.map Step.unlink).forM finish.repairStep >>= fun _ =>
    ([Step.syncPruned] ++ [Step.syncKeeper]).forM finish.repairStep)
    (remembered, (afterAuthorization, authorized), [finish.repair.afterSuffix, next]) = _
  have keeperPlan : directory.file (.walSegment layout.boundedPlan.keeper) = keeperPath := rfl
  simp only [Bind.bind, EStateM.bind, unlinks]
  simp only [Bind.bind, EStateM.bind, List.cons_append, List.nil_append, List.forM_eq_forM,
    List.forM_cons, List.forM_nil, repairStep, performPaths, suffix, keeperPlan, last, Pure.pure, EStateM.pure]

private def repairActions (finish : CapturedPrunedAlignedFinish calls reads vacant selected)
    (resolved : DiskDirectory) (plan : Plan) (size : Nat) :
    EStateM IO.Error (CensusDirectoryCache × CensusOpenState) Unit := fun (cache, before) =>
  match finish.repairAt resolved plan size (cache, before, finish.syncDrops) with
  | .ok () (cache, reached, _) => .ok () (cache, reached)
  | .error cause (cache, reached, _) => .error cause (cache, reached)

/-- Use the actual reached keeper cache from the held read chronology
through authorization, ordered removals and the two final barriers. -/
def recoverFromCensus (finish : CapturedPrunedAlignedFinish calls reads vacant selected)
    (chronology : CapturedMarkedReadCensus reads finish.reader) :
    DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened :=
  fun resolved cache => finishPreparedWithCensus
    (reads.prepareFromCensus chronology.metadataRelease chronology.runs.released chronology.sealRelease
      finish.reader.readKeeperAt) (finish.repairActions resolved) cache

def runFromCensus (finish : CapturedPrunedAlignedFinish calls reads vacant selected)
    (chronology : CapturedMarkedReadCensus reads finish.reader) :
    EStateM.Result IO.Error CensusOpenState SegmentedSession :=
  calls.runWithMarked (finish.recoverFromCensus chronology)

/-- The checked reads produce the selected preparation used by the ordered prune.
The worker returns the replay and settled files before session allocation. -/
theorem recoversWithSelectedPreparation (finish : CapturedPrunedAlignedFinish calls reads vacant selected)
    (chronology : CapturedMarkedReadCensus reads finish.reader)
    (prepared : Prepared retry.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    ∃ opened,
      reads.walReads.prepare reads.reads.readPrefix (admission.reached, admission.held) =
        .ok (layout.boundedPlan, opened, layout.plan.keeperBytes.size) (admission.reached, admission.held) ∧
      finish.recoverFromCensus chronology directory admission.cache (admission.reached, admission.held) =
        .ok opened (finish.census, finish.settled) := by
  obtain ⟨opened, reached, projected⟩ := reads.preparesFromCensus chronology.manifest chronology.runs selected
    chronology.marker chronology.beforeListing finish.reader chronology.seals chronology.offsets chronology.retained
    following prepared.newer accepted ordered finish.reader.readKeeperAt (finish.reader.readsAligned finish.aligned)
  have later := prepared.newer _ List.mem_cons_self
  exact ⟨opened, projected, by simp only [recoverFromCensus, finishPreparedWithCensus, reached, repairActions,
    finish.repairAt_returns later]⟩

/-- The checked reads and ordered prune return the exact recovery result
and settled files before the session allocations. -/
theorem recoversFromCensus (finish : CapturedPrunedAlignedFinish calls reads vacant selected)
    (chronology : CapturedMarkedReadCensus reads finish.reader)
    (prepared : Prepared retry.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    ∃ opened, finish.recoverFromCensus chronology directory admission.cache (admission.reached, admission.held) =
      .ok opened (finish.census, finish.settled) := by
  obtain ⟨opened, _, recovered⟩ := finish.recoversWithSelectedPreparation chronology prepared following accepted ordered
  exact ⟨opened, recovered⟩

/-- The successful aligned prune returns the same table selected from
the physical checkpoint and WAL. The final image has no later WAL names,
and the final census retains the lock and directory and releases the keeper. -/
theorem installsFromCensus (finish : CapturedPrunedAlignedFinish calls reads vacant selected)
    (chronology : CapturedMarkedReadCensus reads finish.reader)
    {metadata : IO.FS.Metadata}
    (marker : admission.lookup (directory.file .walBoundary) (admission.reached, admission.held) =
      .ok (.ok metadata) (admission.reached, admission.held))
    (laterValid : retry.image.later.Beyond layout.range.through)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    ∃ session, finish.runFromCensus chronology = .ok session (finish.census, finish.settled) ∧
      finish.settled.image.directory.active = retry.image.directory.active ∧
      finish.settled.image.later.DurablyEmpty ∧
      admission.owner ∈ finish.census.slots ∧ admission.cached ∈ finish.census.slots ∧
      finish.census.references reads.wal.keeper.calls.slot.description = [] ∧
      CachedRetryInstalled (before := retry) reads.walReads admission.reached admission.owner reads.bindings
        published calls.liveRefs (.ok session finish.settled) := by
  obtain ⟨opened, reached, projected⟩ := reads.preparesFromCensus chronology.manifest chronology.runs selected
    chronology.marker chronology.beforeListing finish.reader chronology.seals chronology.offsets chronology.retained
    following laterValid accepted ordered finish.reader.readKeeperAt (finish.reader.readsAligned finish.aligned)
  have later := laterValid _ List.mem_cons_self
  have tailEmpty : layout.tail = ByteArray.empty := by
    have measured := finish.aligned.trans reads.wal.keeper.observesFile.extent
    rw [ByteArray.size_append] at measured
    exact ByteArray.size_eq_zero_iff.mp (by omega)
  have pruned := ListedLaterWalPrune.settledImage retry.image
  have read : retry.image.unlinkVisibleSuffix.syncDirectory.keeper.active = some layout.target.trimmed := by
    rw [pruned.2.2.2]
    change retry.image.keeper.active = some layout.keeper.bytes
    simpa only [tailEmpty, ByteArray.append_empty] using layout.visible
  have effects : EffectTrace layout.target retry.image finish.settled.image :=
    .aligned (.syncPruned ((EffectTrace.authorized (target := layout.target) (initial := retry.image)).unlinks
      retry.image.later.visible later)) pruned.1 read
  have ready : finish.settled.image.Ready layout.target :=
    FileImage.readyAfterKeeperSync (image := retry.image.unlinkVisibleSuffix.syncDirectory)
      (by rw [pruned.2.1]; rfl) (by rw [pruned.2.1]; rfl) read pruned.1
  let projectedFinish : DiskDirectory → DescriptorSlot → CensusDirectoryCache → Plan × Reopened × Nat →
      EStateM IO.Error CensusOpenState Reopened :=
    fun _ _ _ (_, opened, _) _ => .ok opened (finish.census, finish.settled)
  have same : finish.runFromCensus chronology = calls.runWithFinish reads projectedFinish := by
    unfold runFromCensus recoverFromCensus
    apply calls.runWithMarked_eq reads _ projectedFinish marker
    simp only [finishPreparedWithCensus, reached, repairActions, finish.repairAt_returns later,
      Bind.bind, EStateM.bind, projected, projectedFinish]
  obtain ⟨session, returned, installed⟩ :=
    CapturedAlignedCallbacks.installsWithFinish (calls := calls) (report := reads) vacant marker laterValid
      following accepted ordered selected projectedFinish (fun _ => rfl) ready effects
  exact ⟨session, same.trans returned, ready.selected, pruned.1, finish.lockRetained, finish.directoryRetained,
    finish.keeperReleased, installed⟩

end CapturedPrunedAlignedFinish

end Alvoki.Storage.DiskSession
