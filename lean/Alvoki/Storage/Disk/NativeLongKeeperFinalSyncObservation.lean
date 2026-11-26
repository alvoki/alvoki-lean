import Alvoki.Storage.Disk.NativeCheckpointOpenChronology
import Alvoki.Storage.Disk.NativeLongKeeperFinalSyncError
import Alvoki.Storage.Disk.NativeLongKeeperRenameError
import Alvoki.Storage.Disk.NativeLongKeeperStorage
import Alvoki.Storage.Disk.NativeLongKeeperPending
import Alvoki.Storage.Disk.NativeDurableWriteReboot
import Alvoki.Storage.Disk.NativeMarkedScanFrame
import Alvoki.Storage.Disk.NativeMarkedFirstUnlinkError
import Alvoki.Storage.Disk.NativeRetainedOpenStorage
import Alvoki.Storage.Disk.NativeWalPublicationTail

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting CheckpointPublication

private theorem NativeReadyState.selectedRetryPath_rootOrChild {state : NativeReadyState} {path : FilePath}
    (retained : state.selectedRetryPath path) :
    path = state.session.directory.path ∨ ∃ file, path = state.session.directory.file file := by
  rcases retained with marker | held
  · exact .inr ⟨.walBoundary, marker⟩
  rcases held with root | lock | manifest | sealedPath | runPath
  · exact .inl root
  · exact .inr ⟨.lock, lock⟩
  · exact .inr ⟨.manifest, manifest⟩
  · obtain ⟨segment, _, same⟩ := sealedPath
    exact .inr ⟨.walSegment segment.first, same⟩
  · obtain ⟨_, metadata, index, _, _, _, same⟩ := runPath
    exact .inr ⟨.run metadata.header.generation index, same⟩

private theorem WalRootSyncEffect.framesScopedFiles {directory : DiskDirectory} {scope : FilePath → Prop}
    {effective : Bool} {entry reached : CheckpointStorageObservation}
    (effect : WalRootSyncEffect directory effective entry reached)
    (parent : entry.Frames (· = directory.path) reached)
    (managed : ∀ path, scope path → path = directory.path ∨ ∃ file, path = directory.file file) :
    entry.files.Frames scope reached.files := by
  intro path retained
  rcases managed path retained with atRoot | ⟨file, rfl⟩
  · exact parent.visible path atRoot
  · exact ⟨effect.visible file, fun inode bound =>
      effect.bytes reached.files.names (.inl rfl) file inode ((effect.visible file).trans bound)⟩

/-- A directory fsync frames the protected child bytes for either
reported effect. Parent binding continuity is a separate effect law. -/
private theorem WalRootSyncEffect.framesSelectedRetry {state : NativeReadyState} {effective : Bool}
    {entry reached : CheckpointStorageObservation} {before after : Nat → ByteArray}
    (effect : WalRootSyncEffect state.session.directory effective entry reached)
    (parent : entry.Frames (· = state.session.directory.path) reached) (live : after = before) :
    state.SelectedRetryFrame entry reached before after := by
  have durable := effect.framesScopedFiles parent (scope := state.selectedRetryPath)
    (fun _ => NativeReadyState.selectedRetryPath_rootOrChild)
  exact ⟨fun path held => ⟨(durable path held).1, by rw [live]; intros; rfl⟩, durable, parent⟩


section PruneDirectorySync

variable {heap : Type} {directory : DiskDirectory} {view : OpenCloseHeapView heap FileImage}
  {scope : FilePath → Prop} {through : Nat} {storage : heap → CheckpointStorageObservation}
  {visible : heap → Nat → ByteArray}

/-- A reported root fsync error frames the selected files even if the
directory's child bindings have settled. The literal cached handle
identifies that root independently of the report's effect. -/
theorem AlignedKeeperCacheCallbacks.framesPruneDirectoryError
    (calls : AlignedKeeperCacheCallbacks heap)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    {before issued reached : heap} {handle : IO.FS.Handle} {cause : IO.Error} {effective : Bool}
    (loaded : calls.getDirectory cached before = .ok (some handle) issued)
    (returned : calls.syncPaths directory.path cached active pending #[directory.path] before = .error cause reached)
    (target : RawFsyncTarget view before issued handle)
    (bound : (storage issued).files.names directory.path =
      some ((view.descriptors issued).inode (view.handle issued handle).2.1.description))
    (loadFrame : SampledCheckpointRetryFrame directory scope through storage visible before issued)
    (managed : ∀ path, scope path → path = directory.path ∨ ∃ file, path = directory.file file)
    (observation : ∀ diagnostic, calls.sync handle issued = .error diagnostic reached →
      (view.handle issued handle).2.1 ∈ (view.descriptors issued).slots →
      (storage issued).files.names directory.path =
        some ((view.descriptors issued).inode (view.handle issued handle).2.1.description) →
      WalRootSyncEffect directory effective (storage issued) (storage reached) ∧
      (storage issued).Frames (· = directory.path) (storage reached) ∧
      ∀ path, scope path → ∀ inode, (storage issued).files.names path = some inode →
        visible reached inode = visible issued inode) :
    ∃ diagnostic, calls.sync handle issued = .error diagnostic reached ∧
      cause = IO.userError s!"sync failed for '{directory.path}': {diagnostic}" ∧
      SampledCheckpointRetryFrame directory scope through storage visible before reached ∧
      WalRootSyncEffect directory effective (storage issued) (storage reached) := by
  obtain ⟨diagnostic, failed, reported⟩ : ∃ diagnostic, calls.sync handle issued = .error diagnostic reached ∧
      cause = IO.userError s!"sync failed for '{directory.path}': {diagnostic}" := by
    rw [AlignedKeeperCacheCallbacks.syncPaths, SyncPathGroup.run_single] at returned
    cases raw : calls.sync handle issued with
    | ok value after =>
      cases value
      simp [syncWithHandles, Bind.bind, EStateM.bind, loaded, raw, Pure.pure, EStateM.pure] at returned
    | error diagnostic after =>
      simp [syncWithHandles, Bind.bind, EStateM.bind, loaded, raw, Pure.pure, EStateM.pure] at returned
      obtain ⟨sameCause, rfl⟩ := returned
      exact ⟨diagnostic, rfl, sameCause.symm⟩
  obtain ⟨children, parent, live⟩ := observation diagnostic failed target.live bound
  have durable := children.framesScopedFiles parent managed
  have atSync : SampledCheckpointRetryFrame directory scope through storage visible issued reached :=
    ⟨fun path selected => ⟨(durable path selected).1, fun inode named => congrArg (fun bytes => [bytes])
      (live path selected inode named)⟩,
      fun start _ => congrArg Option.isSome (children.visible (.walSegment start)), durable, parent⟩
  exact ⟨diagnostic, failed, reported, loadFrame.trans atSync, children⟩

end PruneDirectorySync

section DirectorySync

variable {heap : Type} {directory : DiskDirectory} {initial : LockedFileState FileImage}
  {history : List WAL.Write} {layout : CanonicalKeeperLayout initial.image history}
  {operations : MarkedRetryChunkOperations
    (Cache (DescriptorInventory × DescriptorSlot × Nat)) directory layout}
  {published : CheckpointPublication.Image} {held : HeldDirectoryMarkedRetryReports operations published}
  {authorized : ListedDirectoryAuthorization held} {pruning : LongKeeperPruning authorized}
  {stage : ListedLongKeeperStageAt pruning} {renamed : ListedLongKeeperRename stage}

/-- The issued final sync connects the exact bounded repair error to
its reached storage frame and live keeper. Only the observed path from
authorization to this issued descriptor needs physical frames. An
effective sync settles the reached keeper inode in every crash map. -/
theorem ListedLongKeeperDirectoryIssue.returnsSelectedRepairError
    (issue : ListedLongKeeperDirectoryIssue renamed) (view : OpenCloseHeapView heap FileImage)
    (state : NativeReadyState) (sameDirectory : state.session.directory = directory)
    (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (callbacks : AlignedKeeperCacheCallbacks heap)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (stageCalls : LongKeeperStageCallbacks heap) (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {effective : Bool} {physical : Nat}
    {start authorizedHeap pruned recorded synced renamedHeap issued reached : heap}
    {handle : IO.FS.Handle} {cause : IO.Error}
    (startFiles : (view.files start).image = initial.image)
    (measured : physical = authorized.keeper.metadata.byteSize.toNat)
    (authorize : callbacks.syncPaths directory.path cached active pending #[directory.path] start = .ok () authorizedHeap)
    (prune : let write := stageCalls.stage pending callbacks.modifyPending
      let sync := callbacks.syncPaths directory.path cached active pending
      ((layout.boundedPlan.newer.map Step.unlink ++ [Step.syncPruned]).forM
        (performPaths directory layout.boundedPlan remove throw write sync rename)) authorizedHeap = .ok () pruned)
    (written : stageCalls.stage pending callbacks.modifyPending (directory.file .stagedWal) layout.keeper.bytes pruned =
      .ok () recorded)
    (persisted : callbacks.syncPaths directory.path cached active pending #[directory.file .stagedWal] recorded = .ok () synced)
    (moved : rename (directory.file .stagedWal) (directory.file (.walSegment layout.keeper.first))
      synced = .ok () renamedHeap)
    (loaded : callbacks.getDirectory cached renamedHeap = .ok (some handle) issued)
    (atIssue : view.handle issued handle = (issue.inventory, held.lifetime.directorySlot, 0))
    (census : view.descriptors issued = issue.inventory)
    (issuedFiles : view.files issued = issue.files)
    (root : (storage issued).files.names directory.path = issue.bindings directory.path)
    (keeper : (storage issued).files.names (directory.file (.walSegment layout.keeper.first)) =
      issue.bindings (directory.file (.walSegment layout.keeper.first)))
    (scratch : (storage issued).files.names (directory.file .stagedWal) = issue.bindings (directory.file .stagedWal))
    (keeperBytes : visible issued (stage.inventory.inode stage.slot.description) = layout.target.trimmed)
    (keeperDurable : (storage issued).files.bytes (stage.inventory.inode stage.slot.description) = [layout.target.trimmed])
    (prefixFrame : state.SelectedRetryFrame (storage start) (storage issued) (visible start) (visible issued))
    (failed : callbacks.sync handle issued = .error cause reached)
    (effect : callbacks.sync handle issued = .error cause reached →
      (view.handle issued handle).2.1 ∈ (view.descriptors issued).slots →
      (storage issued).files.names directory.path =
        some ((view.descriptors issued).inode (view.handle issued handle).2.1.description) →
      view.files issued = issue.files →
      view.files reached = issue.stopped effective ∧
      WalRootSyncEffect directory effective (storage issued) (storage reached) ∧
      (storage issued).Frames (· = directory.path) (storage reached) ∧ visible reached = visible issued) :
    let write := stageCalls.stage pending callbacks.modifyPending
    let sync := callbacks.syncPaths directory.path cached active pending
    finishBoundedMarkedOpen directory layout.boundedPlan physical remove write sync rename start =
      .error (IO.userError s!"sync failed for '{directory.path}': {cause}") reached ∧
    (view.files reached).image = (issue.stopped effective).image ∧
    EffectTrace layout.target (view.files start).image (view.files reached).image ∧
    state.SelectedRetryFrame (storage start) (storage reached) (visible start) (visible reached) ∧
    RawOpenRetryTrace.KeeperAt view directory layout.target (fun atHeap => (storage atHeap).files.names) visible reached ∧
    (storage reached).files.names (directory.file (.walSegment layout.keeper.first)) =
      some (stage.inventory.inode stage.slot.description) ∧
    (storage reached).files.bytes (stage.inventory.inode stage.slot.description) = [layout.target.trimmed] ∧
    (effective = true → ∀ names ∈ (storage reached).crashNames,
      names (directory.file (.walSegment layout.keeper.first)) = some (stage.inventory.inode stage.slot.description)) := by
  intro write sync
  let names atHeap := (storage atHeap).files.names
  obtain ⟨live, bound⟩ := issue.rawDirectoryTarget view names atIssue census root
  obtain ⟨files, children, parent, unchanged⟩ := effect failed live bound issuedFiles
  obtain ⟨returned, _, trace, activeKeeper, _, _, _, _, named, _⟩ :=
    issue.rawFinalSyncError callbacks cached active pending remove stageCalls rename view names startFiles measured
      authorize prune written persisted moved loaded atIssue census issuedFiles root keeper scratch failed
      (fun _ _ _ _ => files) children.visible
  have childScope : WalRootSyncEffect state.session.directory effective (storage issued) (storage reached) :=
    sameDirectory.symm ▸ children
  have parentScope : (storage issued).Frames (· = state.session.directory.path) (storage reached) := by
    rw [sameDirectory]
    exact parent
  have durable := (children.bytes (storage reached).files.names (.inl rfl)
    (.walSegment layout.keeper.first) (stage.inventory.inode stage.slot.description) named).trans keeperDurable
  refine ⟨returned, congrArg LockedFileState.image files, trace,
    prefixFrame.trans (childScope.framesSelectedRetry parentScope unchanged), ?_, named, durable, ?_⟩
  · unfold RawOpenRetryTrace.KeeperAt
    change (view.files reached).image.keeper.active =
      (names reached (directory.file (.walSegment layout.keeper.first))).map (visible reached)
    rw [activeKeeper, named, Option.map_some, unchanged, keeperBytes]
  · intro applied names survives
    exact (children.settled applied names survives (.walSegment layout.keeper.first)).trans named

end DirectorySync

section CatalogAtError

variable {heap : Type} {view : OpenCloseHeapView heap FileImage} {directory : DiskDirectory}
  {wal : WalSegmentImage} {target : Target} {plan : Plan} {names : heap → FilePath → Option Nat}

/-- Once the actual unlink pass has returned, cleanup need only carry
canonical name presence. A later rename may exchange the keeper inode
without changing its membership in the selected namespace. -/
theorem RawOpenRetryTrace.keepsCatalogAfterPruning
    {entry beforeUnlinks afterUnlinks reached : heap} {first through : Nat}
    (initial : wal.NamespaceWindow directory first through (names entry))
    (firstCovered : first ≤ target.range.through) (cutoffCovered : target.range.through ≤ through)
    (bounded : ∀ start ∈ wal.segments.map WalSegment.first, start ≤ target.range.through)
    (beforePrune : ∀ start, first ≤ start → start ≤ target.range.through →
      (names beforeUnlinks (directory.file (.walSegment start))).isSome =
        (names entry (directory.file (.walSegment start))).isSome)
    (later : ∀ start ∈ plan.newer, target.range.through < start)
    (listed : ∀ start, target.range.through < start →
      ((names beforeUnlinks (directory.file (.walSegment start))).isSome = true ↔ start ∈ plan.newer))
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (unlink : ∀ {ordinal before after result}, ordinal ∈ plan.newer →
      remove (directory.file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () →
      names after (directory.file (.walSegment ordinal)) = none ∧
      ∀ start, start ≠ ordinal → names after (directory.file (.walSegment start)) =
        names before (directory.file (.walSegment start)))
    (returned : ((plan.newer.map Step.unlink).forM
      (performPaths directory plan remove throw write sync rename)) beforeUnlinks = .ok () afterUnlinks)
    (afterPrune : ∀ start, first ≤ start → (names reached (directory.file (.walSegment start))).isSome =
      (names afterUnlinks (directory.file (.walSegment start))).isSome)
    (laterEmpty : (view.files reached).image.later.visible = []) :
    wal.NamespaceWindow directory first through (names reached) ∧
      RawOpenRetryTrace.LaterWalAt view directory target names reached := by
  have selected := (initial.restrict (Nat.le_refl first) cutoffCovered).frame beforePrune
  have pruned := selected.afterAcceptedUnlinks bounded later (fun start beyond => (listed start beyond).mp)
    remove write sync rename unlink returned
  have complete upper := (pruned upper).frame (fun start lower _ => afterPrune start lower)
  refine ⟨complete through, ?_⟩
  intro start
  rw [laterEmpty]
  constructor
  · simp
  · rintro ⟨above, inode, named⟩
    have present : (names reached (directory.file (.walSegment start))).isSome = true := by rw [named]; rfl
    have lower := Nat.le_trans firstCovered (Nat.le_of_lt above)
    exact (Nat.not_le_of_gt above (bounded start ((complete start start lower (Nat.le_refl start)).mp present))).elim

end CatalogAtError

section ReplacementPrefix

/-- Follow the logical image of the actual rooted barriers, accepted
suffix removals, and staged fsync up to the keeper rename. Both later
error sites see this same synced stage and the same pruned catalog. -/
theorem longKeeperSyncPrefix {heap : Type} (files : heap → FileImage) (directory : DiskDirectory)
    (target : Target) (plan : Plan)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {entry authorized pruned recorded synced : heap}
    (authorize : sync #[directory.path] entry = .ok () authorized)
    (prune : ((plan.newer.map Step.unlink ++ [Step.syncPruned]).forM
      (performPaths directory plan remove throw write sync rename)) authorized = .ok () pruned)
    (written : write (directory.file .stagedWal) target.trimmed pruned = .ok () recorded)
    (persisted : sync #[directory.file .stagedWal] recorded = .ok () synced)
    (covers : ∀ ordinal ∈ (files entry).later.visible, ordinal ∈ plan.newer)
    (later : ∀ ordinal ∈ plan.newer, target.range.through < ordinal)
    (authorizationImage : sync #[directory.path] entry = .ok () authorized →
      files authorized = (files entry).syncDirectory)
    (pruneImage : ∀ {unlinked}, ((plan.newer.map Step.unlink).forM
      (performPaths directory plan remove throw write sync rename)) authorized = .ok () unlinked →
      sync #[directory.path] unlinked = .ok () pruned → files pruned = (files unlinked).syncDirectory)
    (unlink : ∀ {ordinal before after result}, ordinal ∈ plan.newer →
      remove (directory.file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () → files after = (files before).unlinkLater ordinal)
    (writeStage : write (directory.file .stagedWal) target.trimmed pruned = .ok () recorded →
      files recorded = (files pruned).withScratch (some (target.trimmed, false)))
    (syncStage : write (directory.file .stagedWal) target.trimmed pruned = .ok () recorded →
      sync #[directory.file .stagedWal] recorded = .ok () synced →
      files synced = (files recorded).withScratch (some (target.trimmed, true))) :
    EffectTrace target (files entry) (files pruned) ∧ (files pruned).later.DurablyEmpty ∧
      files synced = (files pruned).withScratch (some (target.trimmed, true)) ∧
      (files synced).keeper.active = (files entry).keeper.active := by
  have authorizedImage := authorizationImage authorize
  have allLater : ∀ ordinal ∈ (files authorized).later.visible, ordinal ∈ plan.newer := by
    rw [authorizedImage]
    exact covers
  obtain ⟨_, unlinks, syncedPrune, unlinkedImage⟩ := foldReturnedPrune directory plan remove write sync rename
    (fun projected reached => files reached = projected) FileImage.unlinkLater rfl
    (fun {ordinal _ _ _ _} member called accepted earlier =>
      (unlink member called accepted).trans (congrArg (fun image => image.unlinkLater ordinal) earlier)) prune
  have prunedImage := pruneImage unlinks syncedPrune
  have initial : EffectTrace target (files entry) (files authorized) := authorizedImage.symm ▸ .authorized
  have prunedTrace : EffectTrace target (files entry) (files pruned) := by
    rw [prunedImage, unlinkedImage]
    exact .syncPruned (initial.unlinks _ later)
  have stageImage : files synced = (files pruned).withScratch (some (target.trimmed, true)) := by
    rw [syncStage written persisted, writeStage written]
    rfl
  refine ⟨prunedTrace, ?_, stageImage, ?_⟩
  · rw [prunedImage, unlinkedImage, FileImage.syncAfterCoveringUnlinks _ _ allLater]
    exact ⟨rfl, rfl⟩
  · rw [stageImage, prunedImage, unlinkedImage, FileImage.syncAfterCoveringUnlinks _ _ allLater, authorizedImage]
    rfl

end ReplacementPrefix

section FailedMarkedRepair

variable {heap stream : Type} {view : OpenCloseHeapView heap FileImage} {directory : DiskDirectory}
  {source : RawMarkedOpenInterpreter heap stream} {entry : heap} {input : FilePath}
  {history : List WAL.Write} {layout : CanonicalKeeperLayout (view.files entry).image history}
  {published : CheckpointPublication.Image}
  {admission : CensusOpenAdmissionReports input directory (view.descriptors entry) (view.files entry)}
  {raw : RawOpenAdmissionReport admission view source.calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock}
  {reads : CapturedMarkedReadReports admission layout published} {keeper : CapturedKeeperOpenReports reads}
  {chronology : CapturedMarkedReadCensus reads keeper}
  {prepared : NativeMarkedCheckpointReadHeap seed chronology source.fileCalls}
  {slotOf : heap → stream → DescriptorSlot} {listing : MarkedDirectoryReadReport prepared source.directoryCalls slotOf}
  (extents : MarkedWalExtentReports prepared listing)
  {checkpoint : Option (PackedTable × UInt64)} {beforeKeeper afterKeeper reached : heap}
  (seals : MarkedSealReadChain seed source.fileCalls chronology.seals listing.reached beforeKeeper)
  (selected : SelectedIntegrityCheckpoint published.durable (view.files entry).image.directory.active.manifest checkpoint)
  (valid : Prepared (view.files entry).image layout.target layout.plan)
  (following : ∀ first ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
    layout.range.watermark < first)
  (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
    (view.files entry).image.directory.active.manifest)
  (ordered : WAL.OrdinalsFrom 1 history)

local notation "callbacks" => source.keeperCallbacks.withFileReads source.fileCalls
local notation "remember" => fun path handle =>
  AlignedKeeperCacheCallbacks.modifyPending callbacks seed.pendingRef (pushPending path handle)
local notation "stageWrite" => source.stage.stage seed.pendingRef (AlignedKeeperCacheCallbacks.modifyPending callbacks)
local notation "groupSync" => AlignedKeeperCacheCallbacks.syncPaths callbacks directory.path
  seed.directoryRef seed.activeRef seed.pendingRef

variable (sameStat : source.fileCalls.stat = source.calls.lookup)
  (flat : optionalMetadataWith (source.fileCalls.stat (directory.file .wal)) seed.afterPending = .ok none seed.afterPending)
  {markedMeta : IO.FS.Metadata}
  (marked : optionalMetadataWith (source.fileCalls.stat (directory.file .walBoundary)) seed.afterPending =
    .ok (some markedMeta) seed.afterPending)
  (keeperRead : source.fileCalls.readKeeperWithRelease
    (fun path handle => (source.keeperCallbacks.withFileReads source.fileCalls).modifyPending seed.pendingRef
      (pushPending path handle))
    (directory.file (.walSegment layout.keeper.first)) layout.keeper.bytes.size
    reads.wal.keeper.calls.metadata.byteSize.toNat beforeKeeper = .ok layout.keeper.bytes afterKeeper)

include extents seals selected valid following accepted ordered sameStat flat marked keeperRead

/-- Carry a scoped frame from the checked reader through the actual
failed repair, cache disposal, unlock and lock release. The unlock can
replace the worker's error in the public diagnostic. -/
theorem MarkedWalExtentReports.finalizesFailedRepairWithFrame
    {frame : heap → heap → Prop} (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (readerFrames : source.fileCalls.ScopeFrames frame)
    (listingFrames : source.directoryCalls.ScopeFrames directory frame)
    (keeperFrame : frame beforeKeeper afterKeeper)
    {cause : IO.Error}
    (repair : finishBoundedMarkedOpen directory layout.boundedPlan reads.wal.keeper.calls.metadata.byteSize.toNat
      source.remove stageWrite groupSync source.rename afterKeeper = .error cause reached)
    (repairFrame : frame afterKeeper reached)
    (dispose : RawOpenCacheDisposal (admitted := raw) seed reached)
    (sameDisposal : source.dispose = dispose.dispose)
    (owner : (view.files reached).owners = admission.held.owners)
    (finalized : RawOpenErrorLockFinalization view directory source.release raw.lock admission.owner dispose.reached)
    (scope : dispose.ScopeFrames finalized frame) :
    source.openTable input entry = .error (dispose.diagnostic cause) finalized.reached ∧
      frame entry finalized.reached ∧ (view.files finalized.reached).image = (view.files reached).image := by
  let worker := source.worker seed.directoryRef seed.activeRef seed.pendingRef
  have rejected := extents.workerReturnsFailedRepair source (raw := raw) seals selected valid following accepted ordered
    sameStat flat marked keeperRead repair
  have disposed := dispose.returnsAt worker cause rejected rfl owner
  obtain ⟨_, _, _, _, _, _, _, _, _, image, _⟩ := dispose.returnsAfterLockFinalizationAt worker cause disposed finalized
  obtain ⟨toListing, toKeeper⟩ := listing.framesThroughSeals selected seals frame refl trans readerFrames listingFrames
  exact ⟨dispose.returnsMarkedInterpreter source sameDisposal (rejected _) finalized,
    scope.preserves trans (trans (trans toListing toKeeper) (trans keeperFrame repairFrame)), image⟩

variable {scope : FilePath → Prop} {through : Nat}
  {observe : heap → CheckpointStorageObservation} {readBytes : heap → Nat → ByteArray}

local notation "sampledFrame" => SampledCheckpointRetryFrame directory scope through observe readBytes

/-- Both a failed suffix removal and an error at the following root
barrier extend the same failed-open chronology. Accepted removals
retain their effects at the error heap. -/
theorem MarkedWalExtentReports.extendsCheckpointRetryAfterFailedWalPruneBlock
    {first : heap} {earlier : List (FilePath × IO.Error)} (prior : source.FailedCalls first earlier entry)
    (readerFrames : source.fileCalls.ScopeFrames sampledFrame)
    (listingFrames : source.directoryCalls.ScopeFrames directory sampledFrame)
    (remembered : ∀ {path file before after}, remember path file before = .ok () after → sampledFrame before after)
    {authorized : heap} {cause : IO.Error}
    (authorization : groupSync #[directory.path] afterKeeper = .ok () authorized)
    (authorizedFrame : sampledFrame afterKeeper authorized)
    (needsPrune : layout.boundedPlan.newer ≠ [] ∨ layout.boundedPlan.keeperSize < reads.wal.keeper.calls.metadata.byteSize.toNat)
    (cutoff : through ≤ layout.boundedPlan.through)
    (outside : ∀ ordinal ∈ layout.boundedPlan.newer, ¬ scope (directory.file (.walSegment ordinal)))
    (unlink : SampledCheckpointRetryFrame.WalUnlinkEffects directory scope through observe readBytes
      layout.boundedPlan source.remove)
    (stopped : ((layout.boundedPlan.newer.map Step.unlink ++ [Step.syncPruned]).forM
      (performPaths directory layout.boundedPlan source.remove throw stageWrite groupSync source.rename)) authorized =
      .error cause reached)
    (barrier : ∀ {unlinked}, ((layout.boundedPlan.newer.map Step.unlink).forM
      (performPaths directory layout.boundedPlan source.remove throw stageWrite groupSync source.rename)) authorized =
        .ok () unlinked → groupSync #[directory.path] unlinked = .error cause reached →
      ∃ (issued : heap) (handle : IO.FS.Handle) (effective : Bool),
        (callbacks).getDirectory seed.directoryRef unlinked = .ok (some handle) issued ∧
        RawFsyncTarget view unlinked issued handle ∧
        (observe issued).files.names directory.path =
          some ((view.descriptors issued).inode (view.handle issued handle).2.1.description) ∧
        sampledFrame unlinked issued ∧
        (∀ path, scope path → path = directory.path ∨ ∃ file, path = directory.file file) ∧
        ∀ diagnostic, (callbacks).sync handle issued = .error diagnostic reached →
          WalRootSyncEffect directory effective (observe issued) (observe reached) ∧
          (observe issued).Frames (· = directory.path) (observe reached) ∧
          ∀ path, scope path → ∀ inode, (observe issued).files.names path = some inode →
            readBytes reached inode = readBytes issued inode)
    (dispose : RawOpenCacheDisposal (admitted := raw) seed reached)
    (sameDisposal : source.dispose = dispose.dispose)
    (owner : (view.files reached).owners = admission.held.owners)
    (finalized : RawOpenErrorLockFinalization view directory source.release raw.lock admission.owner dispose.reached)
    (cleanup : dispose.ScopeFrames finalized sampledFrame) :
    source.openTable input entry = .error (dispose.diagnostic cause) finalized.reached ∧
      source.FailedCalls first (earlier ++ [(input, dispose.diagnostic cause)]) finalized.reached ∧
      sampledFrame entry finalized.reached := by
  have bytes : layout.boundedPlan.keeperBytes.size = layout.boundedPlan.keeperSize := layout.target.trimmedSize
  have checked := layout.boundedPlan_valid ((Plan.valid_iff layout.plan).mp valid.valid).2.2
  have extent : reads.wal.keeper.calls.metadata.byteSize.toNat = (layout.keeper.bytes ++ layout.tail).size :=
    reads.wal.keeper.observesFile.extent
  have bounded : layout.boundedPlan.keeperSize ≤ reads.wal.keeper.calls.metadata.byteSize.toNat := by
    rw [← bytes]
    change layout.keeper.bytes.size ≤ reads.wal.keeper.calls.metadata.byteSize.toNat
    rw [extent]
    simp
  obtain ⟨repair, repairFrame⟩ := SampledCheckpointRetryFrame.afterFailedWalPruneBlock checked bytes bounded
    needsPrune cutoff outside authorization authorizedFrame unlink stopped (fun unlinks returned => by
      obtain ⟨_, _, _, loaded, target, bound, load, managed, physical⟩ := barrier unlinks returned
      obtain ⟨_, _, _, framed, _⟩ := (callbacks).framesPruneDirectoryError seed.directoryRef seed.activeRef seed.pendingRef
        loaded returned target bound load managed (fun diagnostic failed _ _ => physical diagnostic failed)
      exact framed)
  have keeperFrame := source.fileCalls.readKeeperKeepsFrame readerFrames SampledCheckpointRetryFrame.refl
    SampledCheckpointRetryFrame.trans remember remembered _ _ _ keeperRead
  obtain ⟨returned, framed, _⟩ := extents.finalizesFailedRepairWithFrame seals selected valid following accepted ordered
    (frame := sampledFrame)
    sameStat flat marked keeperRead SampledCheckpointRetryFrame.refl SampledCheckpointRetryFrame.trans readerFrames
    listingFrames keeperFrame repair repairFrame dispose sameDisposal owner finalized cleanup
  exact ⟨returned, .next prior input returned, framed⟩

end FailedMarkedRepair

section SelectedRetry

private def keepsWalNames {heap : Type} (directory : DiskDirectory) (names : heap → FilePath → Option Nat)
    (before after : heap) : Prop :=
  ∀ start, (names after (directory.file (.walSegment start))).isSome =
    (names before (directory.file (.walSegment start))).isSome

variable {heap stream : Type} {view : OpenCloseHeapView heap FileImage} {state : NativeReadyState}
  {source : RawMarkedOpenInterpreter heap stream} {first entry : heap} {input : FilePath}
  {target : Target} {storage : heap → CheckpointStorageObservation} {visible : heap → Nat → ByteArray}
  {earlier : List (FilePath × IO.Error)} {prior : source.FailedCalls first earlier entry}
  {firstOffset through : Nat} {keep : heap → Prop}

local notation "dir" => state.session.directory
local notation "retryNames" => fun atHeap => CheckpointSurvivingFiles.names (CheckpointStorageObservation.files (storage atHeap))
local notation "liveFiles" => fun atHeap => CheckpointSurvivingFiles.mk (retryNames atHeap) fun inode => [visible atHeap inode]
local notation "catalog" => fun atHeap => state.writer.wal.NamespaceWindow dir firstOffset through (retryNames atHeap)
local notation "selectedWal" => fun atHeap => catalog atHeap ∧
  RawOpenRetryTrace.KeeperAt view dir target retryNames visible atHeap ∧
  state.SelectedRetryDurability target (storage atHeap) ∧
    RawOpenRetryTrace.LaterWalAt view dir target retryNames atHeap
local notation "walNameFrame" => keepsWalNames dir retryNames
local notation "retryFrame" => fun entry reached =>
  state.SelectedRetryFrame (storage entry) (storage reached) (visible entry) (visible reached)

variable {history : List WAL.Write} {layout : CanonicalKeeperLayout (view.files entry).image history}
  {published : CheckpointPublication.Image}
  {admission : CensusOpenAdmissionReports input state.session.directory (view.descriptors entry) (view.files entry)}
  {raw : RawOpenAdmissionReport admission view source.calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock}
  {reads : CapturedMarkedReadReports admission layout published} {keeper : CapturedKeeperOpenReports reads}
  {chronology : CapturedMarkedReadCensus reads keeper}
  {prepared : NativeMarkedCheckpointReadHeap seed chronology source.fileCalls}
  {slotOf : heap → stream → DescriptorSlot} {listing : MarkedDirectoryReadReport prepared source.directoryCalls slotOf}
  (extents : MarkedWalExtentReports prepared listing)

include extents

/-- Follow the selected reads and bounded repair on the cache allocated
by this open. The cleanup exposes the worker's changed keeper to the
next attempt and transports the earlier durable selections separately. -/
theorem MarkedWalExtentReports.extendsFailedRepair
    (before : RawOpenRetryTrace.SelectedEffects view source first target liveFiles state.selectedRetryPath keep prior)
    (sameTarget : layout.target = target)
    {checkpoint : Option (PackedTable × UInt64)} {beforeKeeper afterKeeper reached : heap}
    (seals : MarkedSealReadChain seed source.fileCalls chronology.seals listing.reached beforeKeeper)
    (selected : SelectedIntegrityCheckpoint published.durable (view.files entry).image.directory.active.manifest checkpoint)
    (valid : Prepared (view.files entry).image layout.target layout.plan)
    (following : ∀ first ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < first)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      (view.files entry).image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (sameStat : source.fileCalls.stat = source.calls.lookup)
    (flat : optionalMetadataWith (source.fileCalls.stat ((dir).file .wal)) seed.afterPending = .ok none seed.afterPending)
    {markedMeta : IO.FS.Metadata}
    (marked : optionalMetadataWith (source.fileCalls.stat ((dir).file .walBoundary)) seed.afterPending =
      .ok (some markedMeta) seed.afterPending)
    (keeperRead : source.fileCalls.readKeeperWithRelease
      (fun path handle => (source.keeperCallbacks.withFileReads source.fileCalls).modifyPending seed.pendingRef (pushPending path handle))
      ((dir).file (.walSegment layout.keeper.first)) layout.keeper.bytes.size
      reads.wal.keeper.calls.metadata.byteSize.toNat beforeKeeper = .ok layout.keeper.bytes afterKeeper)
    (readerFrames : source.fileCalls.ScopeFrames retryFrame)
    (listingFrames : source.directoryCalls.ScopeFrames dir retryFrame)
    (keeperFrame : retryFrame beforeKeeper afterKeeper)
    {cause : IO.Error}
    (repair : let sync := source.keeperCallbacks.withFileReads source.fileCalls
      finishBoundedMarkedOpen dir layout.boundedPlan reads.wal.keeper.calls.metadata.byteSize.toNat
        source.remove (source.stage.stage seed.pendingRef sync.modifyPending)
        (sync.syncPaths (dir).path seed.directoryRef seed.activeRef seed.pendingRef) source.rename afterKeeper =
      .error cause reached)
    (effects : EffectTrace layout.target (view.files entry).image (view.files reached).image)
    (repairFrame : retryFrame afterKeeper reached)
    (keeperAtError : RawOpenRetryTrace.KeeperAt view dir target retryNames visible reached)
    (dispose : RawOpenCacheDisposal (admitted := raw) seed reached)
    (sameDisposal : source.dispose = dispose.dispose)
    (owner : (view.files reached).owners = admission.held.owners)
    (finalized : RawOpenErrorLockFinalization view dir source.release raw.lock admission.owner dispose.reached)
    (scope : dispose.ScopeFrames finalized retryFrame)
    (keeperCleanup : (liveFiles reached).Frames (· = (dir).file (.walSegment target.first))
      (liveFiles finalized.reached))
    (durability : keep entry → state.SelectedRetryDurability target (storage entry))
    (carries : (view.files finalized.reached).image = (view.files reached).image →
      RawOpenRetryTrace.KeeperAt view dir target retryNames visible finalized.reached →
      state.SelectedRetryDurability target (storage finalized.reached) → keep entry → keep finalized.reached) :
    ∃ returned : source.openTable input entry = .error (dispose.diagnostic cause) finalized.reached,
      RawOpenRetryTrace.SelectedEffects view source first target liveFiles state.selectedRetryPath keep
        (prior.next input returned) ∧ (view.files finalized.reached).image = (view.files reached).image := by
  obtain ⟨returned, kept, image⟩ := extents.finalizesFailedRepairWithFrame seals selected valid following accepted ordered
    (frame := retryFrame)
    sameStat flat marked keeperRead (fun atHeap => NativeReadyState.SelectedRetryFrame.refl state (storage atHeap) (visible atHeap))
    NativeReadyState.SelectedRetryFrame.trans readerFrames listingFrames keeperFrame repair repairFrame dispose sameDisposal
    owner finalized scope
  have keeperAt : RawOpenRetryTrace.KeeperAt view dir target retryNames visible finalized.reached := by
    unfold RawOpenRetryTrace.KeeperAt at keeperAtError ⊢
    rw [image, keeperAtError]
    exact (keeperCleanup.visiblePayload (names := retryNames) (bytes := visible) rfl).symm
  have trace : EffectTrace target (view.files entry).image (view.files finalized.reached).image := by
    rw [image, ← sameTarget]
    exact effects
  exact ⟨returned, .append (calls := .next .empty input returned) before (.inr trace) kept.live
    (fun selected => carries image keeperAt ((durability selected).frame kept.durable kept.parent) selected), image⟩

local notation "callbacks" => source.keeperCallbacks.withFileReads source.fileCalls
local notation "stageWrite" => LongKeeperStageCallbacks.stage source.stage seed.pendingRef (AlignedKeeperCacheCallbacks.modifyPending callbacks)
local notation "groupSync" => AlignedKeeperCacheCallbacks.syncPaths callbacks (DiskDirectory.path dir) seed.directoryRef seed.activeRef seed.pendingRef

omit extents in
/-- Move the selected catalog through the literal reader, the accepted
suffix pass, and the common stage sync. Only the reached suffix error
and the two cleanup paths can extend this name frame beyond that stage. -/
private theorem MarkedDirectoryReadReport.carriesPrunedCatalog
    (listing : MarkedDirectoryReadReport prepared source.directoryCalls slotOf)
    {checkpoint : Option (PackedTable × UInt64)}
    {beforeKeeper afterKeeper authorized pruned synced reached : heap}
    (seals : MarkedSealReadChain seed source.fileCalls chronology.seals listing.reached beforeKeeper)
    (selected : SelectedIntegrityCheckpoint published.durable (view.files entry).image.directory.active.manifest checkpoint)
    (prune : ((layout.boundedPlan.newer.map Step.unlink ++ [Step.syncPruned]).forM
      (performPaths dir layout.boundedPlan source.remove throw stageWrite groupSync source.rename)) authorized = .ok () pruned)
    (dispose : RawOpenCacheDisposal (admitted := raw) seed reached)
    (finalized : RawOpenErrorLockFinalization view dir source.release raw.lock admission.owner dispose.reached)
    (readerNames : source.fileCalls.ScopeFrames walNameFrame)
    (listingNames : source.directoryCalls.ScopeFrames dir walNameFrame)
    (keeperNames : walNameFrame beforeKeeper afterKeeper)
    (authorizationNames : walNameFrame afterKeeper authorized)
    (namesThroughStage : ∀ {unlinked}, ((layout.boundedPlan.newer.map Step.unlink).forM
      (performPaths dir layout.boundedPlan source.remove throw stageWrite groupSync source.rename)) authorized = .ok () unlinked →
      groupSync #[(dir).path] unlinked = .ok () pruned → walNameFrame unlinked synced)
    (namesOfError : walNameFrame synced reached)
    (namesOfCleanup : dispose.ScopeFrames finalized walNameFrame)
    (firstCovered : firstOffset ≤ target.range.through)
    (cutoffCovered : target.range.through ≤ through)
    (bounded : ∀ start ∈ state.writer.wal.segments.map WalSegment.first, start ≤ target.range.through)
    (later : ∀ ordinal ∈ layout.boundedPlan.newer, target.range.through < ordinal)
    (listed : ∀ start, target.range.through < start →
      ((retryNames authorized ((dir).file (.walSegment start))).isSome = true ↔ start ∈ layout.boundedPlan.newer))
    (unlinkNames : ∀ {ordinal before after result}, ordinal ∈ layout.boundedPlan.newer →
      source.remove ((dir).file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () →
      retryNames after ((dir).file (.walSegment ordinal)) = none ∧
      ∀ start, start ≠ ordinal →
        retryNames after ((dir).file (.walSegment start)) = retryNames before ((dir).file (.walSegment start)))
    (initial : catalog entry) (gone : (view.files finalized.reached).image.later.visible = []) :
    catalog finalized.reached ∧ RawOpenRetryTrace.LaterWalAt view dir target retryNames finalized.reached := by
  obtain ⟨unlinked, unlinks, suffixSync⟩ :=
    returnedWalUnlinksAndBarrier dir layout.boundedPlan source.remove stageWrite groupSync source.rename prune
  have trans {first middle last : heap} (before : walNameFrame first middle)
      (after : walNameFrame middle last) : walNameFrame first last := fun start => (after start).trans (before start)
  obtain ⟨throughListing, throughSeals⟩ :=
    listing.framesThroughSeals selected seals walNameFrame (fun _ _ => rfl) trans readerNames listingNames
  have admission := raw.framesThroughCache seed (frame := walNameFrame) trans namesOfCleanup.admission
  have beforePrune := trans (trans admission (trans throughListing throughSeals))
    (trans keeperNames authorizationNames)
  have afterPrune := trans (namesThroughStage unlinks suffixSync)
    (trans namesOfError (namesOfCleanup.afterWorker trans))
  exact RawOpenRetryTrace.keepsCatalogAfterPruning (view := view) (target := target) (names := retryNames)
    initial firstCovered cutoffCovered bounded (fun start _ _ => beforePrune start) later listed
    source.remove stageWrite groupSync source.rename unlinkNames unlinks (fun start _ => afterPrune start) gone

/-- Feed the actual repair stopped by the final directory fsync into
the same fixed opener's cleanup and failed-call prefix. This applies
to whichever WAL target the preceding operation left selected. -/
theorem MarkedWalExtentReports.extendsFinalSyncError
    {operations : MarkedRetryChunkOperations
      (SyncHandleRouting.Cache (DescriptorInventory × DescriptorSlot × Nat)) dir layout}
    {held : HeldDirectoryMarkedRetryReports operations published}
    {authorization : ListedDirectoryAuthorization held} {pruning : LongKeeperPruning authorization}
    {staged : ListedLongKeeperStageAt pruning} {renamed : ListedLongKeeperRename staged}
    (issue : ListedLongKeeperDirectoryIssue renamed)
    (before : RawOpenRetryTrace.SelectedEffects view source first target liveFiles state.selectedRetryPath selectedWal prior)
    (sameTarget : layout.target = target)
    {checkpoint : Option (PackedTable × UInt64)} {beforeKeeper afterKeeper reached : heap}
    (seals : MarkedSealReadChain seed source.fileCalls chronology.seals listing.reached beforeKeeper)
    (selected : SelectedIntegrityCheckpoint published.durable (view.files entry).image.directory.active.manifest checkpoint)
    (valid : Prepared (view.files entry).image layout.target layout.plan)
    (following : ∀ first ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < first)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      (view.files entry).image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (sameStat : source.fileCalls.stat = source.calls.lookup)
    (flat : optionalMetadataWith (source.fileCalls.stat ((dir).file .wal)) seed.afterPending = .ok none seed.afterPending)
    {markedMeta : IO.FS.Metadata}
    (marked : optionalMetadataWith (source.fileCalls.stat ((dir).file .walBoundary)) seed.afterPending =
      .ok (some markedMeta) seed.afterPending)
    (keeperRead : source.fileCalls.readKeeperWithRelease
      (fun path handle => (callbacks).modifyPending seed.pendingRef (pushPending path handle))
      ((dir).file (.walSegment layout.keeper.first)) layout.keeper.bytes.size
      reads.wal.keeper.calls.metadata.byteSize.toNat beforeKeeper = .ok layout.keeper.bytes afterKeeper)
    (readerFrames : source.fileCalls.ScopeFrames retryFrame)
    (listingFrames : source.directoryCalls.ScopeFrames dir retryFrame)
    (keeperFrame : retryFrame beforeKeeper afterKeeper)
    {authorized pruned recorded synced renamedHeap issued : heap}
    {handle : IO.FS.Handle} {cause : IO.Error} {effective : Bool}
    (startFiles : (view.files afterKeeper).image = (view.files entry).image)
    (measured : reads.wal.keeper.calls.metadata.byteSize.toNat = authorization.keeper.metadata.byteSize.toNat)
    (authorize : groupSync #[(dir).path] afterKeeper = .ok () authorized)
    (prune : ((layout.boundedPlan.newer.map Step.unlink ++ [Step.syncPruned]).forM
      (performPaths dir layout.boundedPlan source.remove throw stageWrite groupSync source.rename)) authorized = .ok () pruned)
    (written : stageWrite ((dir).file .stagedWal) layout.keeper.bytes pruned = .ok () recorded)
    (persisted : groupSync #[((dir).file .stagedWal)] recorded = .ok () synced)
    (moved : source.rename ((dir).file .stagedWal) ((dir).file (.walSegment layout.keeper.first))
      synced = .ok () renamedHeap)
    (loaded : (callbacks).getDirectory seed.directoryRef renamedHeap = .ok (some handle) issued)
    (atIssue : view.handle issued handle = (issue.inventory, held.lifetime.directorySlot, 0))
    (census : view.descriptors issued = issue.inventory)
    (issuedFiles : view.files issued = issue.files)
    (root : retryNames issued (dir).path = issue.bindings (dir).path)
    (keeper : retryNames issued ((dir).file (.walSegment layout.keeper.first)) =
      issue.bindings ((dir).file (.walSegment layout.keeper.first)))
    (scratch : retryNames issued ((dir).file .stagedWal) = issue.bindings ((dir).file .stagedWal))
    (keeperBytes : visible issued (staged.inventory.inode staged.slot.description) = layout.target.trimmed)
    (keeperDurable : (storage issued).files.bytes (staged.inventory.inode staged.slot.description) = [layout.target.trimmed])
    (authorizedFrame : retryFrame afterKeeper authorized)
    (currentReady : state.Valid) (targetAtKeeper : layout.target.first = state.writer.wal.active.first)
    (unlinkFrame : ∀ {ordinal before after result}, ordinal ∈ layout.boundedPlan.newer →
      source.remove ((dir).file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () →
      (liveFiles before).Frames (· ≠ (dir).file (.walSegment ordinal)) (liveFiles after) ∧
      (storage before).files.Frames (· ≠ (dir).file (.walSegment ordinal)) (storage after).files ∧
      (storage before).Frames (· = (dir).path) (storage after))
    (suffixSyncFrame : ∀ {before after}, groupSync #[(dir).path] before = .ok () after → retryFrame before after)
    (stageFrame : retryFrame pruned synced) (renameFrame : retryFrame synced renamedHeap)
    (loadFrame : retryFrame renamedHeap issued)
    (failed : (callbacks).sync handle issued = .error cause reached)
    (effect : (callbacks).sync handle issued = .error cause reached →
      (view.handle issued handle).2.1 ∈ (view.descriptors issued).slots →
      retryNames issued (dir).path =
        some ((view.descriptors issued).inode (view.handle issued handle).2.1.description) →
      view.files issued = issue.files →
      view.files reached = issue.stopped effective ∧
      WalRootSyncEffect dir effective (storage issued) (storage reached) ∧
      (storage issued).Frames (· = (dir).path) (storage reached) ∧ visible reached = visible issued)
    (dispose : RawOpenCacheDisposal (admitted := raw) seed reached)
    (sameDisposal : source.dispose = dispose.dispose)
    (owner : (view.files reached).owners = admission.held.owners)
    (finalized : RawOpenErrorLockFinalization view dir source.release raw.lock admission.owner dispose.reached)
    (scope : dispose.ScopeFrames finalized retryFrame)
    (keeperCleanup : (liveFiles reached).Frames (· = (dir).file (.walSegment target.first))
      (liveFiles finalized.reached))
    (readerNames : source.fileCalls.ScopeFrames walNameFrame)
    (listingNames : source.directoryCalls.ScopeFrames dir walNameFrame)
    (keeperNames : walNameFrame beforeKeeper afterKeeper)
    (namesOfDirectorySync : ∀ {before after}, groupSync #[(dir).path] before = .ok () after → walNameFrame before after)
    (namesOfStageWrite : walNameFrame pruned recorded)
    (namesOfStageSync : walNameFrame recorded synced)
    (namesOfRename : walNameFrame synced renamedHeap)
    (namesOfLoad : walNameFrame renamedHeap issued)
    (namesOfCleanup : dispose.ScopeFrames finalized walNameFrame)
    (firstCovered : firstOffset ≤ target.range.through)
    (cutoffCovered : target.range.through ≤ through)
    (bounded : ∀ start ∈ state.writer.wal.segments.map WalSegment.first, start ≤ target.range.through)
    (listed : ∀ start, target.range.through < start →
      ((retryNames authorized ((dir).file (.walSegment start))).isSome = true ↔ start ∈ layout.boundedPlan.newer))
    (unlinkNames : ∀ {ordinal before after result}, ordinal ∈ layout.boundedPlan.newer →
      source.remove ((dir).file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () →
      retryNames after ((dir).file (.walSegment ordinal)) = none ∧
      ∀ start, start ≠ ordinal →
        retryNames after ((dir).file (.walSegment start)) = retryNames before ((dir).file (.walSegment start)))
    (keeperStorage : (storage reached).files.Frames (· = (dir).file (.walSegment layout.keeper.first))
      (storage finalized.reached).files) :
    ∃ returned : source.openTable input entry =
        .error (dispose.diagnostic (IO.userError s!"sync failed for '{(dir).path}': {cause}")) finalized.reached,
      RawOpenRetryTrace.SelectedEffects view source first target liveFiles state.selectedRetryPath selectedWal
        (prior.next input returned) ∧
      retryNames finalized.reached ((dir).file (.walSegment layout.keeper.first)) =
        some (staged.inventory.inode staged.slot.description) ∧
      (storage finalized.reached).files.bytes (staged.inventory.inode staged.slot.description) = [layout.target.trimmed] ∧
      (view.files finalized.reached).image.keeper.active = some target.trimmed ∧
      (view.files finalized.reached).image.later.DurablyEmpty := by
  have prunedFrame := framesReturnedPrune dir layout.boundedPlan source.remove stageWrite groupSync source.rename
    retryFrame (fun atHeap => NativeReadyState.SelectedRetryFrame.refl state (storage atHeap) (visible atHeap))
    (fun first last => first.trans last) (unlink := by
      intro ordinal before after result member removed accepted
      obtain ⟨live, durable, parent⟩ := unlinkFrame member removed accepted
      have afterTarget : layout.range.through < ordinal := pruning.later ordinal member
      have covers : state.writer.wal.active.first ≤ layout.range.through :=
        targetAtKeeper ▸ layout.target.firstCovered
      have separate (path : FilePath) (inside : state.selectedRetryPath path) :
          path ≠ (dir).file (.walSegment ordinal) :=
        state.protectedPathNeWalFromActive currentReady inside (Nat.le_trans covers (Nat.le_of_lt afterTarget))
      exact ⟨fun path inside => live path (separate path inside),
        fun path inside => durable path (separate path inside), parent⟩)
    suffixSyncFrame prune
  have reachedIssue := authorizedFrame.trans (prunedFrame.trans (stageFrame.trans (renameFrame.trans loadFrame)))
  obtain ⟨repair, workerImage, trace, carried, kept, named, durable, _⟩ :=
    issue.returnsSelectedRepairError view state rfl storage visible callbacks seed.directoryRef seed.activeRef seed.pendingRef
      source.remove source.stage source.rename startFiles measured authorize prune written persisted moved loaded atIssue
      census issuedFiles root keeper scratch keeperBytes keeperDurable reachedIssue failed effect
  obtain ⟨liveRoot, rootBinding⟩ := issue.rawDirectoryTarget view retryNames atIssue census root
  have errorNames : walNameFrame synced reached := fun start =>
    (congrArg Option.isSome ((effect failed liveRoot rootBinding issuedFiles).2.1.visible (.walSegment start))).trans
      ((namesOfLoad start).trans (namesOfRename start))
  have laterBound (ordinal : Nat) (member : ordinal ∈ layout.boundedPlan.newer) : target.range.through < ordinal :=
    sameTarget ▸ pruning.later ordinal member
  rw [startFiles] at trace
  obtain ⟨returned, selectedEffects, finalImage⟩ := extents.extendsFailedRepair before sameTarget seals selected valid following accepted ordered sameStat flat marked
    keeperRead readerFrames listingFrames keeperFrame repair trace carried (sameTarget ▸ kept) dispose sameDisposal owner
    finalized scope keeperCleanup (fun initial => initial.2.2.1) (by
      intro image finalKeeper finalDurability initial
      have gone : (view.files finalized.reached).image.later.visible = [] := by
        rw [image, workerImage]
        exact (issue.visibleAfterRename effective).2.1
      obtain ⟨nextWindow, nextSuffix⟩ := listing.carriesPrunedCatalog
        seals selected prune dispose finalized readerNames listingNames keeperNames (namesOfDirectorySync authorize)
        (fun _ sync start => (namesOfStageSync start).trans ((namesOfStageWrite start).trans ((namesOfDirectorySync sync) start)))
        errorNames namesOfCleanup firstCovered cutoffCovered bounded
        laterBound listed unlinkNames initial.1 gone
      exact ⟨nextWindow, finalKeeper, finalDurability, nextSuffix⟩)
  obtain ⟨sameName, sameBytes⟩ := keeperStorage _ rfl
  refine ⟨returned, selectedEffects, sameName.trans named, (sameBytes _ named).trans durable, ?_⟩
  rw [finalImage, workerImage, ← sameTarget]
  exact issue.visibleAfterRename effective

/-- Maintain the prior writer's file footprint while identifying the
cached descriptor allocated by this actual retry. -/
private def repairRootScope (state : NativeReadyState) (current : DescriptorInventory) (cached : DescriptorSlot) :
    NativeReadyState := { state with census := current, directorySlot := cached }

/-- The actual failed replacement rename, including a reported move
before EIO, enters the shared failed-call fold with the original
selected catalog, the observed keeper, and the reached cleanup heap. -/
theorem MarkedWalExtentReports.extendsLongRenameError
    (before : RawOpenRetryTrace.SelectedEffects view source first target liveFiles state.selectedRetryPath selectedWal prior)
    (sameTarget : layout.target = target)
    {checkpoint : Option (PackedTable × UInt64)} {beforeKeeper afterKeeper reached : heap}
    (seals : MarkedSealReadChain seed source.fileCalls chronology.seals listing.reached beforeKeeper)
    (selected : SelectedIntegrityCheckpoint published.durable (view.files entry).image.directory.active.manifest checkpoint)
    (valid : Prepared (view.files entry).image layout.target layout.plan)
    (following : ∀ first ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < first)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      (view.files entry).image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (sameStat : source.fileCalls.stat = source.calls.lookup)
    (flat : optionalMetadataWith (source.fileCalls.stat ((dir).file .wal)) seed.afterPending = .ok none seed.afterPending)
    {markedMeta : IO.FS.Metadata}
    (marked : optionalMetadataWith (source.fileCalls.stat ((dir).file .walBoundary)) seed.afterPending =
      .ok (some markedMeta) seed.afterPending)
    (keeperRead : source.fileCalls.readKeeperWithRelease
      (fun path handle => (callbacks).modifyPending seed.pendingRef (pushPending path handle))
      ((dir).file (.walSegment layout.keeper.first)) layout.keeper.bytes.size
      reads.wal.keeper.calls.metadata.byteSize.toNat beforeKeeper = .ok layout.keeper.bytes afterKeeper)
    (readerFrames : source.fileCalls.ScopeFrames retryFrame)
    (listingFrames : source.directoryCalls.ScopeFrames dir retryFrame)
    (keeperFrame : retryFrame beforeKeeper afterKeeper)
    {authorized pruned recorded synced : heap} {cause : IO.Error} {effective : Bool} {old : Nat}
    (startFiles : (view.files afterKeeper).image = (view.files entry).image)
    (longer : layout.boundedPlan.keeperSize < reads.wal.keeper.calls.metadata.byteSize.toNat)
    (authorize : groupSync #[(dir).path] afterKeeper = .ok () authorized)
    (prune : ((layout.boundedPlan.newer.map Step.unlink ++ [Step.syncPruned]).forM
      (performPaths dir layout.boundedPlan source.remove throw stageWrite groupSync source.rename)) authorized = .ok () pruned)
    (written : stageWrite ((dir).file .stagedWal) layout.keeper.bytes pruned = .ok () recorded)
    (persisted : groupSync #[((dir).file .stagedWal)] recorded = .ok () synced)
    (later : ∀ ordinal ∈ layout.boundedPlan.newer, target.range.through < ordinal)
    (covers : ∀ ordinal ∈ (view.files afterKeeper).image.later.visible, ordinal ∈ layout.boundedPlan.newer)
    (authorizationImage : groupSync #[(dir).path] afterKeeper = .ok () authorized →
      (view.files authorized).image = (view.files afterKeeper).image.syncDirectory)
    (pruneImage : ∀ {unlinked}, ((layout.boundedPlan.newer.map Step.unlink).forM
      (performPaths dir layout.boundedPlan source.remove throw stageWrite groupSync source.rename)) authorized = .ok () unlinked →
      groupSync #[(dir).path] unlinked = .ok () pruned →
      (view.files pruned).image = (view.files unlinked).image.syncDirectory)
    (unlinkImage : ∀ {ordinal before after result}, ordinal ∈ layout.boundedPlan.newer →
      source.remove ((dir).file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () →
      (view.files after).image = (view.files before).image.unlinkLater ordinal)
    (writeStage : (view.files recorded).image = (view.files pruned).image.withScratch (some (target.trimmed, false)))
    (syncStage : (view.files synced).image = (view.files recorded).image.withScratch (some (target.trimmed, true)))
    (currentReady : state.Valid) (targetAtKeeper : target.first = state.writer.wal.active.first)
    (buffered : heap → IO.FS.Handle → ByteArray)
    (physical : source.stage.ReplacementPrefixStorageEffects callbacks
      (repairRootScope state (view.descriptors afterKeeper) admission.cached) view storage visible buffered
      seed.directoryRef seed.pendingRef seed.handle)
    (root : CachedKeeperReplacementRoot (repairRootScope state (view.descriptors afterKeeper) admission.cached)
      view seed.directoryRef seed.handle afterKeeper)
    (rootNamed : retryNames afterKeeper (dir).path = some ((view.descriptors afterKeeper).inode admission.cached.description))
    (oldNamed : retryNames afterKeeper ((dir).file (.walSegment target.first)) = some old)
    (unlinkStorage : ∀ {ordinal before after result}, ¬ state.crashPath ((dir).file (.walSegment ordinal)) →
      source.remove ((dir).file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () →
      (storage before).Frames state.crashPath (storage after) ∧
      (CachedKeeperReplacementRoot (repairRootScope state (view.descriptors afterKeeper) admission.cached)
        view seed.directoryRef seed.handle before →
        CachedKeeperReplacementRoot (repairRootScope state (view.descriptors afterKeeper) admission.cached)
          view seed.directoryRef seed.handle after))
    (records : ∀ {file before after},
      (callbacks).modifyPending seed.pendingRef (pushPending ((dir).file .stagedWal) file) before = .ok () after →
      view.pending after seed.pendingRef = pushPending ((dir).file .stagedWal) file (view.pending before seed.pendingRef))
    (readsPending : ∀ {before entries loaded}, (callbacks).getPending seed.pendingRef before = .ok entries loaded →
      entries = view.pending before seed.pendingRef)
    (readsRoot : ∀ {before result issued}, (callbacks).getDirectory seed.directoryRef before = .ok result issued →
      result = view.directory before seed.directoryRef)
    (readPendingFrames : source.fileCalls.ScopeFrames
      (fun before after => view.pending after seed.pendingRef = view.pending before seed.pendingRef))
    (listingPendingFrames : source.directoryCalls.ScopeFrames dir
      (fun before after => view.pending after seed.pendingRef = view.pending before seed.pendingRef))
    (liveEffects : source.stage.ReplacementPrefixLiveEffects callbacks
      (repairRootScope state (view.descriptors afterKeeper) admission.cached) view storage visible
      seed.directoryRef seed.pendingRef seed.handle source.remove)
    (keeper : RawOpenRetryTrace.KeeperAt view (dir) target retryNames visible afterKeeper)
    (failed : source.rename ((dir).file .stagedWal)
      ((dir).file (.walSegment target.first)) synced = .error cause reached)
    (observation : ∀ {replacement}, source.rename ((dir).file .stagedWal)
      ((dir).file (.walSegment target.first)) synced = .error cause reached →
      retryNames synced ((dir).file .stagedWal) = some replacement →
      retryNames synced ((dir).file (.walSegment target.first)) = some old →
      replacement ≠ old →
      WalKeeperRenameEffect state.session.directory target.first replacement effective
        (storage synced) (storage reached) (visible synced) (visible reached) ∧
      (if effective then (view.files synced).image.effect target (.replace .renameStaged)
        else some (view.files synced).image) = some (view.files reached).image)
    (dispose : RawOpenCacheDisposal (admitted := raw) seed reached)
    (sameDisposal : source.dispose = dispose.dispose)
    (owner : (view.files reached).owners = admission.held.owners)
    (finalized : RawOpenErrorLockFinalization view dir source.release raw.lock admission.owner dispose.reached)
    (scope : dispose.ScopeFrames finalized retryFrame)
    (keeperCleanup : (liveFiles reached).Frames (· = (dir).file (.walSegment target.first))
      (liveFiles finalized.reached))
    (readerNames : source.fileCalls.ScopeFrames walNameFrame)
    (listingNames : source.directoryCalls.ScopeFrames dir walNameFrame)
    (keeperNames : walNameFrame beforeKeeper afterKeeper)
    (namesOfCleanup : dispose.ScopeFrames finalized walNameFrame)
    (firstCovered : firstOffset ≤ target.range.through)
    (cutoffCovered : target.range.through ≤ through)
    (bounded : ∀ start ∈ state.writer.wal.segments.map WalSegment.first, start ≤ target.range.through)
    (listed : ∀ start, target.range.through < start →
      ((retryNames authorized ((dir).file (.walSegment start))).isSome = true ↔ start ∈ layout.boundedPlan.newer))
    (unlinkNames : ∀ {ordinal before after result}, ordinal ∈ layout.boundedPlan.newer →
      source.remove ((dir).file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () →
      retryNames after ((dir).file (.walSegment ordinal)) = none ∧
      ∀ start, start ≠ ordinal →
        retryNames after ((dir).file (.walSegment start)) = retryNames before ((dir).file (.walSegment start))) :
    ∃ returned : source.openTable input entry = .error (dispose.diagnostic cause) finalized.reached,
      RawOpenRetryTrace.SelectedEffects view source first target liveFiles state.selectedRetryPath selectedWal
        (prior.next input returned) := by
  have path : layout.boundedPlan.keeper = target.first := congrArg Target.first sameTarget
  have payload : layout.keeper.bytes = target.trimmed := congrArg Target.trimmed sameTarget
  have size : layout.boundedPlan.keeperBytes.size = layout.boundedPlan.keeperSize := layout.target.trimmedSize
  have checked : layout.boundedPlan.valid = true :=
    layout.boundedPlan_valid fun ordinal member =>
      show layout.target.range.through < ordinal from sameTarget.symm ▸ later ordinal member
  have actualWrite : stageWrite ((dir).file .stagedWal) target.trimmed pruned = .ok () recorded := payload ▸ written
  obtain ⟨prunedTrace, prunedEmpty, syncedImage, keeperActive⟩ :=
    longKeeperSyncPrefix (fun atHeap => (view.files atHeap).image) dir target layout.boundedPlan
      source.remove stageWrite groupSync source.rename authorize prune actualWrite persisted covers later
      authorizationImage pruneImage unlinkImage (fun _ => writeStage) (fun _ _ => syncStage)
  obtain ⟨unlinked, unlinks, suffixSync⟩ :=
    returnedWalUnlinksAndBarrier dir layout.boundedPlan source.remove stageWrite groupSync source.rename prune
  have away (ordinal : Nat) (member : ordinal ∈ layout.boundedPlan.newer) :
      ¬ state.crashPath ((dir).file (.walSegment ordinal)) := by
    have past : state.writer.wal.active.first < ordinal :=
      targetAtKeeper ▸ Nat.lt_of_le_of_lt target.firstCovered (later ordinal member)
    intro hit
    rcases NativeReadyState.crashPath_iff_write.mp hit with mark | keep | protectedPath
    · exact state.protectedPathNeWalFromActive currentReady (.inl mark) (Nat.le_of_lt past) rfl
    · exact (Nat.ne_of_gt past) ((dir).walSegment_path_injective keep)
    · exact state.protectedPathNeWalFromActive currentReady (.inr protectedPath) (Nat.le_of_lt past) rfl
  have writtenPrefix : stageWrite ((dir).file .stagedWal)
      (layout.boundedPlan.keeperBytes.extract 0 layout.boundedPlan.keeperSize) pruned = .ok () recorded := by
    rw [layout.boundedPlan_extractKeeper]
    exact written
  obtain ⟨durableFrame, rootFrame, _, authorizedScope, stageScope, oldAtRename, oldSettled,
    issued, file, slot, replacement, _, _, apart, stageAtIssue, bytesAtIssue, fileSync, liveAtSync, protects⟩ :=
    source.stage.prunedAndSyncedReplacement callbacks
      (repairRootScope state (view.descriptors afterKeeper) admission.cached) view storage visible buffered
      seed.directoryRef seed.activeRef seed.pendingRef source.remove source.rename seed.handle physical
      layout.boundedPlan (path.trans targetAtKeeper) root rootNamed
      (by simpa only [repairRootScope, path] using oldNamed) away unlinkStorage records readsPending readsRoot
      authorize unlinks suffixSync writtenPrefix persisted
  have renamedOld : retryNames synced ((dir).file (.walSegment target.first)) = some old := by
    simpa only [repairRootScope, path] using oldAtRename
  have oldChoices : ∀ names ∈ (storage synced).crashNames, names ((dir).file (.walSegment target.first)) = some old := by
    simpa only [repairRootScope, path] using oldSettled
  have stagedNamed := (congrFun fileSync.names ((dir).file .stagedWal)).trans stageAtIssue
  have atIssueBytes : visible issued replacement = target.trimmed := by
    rw [bytesAtIssue, layout.boundedPlan_extractKeeper]
    exact payload
  have stagedLive := liveAtSync.trans atIssueBytes
  have stagedDurable : (storage synced).files.bytes replacement = [target.trimmed] := by
    simpa [atIssueBytes] using fileSync.bytes replacement
  have observedLong : layout.keeper.bytes.size < reads.wal.keeper.calls.metadata.byteSize.toNat := by
    change layout.boundedPlan.keeperBytes.size < reads.wal.keeper.calls.metadata.byteSize.toNat
    rw [size]
    exact longer
  have emptyPending := listing.emptyPendingAfterLongKeeper selected seals readPendingFrames listingPendingFrames
    (fun path handle => (callbacks).modifyPending seed.pendingRef (pushPending path handle)) observedLong keeperRead
  have live := protects liveEffects emptyPending
  have keeperPath : state.crashPath ((dir).file (.walSegment target.first)) :=
    NativeReadyState.crashPath_iff_write.mpr (.inr (.inl
      (congrArg (fun start => (dir).file (.walSegment start)) targetAtKeeper)))
  have sameOld : visible synced old = visible afterKeeper old :=
    (List.cons.inj ((live _ keeperPath).2 old oldNamed)).1
  have atRename : RawOpenRetryTrace.KeeperAt view dir target retryNames visible synced := by
    unfold RawOpenRetryTrace.KeeperAt at keeper ⊢
    rw [keeperActive, keeper, renamedOld, oldNamed]
    exact congrArg some sameOld.symm
  have toRename : retryFrame afterKeeper synced := by
    have inScope (path : FilePath) (selected : state.selectedRetryPath path) : state.crashPath path :=
      NativeReadyState.crashPath_iff_write.mpr (selected.imp id Or.inr)
    exact ⟨fun path selected => live path (inScope path selected),
      fun path selected => durableFrame path (inScope path selected), rootFrame⟩
  have safe (path : FilePath) (selectedPath : state.selectedRetryPath path) :
      path ≠ (dir).file (.walSegment target.first) ∧ path ≠ (dir).file .stagedWal := by
    refine ⟨?_, state.stagedWalOutsideRetryFootprint path selectedPath⟩
    rw [targetAtKeeper]
    exact state.protectedPathNeWalFromActive currentReady selectedPath (Nat.le_refl _)
  obtain ⟨repair, trace, framed, liveKeeper, _, renameNames, _, _, laterGone⟩ :=
    failedLongKeeperRename view state target layout.boundedPlan reads.wal.keeper.calls.metadata.byteSize.toNat
      storage visible source.remove stageWrite groupSync source.rename checked size longer path payload authorize
      prune actualWrite persisted prunedTrace prunedEmpty syncedImage toRename safe renamedOld oldChoices stagedNamed
      apart stagedLive stagedDurable atRename failed observation
  rw [startFiles] at trace
  have errorNames : walNameFrame synced reached := fun start => (renameNames start start).live start (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨returned, effects, _⟩ := extents.extendsFailedRepair before sameTarget seals selected valid following accepted ordered sameStat flat marked
    keeperRead readerFrames listingFrames keeperFrame repair (sameTarget.symm ▸ trace) framed liveKeeper dispose
    sameDisposal owner finalized scope keeperCleanup (fun initial => initial.2.2.1) (by
      intro image finalKeeper finalDurability initial
      have gone : (view.files finalized.reached).image.later.visible = [] := image.symm ▸ laterGone.1
      obtain ⟨nextWindow, nextSuffix⟩ := listing.carriesPrunedCatalog
        seals selected prune dispose finalized readerNames listingNames keeperNames
        (fun start => congrArg Option.isSome (authorizedScope start))
        (by
          intro other loop _ start
          have same : other = unlinked := by
            rw [unlinks] at loop
            cases loop
            rfl
          subst other
          exact congrArg Option.isSome (stageScope start))
        errorNames namesOfCleanup firstCovered cutoffCovered bounded
        later listed unlinkNames initial.1 gone
      exact ⟨nextWindow, finalKeeper, finalDurability, nextSuffix⟩)
  exact ⟨returned, effects⟩

end SelectedRetry

end Alvoki.Storage.DiskSession
