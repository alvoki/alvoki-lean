import Alvoki.Storage.Disk.NativeCheckpointOpenChronology
import Alvoki.Storage.Disk.NativeLongKeeperFinalSyncError
import Alvoki.Storage.Disk.NativeDurableWriteReboot
import Alvoki.Storage.Disk.NativeMarkedScanFrame
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

/-- A directory fsync frames the protected child bytes for either
reported effect. Parent binding continuity is a separate effect law. -/
private theorem WalRootSyncEffect.framesSelectedRetry {state : NativeReadyState} {effective : Bool}
    {entry reached : CheckpointStorageObservation} {before after : Nat → ByteArray}
    (effect : WalRootSyncEffect state.session.directory effective entry reached)
    (parent : entry.Frames (· = state.session.directory.path) reached) (live : after = before) :
    state.SelectedRetryFrame entry reached before after := by
  have durable : entry.files.Frames state.selectedRetryPath reached.files := by
    intro path retained
    rcases NativeReadyState.selectedRetryPath_rootOrChild retained with atRoot | ⟨file, rfl⟩
    · exact parent.visible path atRoot
    · exact ⟨effect.visible file, fun inode bound =>
        effect.bytes reached.files.names (.inl rfl) file inode ((effect.visible file).trans bound)⟩
  exact ⟨fun path held => ⟨(durable path held).1, by rw [live]; intros; rfl⟩, durable, parent⟩


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
  refine ⟨returned, trace, prefixFrame.trans (childScope.framesSelectedRetry parentScope unchanged), ?_, named, durable, ?_⟩
  · unfold RawOpenRetryTrace.KeeperAt
    change (view.files reached).image.keeper.active =
      (names reached (directory.file (.walSegment layout.keeper.first))).map (visible reached)
    rw [activeKeeper, named, Option.map_some, unchanged, keeperBytes]
  · intro applied names survives
    exact (children.settled applied names survives (.walSegment layout.keeper.first)).trans named

end DirectorySync

section Finalization

variable {heap : Type} {view : OpenCloseHeapView heap FileImage} {directory : DiskDirectory}
  {calls : RawOpenAdmissionCallbacks heap} {init : OpenSyncCacheCallbacks heap}
  {release : IO.FS.Handle → heap → heap} {input : FilePath} {entry : heap} {workerImage : FileImage}

/-- Cache disposal and lock cleanup retain the worker's live keeper.
This applies to an unchanged keeper and to one already replaced. -/
theorem RawFinalizedOpenAttempt.keepsObservedKeeper
    (failed : RawFinalizedOpenAttempt view directory calls init release input entry workerImage)
    {target : Target} {names : heap → FilePath → Option Nat} {visible : heap → Nat → ByteArray}
    (frame : (⟨names failed.beforeCleanup, fun inode => [visible failed.beforeCleanup inode]⟩ : CheckpointSurvivingFiles).Frames
      (· = directory.file (.walSegment target.first))
      ⟨names failed.reached, fun inode => [visible failed.reached inode]⟩)
    (worker : workerImage.keeper.active =
      (names failed.beforeCleanup (directory.file (.walSegment target.first))).map (visible failed.beforeCleanup)) :
    RawOpenRetryTrace.KeeperAt view directory target names visible failed.reached := by
  obtain ⟨_, _, _, _, _, _, returnedImage, _⟩ := failed.returns
  unfold RawOpenRetryTrace.KeeperAt
  rw [returnedImage, worker]
  exact (frame.visiblePayload rfl).symm

end Finalization

section SelectedRetry

variable {heap stream : Type} {view : OpenCloseHeapView heap FileImage} {state : NativeReadyState}
  {source : RawMarkedOpenInterpreter heap stream} {first entry : heap} {input : FilePath}
  {target : Target} {storage : heap → CheckpointStorageObservation} {visible : heap → Nat → ByteArray}
  {earlier : List (FilePath × IO.Error)} {prior : source.FailedCalls first earlier entry}

local notation "dir" => state.session.directory
local notation "retryNames" => fun atHeap => CheckpointSurvivingFiles.names (CheckpointStorageObservation.files (storage atHeap))
local notation "liveFiles" => fun atHeap => CheckpointSurvivingFiles.mk (retryNames atHeap) fun inode => [visible atHeap inode]
local notation "keep" => fun atHeap => RawOpenRetryTrace.KeeperAt view dir target retryNames visible atHeap ∧
  state.SelectedRetryDurability target (storage atHeap)
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
    (inodes : (view.descriptors reached).inode = (view.descriptors entry).inode)
    (finalized : RawOpenErrorLockFinalization view dir source.release raw.lock admission.owner dispose.reached)
    (scope : dispose.ScopeFrames finalized retryFrame)
    (keeperCleanup : (liveFiles reached).Frames (· = (dir).file (.walSegment target.first))
      (liveFiles finalized.reached)) :
    ∃ returned : source.openTable input entry = .error (dispose.diagnostic cause) finalized.reached,
      RawOpenRetryTrace.SelectedEffects view source first target liveFiles state.selectedRetryPath keep
        (prior.next input returned) := by
  let worker := source.worker seed.directoryRef seed.activeRef seed.pendingRef
  have rejected := extents.workerReturnsFailedRepair source (raw := raw) seals selected valid following accepted ordered sameStat
    flat marked keeperRead repair
  let failed := RawFinalizedOpenAttempt.fromWorkerError raw seed dispose worker cause rejected owner inodes finalized
  have refl atHeap := NativeReadyState.SelectedRetryFrame.refl state (storage atHeap) (visible atHeap)
  have trans {first middle last : heap} (a : retryFrame first middle) (b : retryFrame middle last) :
      retryFrame first last := a.trans b
  obtain ⟨toListing, toKeeper⟩ := listing.framesThroughSeals selected seals retryFrame refl trans readerFrames listingFrames
  have inWorker := trans (trans toListing toKeeper) (trans keeperFrame repairFrame)
  have returned := failed.returnsFixedInterpreter source rfl sameDisposal (rejected _)
  have kept := scope.preserves trans inWorker
  have keeperAt := failed.keepsObservedKeeper (target := target) (names := retryNames) (visible := visible)
    keeperCleanup keeperAtError
  exact ⟨returned, before.repair failed (sameTarget ▸ effects) kept.live
    (fun selected => ⟨keeperAt, selected.2.frame kept.durable kept.parent⟩) returned⟩

local notation "callbacks" => source.keeperCallbacks.withFileReads source.fileCalls
local notation "stageWrite" => LongKeeperStageCallbacks.stage source.stage seed.pendingRef (AlignedKeeperCacheCallbacks.modifyPending callbacks)
local notation "groupSync" => AlignedKeeperCacheCallbacks.syncPaths callbacks (DiskDirectory.path dir) seed.directoryRef seed.activeRef seed.pendingRef

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
    (inodes : (view.descriptors reached).inode = (view.descriptors entry).inode)
    (finalized : RawOpenErrorLockFinalization view dir source.release raw.lock admission.owner dispose.reached)
    (scope : dispose.ScopeFrames finalized retryFrame)
    (keeperCleanup : (liveFiles reached).Frames (· = (dir).file (.walSegment target.first))
      (liveFiles finalized.reached))
    (keeperStorage : (storage reached).files.Frames (· = (dir).file (.walSegment layout.keeper.first))
      (storage finalized.reached).files) :
    ∃ returned : source.openTable input entry =
        .error (dispose.diagnostic (IO.userError s!"sync failed for '{(dir).path}': {cause}")) finalized.reached,
      RawOpenRetryTrace.SelectedEffects view source first target liveFiles state.selectedRetryPath keep
        (prior.next input returned) ∧
      retryNames finalized.reached ((dir).file (.walSegment layout.keeper.first)) =
        some (staged.inventory.inode staged.slot.description) ∧
      (storage finalized.reached).files.bytes (staged.inventory.inode staged.slot.description) = [layout.target.trimmed] := by
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
  obtain ⟨repair, trace, carried, kept, named, durable, _⟩ :=
    issue.returnsSelectedRepairError view state rfl storage visible callbacks seed.directoryRef seed.activeRef seed.pendingRef
      source.remove source.stage source.rename startFiles measured authorize prune written persisted moved loaded atIssue
      census issuedFiles root keeper scratch keeperBytes keeperDurable reachedIssue failed effect
  rw [startFiles] at trace
  obtain ⟨returned, selectedEffects⟩ := extents.extendsFailedRepair before sameTarget seals selected valid following accepted ordered sameStat flat marked
    keeperRead readerFrames listingFrames keeperFrame repair trace carried (sameTarget ▸ kept) dispose sameDisposal owner
    inodes finalized scope keeperCleanup
  obtain ⟨sameName, sameBytes⟩ := keeperStorage _ rfl
  exact ⟨returned, selectedEffects, sameName.trans named, (sameBytes _ named).trans durable⟩

end SelectedRetry

end Alvoki.Storage.DiskSession
