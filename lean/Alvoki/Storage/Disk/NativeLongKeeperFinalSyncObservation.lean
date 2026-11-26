import Alvoki.Storage.Disk.NativeCheckpointOpenChronology
import Alvoki.Storage.Disk.NativeLongKeeperFinalSyncError
import Alvoki.Storage.Disk.NativeDurableWriteReboot
import Alvoki.Storage.Disk.AppendGroupedReports
import Alvoki.Storage.Disk.NativeMarkedScanFrame
import Alvoki.Storage.Disk.WalSegmentRepairCheckpointBytes

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting
open WAL.Boundary (WalInodeImage)

section DirectorySync

variable {heap : Type} {directory : DiskDirectory} {initial : LockedFileState FileImage}
  {history : List WAL.Write} {layout : CanonicalKeeperLayout initial.image history}
  {operations : MarkedRetryChunkOperations
    (Cache (DescriptorInventory × DescriptorSlot × Nat)) directory layout}
  {published : CheckpointPublication.Image} {held : HeldDirectoryMarkedRetryReports operations published}
  {authorized : ListedDirectoryAuthorization held} {pruning : LongKeeperPruning authorized}
  {stage : ListedLongKeeperStageAt pruning} {renamed : ListedLongKeeperRename stage}

/-- Project the same returned final fsync onto the logical repair image
and its actual observed keeper inodes. Both error effects keep the
trimmed replacement visible. Only an effective call settles its name. -/
theorem ListedLongKeeperDirectoryIssue.observesFinalSyncError
    (issue : ListedLongKeeperDirectoryIssue renamed) (view : OpenCloseHeapView heap FileImage)
    (inodes : heap → WalInodeImage) (callbacks : AlignedKeeperCacheCallbacks heap)
    {handle : IO.FS.Handle} {issued reached : heap} {cause : IO.Error} {effective : Bool}
    (fileImage : view.files issued = issue.files)
    (keeperInodes : inodes issued = issue.stoppedInodes false)
    (failed : callbacks.sync handle issued = .error cause reached)
    (observed : FsyncResult (view.files issued, inodes issued)
      (issue.stopped true, (inodes issued).settleBinding) effective
      (projectResult (fun heap => (view.files heap, inodes heap)) (callbacks.sync handle issued))) :
    let replacement := stage.inventory.inode stage.slot.description
    view.files reached = issue.stopped effective ∧
    inodes reached = issue.stoppedInodes effective ∧
    (inodes reached).active = replacement ∧
    (inodes reached).visible replacement = layout.target.trimmed ∧
    (inodes reached).crashBytes replacement = [layout.target.trimmed] ∧
    (inodes reached).crashBindings =
      if effective then [replacement] else replacement :: renamed.original.crashBindings := by
  intro replacement
  rw [failed, projectResult, fileImage, keeperInodes] at observed
  have selects {projected : LockedFileState FileImage × WalInodeImage} {applied : Bool}
      (reported : FsyncResult (issue.files, issue.stoppedInodes false)
        (issue.stopped true, (issue.stoppedInodes false).settleBinding) applied (.error cause projected)) :
      projected = (issue.stopped applied, issue.stoppedInodes applied) := by
    cases reported <;> rfl
  have outcome := selects observed
  have seen : inodes reached = issue.stoppedInodes effective := congrArg Prod.snd outcome
  refine ⟨congrArg Prod.fst outcome, seen, (congrArg WalInodeImage.active seen).trans (issue.stoppedBindings effective).1,
    ?_, ?_, ?_⟩
  · rw [seen]
    cases effective <;> simp [replacement, ListedLongKeeperDirectoryIssue.stoppedInodes,
      WalInodeImage.renameSynced, WalInodeImage.settleBinding, CanonicalKeeperLayout.target]
  · rw [seen]
    cases effective <;> simp [replacement, ListedLongKeeperDirectoryIssue.stoppedInodes,
      WalInodeImage.renameSynced, WalInodeImage.settleBinding, CanonicalKeeperLayout.target]
  · rw [seen]
    exact (issue.stoppedBindings effective).2

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

/-- Follow the selected reads and bounded repair on the cache allocated
by this open. The cleanup exposes the worker's changed keeper to the
next attempt and transports the earlier durable selections separately. -/
theorem MarkedWalExtentReports.extendsFailedRepair
    {history : List WAL.Write} {layout : CanonicalKeeperLayout (view.files entry).image history}
    {published : CheckpointPublication.Image}
    {admission : CensusOpenAdmissionReports input dir (view.descriptors entry) (view.files entry)}
    {raw : RawOpenAdmissionReport admission view source.calls entry}
    {seed : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock}
    {reads : CapturedMarkedReadReports admission layout published} {keeper : CapturedKeeperOpenReports reads}
    {chronology : CapturedMarkedReadCensus reads keeper}
    {prepared : NativeMarkedCheckpointReadHeap seed chronology source.fileCalls}
    {slotOf : heap → stream → DescriptorSlot} {listing : MarkedDirectoryReadReport prepared source.directoryCalls slotOf}
    (extents : MarkedWalExtentReports prepared listing)
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
    (repairFrames : let sync := source.keeperCallbacks.withFileReads source.fileCalls
      FinisherFrames dir layout.boundedPlan retryFrame source.remove (source.stage.stage seed.pendingRef sync.modifyPending)
        (sync.syncPaths (dir).path seed.directoryRef seed.activeRef seed.pendingRef) source.rename)
    {object : Nat}
    (keeperBound : retryNames reached ((dir).file (.walSegment layout.keeper.first)) = some object)
    (keeperBytes : visible reached object = layout.target.trimmed)
    (keeperActive : (view.files reached).image.keeper.active = some layout.target.trimmed)
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
  have rejected := extents.workerReturnsFailedRepair source seals selected valid following accepted ordered sameStat
    flat marked keeperRead repair
  let failed := RawFinalizedOpenAttempt.fromWorkerError raw seed dispose worker cause rejected owner inodes finalized
  have refl atHeap := NativeReadyState.SelectedRetryFrame.refl state (storage atHeap) (visible atHeap)
  have trans {first middle last : heap} (a : retryFrame first middle) (b : retryFrame middle last) :
      retryFrame first last := a.trans b
  obtain ⟨toListing, toKeeper⟩ := listing.framesThroughSeals selected seals retryFrame refl trans readerFrames listingFrames
  have repairFrame : retryFrame afterKeeper reached := by
    have carried := finishBoundedMarkedOpen_frames (frame := retryFrame)
      (keeperFileSize := reads.wal.keeper.calls.metadata.byteSize.toNat)
      refl trans repairFrames afterKeeper
    rw [repair] at carried
    exact carried
  have keeperAtError : RawOpenRetryTrace.KeeperAt view dir target retryNames visible reached := by
    unfold RawOpenRetryTrace.KeeperAt
    rw [← sameTarget]
    change (view.files reached).image.keeper.active =
      (retryNames reached ((dir).file (.walSegment layout.keeper.first))).map (visible reached)
    rw [keeperBound, Option.map_some, keeperBytes, keeperActive]
  have inWorker := trans (trans toListing toKeeper) (trans keeperFrame repairFrame)
  have returned := failed.returnsFixedInterpreter source rfl sameDisposal (rejected _)
  have kept := scope.preserves trans inWorker
  have keeperAt := failed.keepsObservedKeeper (target := target) (names := retryNames) (visible := visible)
    keeperCleanup keeperAtError
  exact ⟨returned, before.repair failed (sameTarget ▸ effects) kept.live
    (fun selected => ⟨keeperAt, selected.2.frame kept.durable kept.parent⟩) returned⟩

end SelectedRetry

end Alvoki.Storage.DiskSession
