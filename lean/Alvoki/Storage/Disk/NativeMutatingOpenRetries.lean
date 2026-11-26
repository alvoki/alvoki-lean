import Alvoki.Storage.Disk.Checkpoint.BarrierRetryObservations
import Alvoki.Storage.Disk.NativeRawUncertainWrite
import Alvoki.Storage.Disk.NativeHealthyMarkedTableOpen
import Alvoki.Storage.Disk.NativeFinalizedOpenRetries
import Alvoki.Storage.Disk.WalSegmentRepairEffects

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

variable {heap : Type} {view : OpenCloseHeapView heap FileImage} {directory : DiskDirectory}
  {calls : RawOpenAdmissionCallbacks heap} {init : OpenSyncCacheCallbacks heap}
  {release : IO.FS.Handle → heap → heap} {start : heap}

/-- Put an actual bounded repair error through the same marked reader
and the same cache and lock finalizers used by the raw opener. The
success continuation is not reached when repair returns that error. -/
theorem MarkedWalExtentReports.finalizesFailedRepair
    {source : heap} {input : FilePath} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout (view.files source).image history} {published : CheckpointPublication.Image}
    {admission : CensusOpenAdmissionReports input directory (view.descriptors source) (view.files source)}
    {raw : RawOpenAdmissionReport admission view calls source}
    {seed : OpenSyncCacheAllocations admission.opened view init raw.afterFlock}
    {reads : CapturedMarkedReadReports admission layout published} {keeper : CapturedKeeperOpenReports reads}
    {chronology : CapturedMarkedReadCensus reads keeper} {checkpoint : Option (PackedTable × UInt64)}
    {stream : Type} {fileCalls : MarkedTemporaryReadCalls heap} {directoryCalls : MarkedDirectoryReadCalls heap stream}
    {prepared : NativeMarkedCheckpointReadHeap seed chronology fileCalls}
    {slotOf : heap → stream → DescriptorSlot} {listing : MarkedDirectoryReadReport prepared directoryCalls slotOf}
    (extents : MarkedWalExtentReports prepared listing)
    {beforeKeeper afterKeeper failedHeap : heap}
    (seals : MarkedSealReadChain seed fileCalls chronology.seals listing.reached beforeKeeper)
    (selected : SelectedIntegrityCheckpoint published.durable (view.files source).image.directory.active.manifest checkpoint)
    (valid : Prepared (view.files source).image layout.target layout.plan)
    (following : ∀ first ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < first)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (WAL.Boundary.CheckpointRepresentsPrefix history)
      (view.files source).image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (sameStat : fileCalls.stat = calls.lookup)
    (flat : optionalMetadataWith (fileCalls.stat (directory.file .wal)) seed.afterPending = .ok none seed.afterPending)
    {markedMeta : IO.FS.Metadata}
    (marked : optionalMetadataWith (fileCalls.stat (directory.file .walBoundary)) seed.afterPending =
      .ok (some markedMeta) seed.afterPending)
    (callbacks : AlignedKeeperCacheCallbacks heap)
    (keeperRead : fileCalls.readKeeperWithRelease
      (fun path handle => (callbacks.withFileReads fileCalls).modifyPending seed.pendingRef (pushPending path handle))
      (directory.file (.walSegment layout.keeper.first)) layout.keeper.bytes.size
      reads.wal.keeper.calls.metadata.byteSize.toNat beforeKeeper = .ok layout.keeper.bytes afterKeeper)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)) (stage : LongKeeperStageCallbacks heap)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) {cause : IO.Error}
    (repair : let sync := callbacks.withFileReads fileCalls
      finishBoundedMarkedOpen directory layout.boundedPlan reads.wal.keeper.calls.metadata.byteSize.toNat
        remove (stage.stage seed.pendingRef sync.modifyPending)
        (sync.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef) rename afterKeeper =
      .error cause failedHeap)
    (dispose : RawOpenCacheDisposal (admitted := raw) seed failedHeap)
    (owner : (view.files failedHeap).owners = admission.held.owners)
    (inodes : (view.descriptors failedHeap).inode = (view.descriptors source).inode)
    (finalized : RawOpenErrorLockFinalization view directory release raw.lock admission.owner dispose.reached)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap DiskTable) :
    let recover := fun resolved lock cache => do
      let opened ← recoverHealthyMarkedWithRefs fileCalls directoryCalls callbacks seed.directoryRef seed.activeRef
        seed.pendingRef remove stage rename calls.lookup resolved (bootstrap resolved cache)
      install resolved lock cache opened
    ∃ failed : RawFinalizedOpenAttempt view directory calls init release input source (view.files failedHeap).image,
      failed.recover = recover ∧ failed.beforeCleanup = failedHeap ∧ failed.cause = cause ∧
      failed.reached = finalized.reached := by
  intro recover
  have failed : ∀ cache, recover directory raw.lock cache seed.afterPending = .error cause failedHeap := by
    intro cache
    obtain ⟨_, returned, _⟩ := extents.recoversFromOpenedCacheWith seals selected valid following accepted ordered
      flat marked _ keeperRead remove _ _ rename repair (bootstrap directory cache)
    have physical : recoverHealthyMarkedWithRefs fileCalls directoryCalls callbacks seed.directoryRef seed.activeRef
        seed.pendingRef remove stage rename calls.lookup directory (bootstrap directory cache) seed.afterPending =
      .error cause failedHeap := by
      unfold recoverHealthyMarkedWithRefs
      rw [← sameStat]
      exact returned
    simp only [recover, Bind.bind, EStateM.bind, physical]
  exact ⟨.fromWorkerError raw seed dispose recover cause failed owner inodes finalized, rfl, rfl, rfl, rfl⟩

/-- The caller-visible chronology uses the exact heap after every
failure. A held worker can leave a different image before its cache
and lock finalizers run. Admission here records no repair invariant. -/
inductive RawOpenRetryTrace (view : OpenCloseHeapView heap FileImage) (directory : DiskDirectory)
    (calls : RawOpenAdmissionCallbacks heap) (init : OpenSyncCacheCallbacks heap)
    (release : IO.FS.Handle → heap → heap) (start : heap) : List (FilePath × IO.Error) → heap → Prop where
  | empty : RawOpenRetryTrace view directory calls init release start [] start
  | readOnly {earlier more : List (FilePath × IO.Error)} {entry reached : heap}
      (prior : RawOpenRetryTrace view directory calls init release start earlier entry)
      (attempts : RawFinalizedOpenAttempts view directory calls init release entry more reached) :
      RawOpenRetryTrace view directory calls init release start (earlier ++ more) reached
  | repair {earlier : List (FilePath × IO.Error)} {entry : heap} {workerImage : FileImage}
      (prior : RawOpenRetryTrace view directory calls init release start earlier entry) (input : FilePath)
      (failed : RawFinalizedOpenAttempt view directory calls init release input entry workerImage) :
      RawOpenRetryTrace view directory calls init release start (earlier ++ [(input, failed.diagnostic)]) failed.reached

/-- Local file effects for the already recorded attempts. Repair may
replace the keeper or prune later names. The caller supplies a separate
frame for paths outside those effects, such as the selected runs. -/
inductive RawOpenRetryTrace.SelectedEffects (view : OpenCloseHeapView heap FileImage) (directory : DiskDirectory)
    (calls : RawOpenAdmissionCallbacks heap) (init : OpenSyncCacheCallbacks heap)
    (release : IO.FS.Handle → heap → heap) (start : heap) (target : Target)
    (files : heap → CheckpointSurvivingFiles) (protectedPaths : FilePath → Prop) :
    ∀ {returns : List (FilePath × IO.Error)} {reached : heap},
      RawOpenRetryTrace view directory calls init release start returns reached → Prop where
  | empty : SelectedEffects view directory calls init release start target files protectedPaths .empty
  | readOnly {earlier more : List (FilePath × IO.Error)} {entry reached : heap}
      {prior : RawOpenRetryTrace view directory calls init release start earlier entry}
      {attempts : RawFinalizedOpenAttempts view directory calls init release entry more reached}
      (before : SelectedEffects view directory calls init release start target files protectedPaths prior)
      (frame : (files entry).Frames protectedPaths (files reached)) :
      SelectedEffects view directory calls init release start target files protectedPaths (.readOnly prior attempts)
  | repair {earlier : List (FilePath × IO.Error)} {entry : heap} {workerImage : FileImage}
      {prior : RawOpenRetryTrace view directory calls init release start earlier entry}
      {input : FilePath} {failed : RawFinalizedOpenAttempt view directory calls init release input entry workerImage}
      (before : SelectedEffects view directory calls init release start target files protectedPaths prior)
      (repair : EffectTrace target (view.files entry).image workerImage)
      (frame : (files entry).Frames protectedPaths (files failed.reached)) :
      SelectedEffects view directory calls init release start target files protectedPaths (.repair prior input failed)

/-- Read-only failures keep the current image. The repair effects start
at that same image and are preserved through finalization. Both cases
compose the independent frame on the unchanged physical files. -/
theorem RawOpenRetryTrace.SelectedEffects.preserves {target : Target} {files : heap → CheckpointSurvivingFiles}
    {protectedPaths : FilePath → Prop} {returns : List (FilePath × IO.Error)} {reached : heap}
    {attempts : RawOpenRetryTrace view directory calls init release start returns reached}
    (effects : RawOpenRetryTrace.SelectedEffects view directory calls init release start target files protectedPaths attempts)
    (valid : (view.files start).image.Valid target) :
    (view.files reached).image.Valid target ∧
      (view.files reached).image.kept = (view.files start).image.kept ∧
      (files start).Frames protectedPaths (files reached) ∧
      (view.descriptors reached).inode = (view.descriptors start).inode := by
  induction effects with
  | empty => exact ⟨valid, rfl, fun _ _ => ⟨rfl, fun _ _ => rfl⟩, rfl⟩
  | @readOnly _ _ entry reached prior block _ frame ih =>
    obtain ⟨sameInodes, sameImage⟩ := block.preserves
    exact ⟨sameImage.symm ▸ ih.1, (congrArg FileImage.kept sameImage).trans ih.2.1,
      ih.2.2.1.trans frame, sameInodes.trans ih.2.2.2⟩
  | @repair _ entry workerImage prior input failed _ repair frame ih =>
    obtain ⟨_, _, _, _, _, sameInodes, returnedImage, _⟩ := failed.returns
    have next := repair.valid ih.1.selected ih.1.keeper ih.1.later
    exact ⟨returnedImage.symm ▸ next, (congrArg FileImage.kept returnedImage).trans (repair.keepsSealed.trans ih.2.1),
      ih.2.2.1.trans frame, sameInodes.trans ih.2.2.2⟩

/-- After a sequence of read-only and mutating failed opens, the new
reader uses the keeper and later names at the last returned heap. The
selected history, retained runs and earlier client reads are unchanged. -/
theorem NativeReadPosition.preparesWriteRetry {prior : List WAL.Write} {log : List DatabaseSubmissions}
    (current : NativeReadPosition prior log) {rows : List (UInt64 × Option UInt64)} {batch : List WAL.Write}
    {table : PackedTable} (prepared : prepareBatch current.state.writer.installed.table rows = some (batch, table))
    (fits : current.state.writer.installed.walBytes + WAL.frameSize * rows.length < UInt64.size)
    {target : Target} (admitted : BatchRetryTarget current.state.writer.history batch current.state.writer.wal.active.first target)
    (manifest : target.pair.manifest = current.state.writer.target.pair.manifest)
    {returns : List (FilePath × IO.Error)} {reached : heap} {files : heap → CheckpointSurvivingFiles}
    {protectedPaths : FilePath → Prop}
    {attempts : RawOpenRetryTrace view current.state.session.directory calls init release start returns reached}
    (effects : RawOpenRetryTrace.SelectedEffects view current.state.session.directory calls init release start
      target files protectedPaths attempts) (initial : (view.files start).image.Valid target) :
    current.SelectedWriteLayout batch target (view.files reached).image ∧
      (view.files reached).image.kept = (view.files start).image.kept ∧
      (files start).Frames protectedPaths (files reached) := by
  obtain ⟨observed, sealed, frame, _⟩ := effects.preserves initial
  exact ⟨current.preparesSelectedWrite prepared fits admitted observed manifest, sealed, frame⟩

end Alvoki.Storage.DiskSession
