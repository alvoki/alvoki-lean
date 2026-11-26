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

/-- A scoped frame over singleton live observations carries a named
payload without constraining absent paths or unrelated inode contents. -/
theorem CheckpointSurvivingFiles.Frames.visiblePayload {before after : heap} {scope : FilePath → Prop}
    {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
    (frame : (⟨names before, fun inode => [bytes before inode]⟩ : CheckpointSurvivingFiles).Frames scope
      ⟨names after, fun inode => [bytes after inode]⟩) {path : FilePath} (selected : scope path) :
    (names after path).map (bytes after) = (names before path).map (bytes before) := by
  obtain ⟨named, contents⟩ := frame path selected
  change names after path = names before path at named
  rw [named]
  cases found : names before path with
  | none => rfl
  | some inode =>
    have same : [bytes after inode] = [bytes before inode] := contents inode found
    exact congrArg some (List.cons.inj same).1

/-- The live keeper is the file currently bound at the selected path.
Its previous binding can still be a crash alternative. -/
def RawOpenRetryTrace.KeeperAt (view : OpenCloseHeapView heap FileImage) (directory : DiskDirectory)
    (target : Target) (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray) (atHeap : heap) : Prop :=
  (view.files atHeap).image.keeper.active = (names atHeap (directory.file (.walSegment target.first))).map (bytes atHeap)

/-- The marker joins the immutable write footprint once a retry has
selected a target. Repair gives the live keeper its own relation. -/
def NativeReadyState.selectedRetryPath (state : NativeReadyState) (path : FilePath) : Prop :=
  path = state.session.directory.file .walBoundary ∨ state.writeFramePath path

/-- Facts established when entering a selected retry epoch. The actual
open attempts and their local effects are indexed separately. -/
structure RawOpenRetryTrace.SelectedEntry (view : OpenCloseHeapView heap FileImage)
    (state : NativeReadyState) (target : Target) (names : heap → FilePath → Option Nat)
    (visible : heap → Nat → ByteArray) (first : heap) : Prop where
  valid : (view.files first).image.Valid target
  kept : (view.files first).image.kept = state.writer.files.kept
  manifest : target.pair.manifest = state.writer.target.pair.manifest
  protectedFiles : NativeReadyProtectedStorage state ⟨names first, fun inode => [visible first inode]⟩
  keeper : KeeperAt view state.session.directory target names visible first
  marker : (names first (state.session.directory.file .walBoundary)).map (visible first) = target.pair.walBoundary

/-- A read-only block carries the named keeper using the scoped live
file frame, leaving repairs to establish their own local effect. -/
theorem RawFinalizedOpenAttempts.keepsVisibleKeeper {target : Target}
    {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
    {returns : List (FilePath × IO.Error)} {reached : heap}
    (block : RawFinalizedOpenAttempts view directory calls init release start returns reached)
    (frame : (⟨names start, fun inode => [bytes start inode]⟩ : CheckpointSurvivingFiles).Frames
      (· = directory.file (.walSegment target.first)) ⟨names reached, fun inode => [bytes reached inode]⟩)
    (keeper : RawOpenRetryTrace.KeeperAt view directory target names bytes start) :
    RawOpenRetryTrace.KeeperAt view directory target names bytes reached := by
  unfold RawOpenRetryTrace.KeeperAt at keeper ⊢
  rw [block.preserves.2, keeper]
  exact (frame.visiblePayload rfl).symm

/-- Local file effects for the already recorded attempts. Repair may
replace the keeper or prune later names. The caller supplies a separate
frame for paths outside those effects, such as the selected runs.
An independent observation, such as the live keeper, can be carried by
local laws for just the attempts in this trace. -/
inductive RawOpenRetryTrace.SelectedEffects (view : OpenCloseHeapView heap FileImage) (directory : DiskDirectory)
    (calls : RawOpenAdmissionCallbacks heap) (init : OpenSyncCacheCallbacks heap)
    (release : IO.FS.Handle → heap → heap) (start : heap) (target : Target)
    (files : heap → CheckpointSurvivingFiles) (protectedPaths : FilePath → Prop)
    (keep : heap → Prop) :
    ∀ {returns : List (FilePath × IO.Error)} {reached : heap},
      RawOpenRetryTrace view directory calls init release start returns reached → Prop where
  | empty : SelectedEffects view directory calls init release start target files protectedPaths keep .empty
  | readOnly {earlier more : List (FilePath × IO.Error)} {entry reached : heap}
      {prior : RawOpenRetryTrace view directory calls init release start earlier entry}
      {attempts : RawFinalizedOpenAttempts view directory calls init release entry more reached}
      (before : SelectedEffects view directory calls init release start target files protectedPaths keep prior)
      (frame : (files entry).Frames protectedPaths (files reached))
      (carries : keep entry → keep reached) :
      SelectedEffects view directory calls init release start target files protectedPaths keep (.readOnly prior attempts)
  | repair {earlier : List (FilePath × IO.Error)} {entry : heap} {workerImage : FileImage}
      {prior : RawOpenRetryTrace view directory calls init release start earlier entry}
      {input : FilePath} {failed : RawFinalizedOpenAttempt view directory calls init release input entry workerImage}
      (before : SelectedEffects view directory calls init release start target files protectedPaths keep prior)
      (repair : EffectTrace target (view.files entry).image workerImage)
      (frame : (files entry).Frames protectedPaths (files failed.reached))
      (carries : keep entry → keep failed.reached) :
      SelectedEffects view directory calls init release start target files protectedPaths keep (.repair prior input failed)

/-- Read-only failures keep the current image. The repair effects start
at that same image and are preserved through finalization. Both cases
compose the independent frame on the unchanged physical files. -/
theorem RawOpenRetryTrace.SelectedEffects.preserves {target : Target} {files : heap → CheckpointSurvivingFiles}
    {protectedPaths : FilePath → Prop} {keep : heap → Prop} {returns : List (FilePath × IO.Error)} {reached : heap}
    {attempts : RawOpenRetryTrace view directory calls init release start returns reached}
    (effects : RawOpenRetryTrace.SelectedEffects view directory calls init release start target files protectedPaths keep attempts)
    (valid : (view.files start).image.Valid target) :
    (view.files reached).image.Valid target ∧
      (view.files reached).image.kept = (view.files start).image.kept ∧
      (files start).Frames protectedPaths (files reached) ∧
      (view.descriptors reached).inode = (view.descriptors start).inode ∧
      (keep start → keep reached) := by
  induction effects with
  | empty => exact ⟨valid, rfl, fun _ _ => ⟨rfl, fun _ _ => rfl⟩, rfl, id⟩
  | @readOnly _ _ entry reached prior block _ frame carries ih =>
    obtain ⟨sameInodes, sameImage⟩ := block.preserves
    exact ⟨sameImage.symm ▸ ih.1, (congrArg FileImage.kept sameImage).trans ih.2.1,
      ih.2.2.1.trans frame, sameInodes.trans ih.2.2.2.1, carries ∘ ih.2.2.2.2⟩
  | @repair _ entry workerImage prior input failed _ repair frame carries ih =>
    obtain ⟨_, _, _, _, _, sameInodes, returnedImage, _⟩ := failed.returns
    have next := repair.valid ih.1.selected ih.1.keeper ih.1.later
    exact ⟨returnedImage.symm ▸ next, (congrArg FileImage.kept returnedImage).trans (repair.keepsSealed.trans ih.2.1),
      ih.2.2.1.trans frame, sameInodes.trans ih.2.2.2.1, carries ∘ ih.2.2.2.2⟩

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
    {protectedPaths : FilePath → Prop} {keep : heap → Prop}
    {attempts : RawOpenRetryTrace view current.state.session.directory calls init release start returns reached}
    (effects : RawOpenRetryTrace.SelectedEffects view current.state.session.directory calls init release start
      target files protectedPaths keep attempts) (initial : (view.files start).image.Valid target) :
    Nonempty (current.SelectedWritePlan batch target (view.files reached).image) ∧
      (view.files reached).image.kept = (view.files start).image.kept ∧
      (files start).Frames protectedPaths (files reached) ∧ (keep start → keep reached) := by
  obtain ⟨observed, sealed, frame, _, carries⟩ := effects.preserves initial
  exact ⟨current.preparesSelectedWrite prepared fits admitted observed manifest, sealed, frame, carries⟩

end Alvoki.Storage.DiskSession
