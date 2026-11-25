import Alvoki.Storage.Disk.NativeRawCheckpointDigestError

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {fileCalls : MarkedTemporaryReadCalls heap}

/-- Project the reported marker failure from the real cache heap. The
successful open and both chunk callbacks use the same physical handle.
Its finalizer runs before the failed read returns to the held worker. -/
structure RawMarkerChunkReadError (fault : HeldMarkerChunkFailure admission)
    (seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock)
    (fileCalls : MarkedTemporaryReadCalls heap) where
  sameLookup : fileCalls.stat = calls.lookup
  flat : optionalMetadataWith (calls.lookup (directory.file .wal)) seed.afterPending = .ok none seed.afterPending
  manifestStat : calls.lookup (directory.file .manifest) seed.afterPending =
    .ok ((fault.reads.stat (directory.file .manifest)).map Prod.fst) seed.afterPending
  markerStat : calls.lookup (directory.file .walBoundary) seed.afterPending =
    .ok ((fault.reads.stat (directory.file .walBoundary)).map Prod.fst) seed.afterPending
  handle : IO.FS.Handle
  opened : heap
  afterChunk : heap
  failed : heap
  reached : heap
  openRaw : fileCalls.openRead (directory.file .walBoundary) seed.afterPending = .ok handle opened
  sameOpen : fault.reads.openRead (directory.file .walBoundary) = .ok (view.handle opened handle)
  openedCensus : (view.handle opened handle).1 = view.descriptors opened
  first : fileCalls.readChunk handle WAL.Boundary.acquisitionLimit.toUSize opened = .ok fault.shortChunk afterChunk
  afterChunkHandle : view.handle afterChunk handle = (view.descriptors afterChunk, fault.slot, fault.next)
  second : fileCalls.readChunk handle (WAL.Boundary.acquisitionLimit - fault.shortChunk.size).toUSize afterChunk =
    .error fault.cause failed
  failedHandle : view.handle failed handle = (view.descriptors failed, fault.slot, fault.failedCursor)
  firstDrops : List LockReferenceDrop
  laterDrops : List LockReferenceDrop
  duringRead : fault.duringRead = firstDrops ++ laterDrops
  afterChunkCensus : view.descriptors afterChunk = (view.descriptors opened).afterDrops firstDrops
  failedCensus : view.descriptors failed = (view.descriptors afterChunk).afterDrops laterDrops
  release : dataErrorDropState fileCalls.release handle failed = reached
  releasedCensus : view.descriptors reached = (view.descriptors failed).afterDrops [fault.close]
  openFrame : MarkedReadCacheFrame seed seed.afterPending opened
  firstFrame : MarkedReadCacheFrame seed opened afterChunk
  failedFrame : MarkedReadCacheFrame seed afterChunk failed
  releasedFrame : MarkedReadCacheFrame seed failed reached

namespace RawMarkerChunkReadError

variable {fault : HeldMarkerChunkFailure admission}
variable (seen : RawMarkerChunkReadError (admitted := admitted) fault seed fileCalls)

include seen in
theorem missingManifest :
    fileCalls.readOptional directory (directory.file .manifest) seed.afterPending = .ok none seed.afterPending := by
  obtain ⟨name, message, absent⟩ := fault.manifestProbe
  apply fileCalls.readOptionalMissing directory _ (name := name) (message := message)
  simpa only [seen.sameLookup, absent, Except.map] using seen.manifestStat

include seen in
private theorem statMarker :
    fileCalls.stat (directory.file .walBoundary) seed.afterPending = .ok (.ok fault.metadata) seed.afterPending := by
  simpa only [seen.sameLookup, fault.stat, Except.map] using seen.markerStat

structure Released : Prop where
  returned : fileCalls.readOptional directory (directory.file .walBoundary) seed.afterPending =
    .error fault.cause seen.reached
  opened : (view.handle seen.opened seen.handle).2.1 = fault.slot
  selectedInode : (view.descriptors seen.opened).inode fault.slot.description =
    admission.view.modelObject fault.statLookup.child
  chunkHandle : view.handle seen.afterChunk seen.handle =
    (view.descriptors seen.afterChunk, fault.slot, fault.shortChunk.size)
  prefixBytes : fault.shortChunk = fault.source.extract 0 fault.shortChunk.size
  failed : view.handle seen.failed seen.handle = (view.descriptors seen.failed, fault.slot, fault.failedCursor)
  live : fault.slot ∈ (view.descriptors seen.opened).slots ∧
    fault.slot ∈ (view.descriptors seen.afterChunk).slots ∧ fault.slot ∈ (view.descriptors seen.failed).slots
  census : view.descriptors seen.reached = fault.afterRead
  retired : (view.descriptors seen.reached).references fault.slot.description = []
  held : admission.owner ∈ (view.descriptors seen.reached).slots ∧ admission.cached ∈ (view.descriptors seen.reached).slots
  frame : MarkedReadCacheFrame seed seed.afterPending seen.reached

/-- The stat and read of the selected inode describe the same owned
directory, bytes and cursor as the projected failure. The reported
finalization retires just that temporary description. -/
theorem releasesSelected : seen.Released := by
  have body := readPrefixUntilEofWith_shortThenError (IO.userError "invalid WAL boundary length")
    (fileCalls.readChunk seen.handle) fault.positive fault.short (bytes := ByteArray.empty) seen.first seen.second
  have failed := fileCalls.readWith_error (directory.file .walBoundary)
    (fun file => readPrefixUntilEofWith (IO.userError "invalid WAL boundary length") (fileCalls.readChunk file)
      WAL.Boundary.acquisitionLimit ByteArray.empty) seen.openRaw body
  rw [seen.release] at failed
  have returned : fileCalls.readOptional directory (directory.file .walBoundary) seed.afterPending =
      .error fault.cause seen.reached := by
    rw [fileCalls.readOptionalMarker_effects directory seen.statMarker fault.regular]
    simp only [Bind.bind, EStateM.bind, failed]
  have opened := Except.ok.inj (seen.sameOpen.symm.trans fault.opened)
  have inserted : view.descriptors seen.opened = (admission.reached.afterDrops fault.beforeOpen).insert fault.slot fault.free :=
    seen.openedCensus.symm.trans (congrArg Prod.fst opened)
  have failedCensus : view.descriptors seen.failed = (view.descriptors seen.opened).afterDrops fault.duringRead := by
    rw [seen.failedCensus, seen.afterChunkCensus, DescriptorInventory.afterDrops_append, seen.duringRead]
  have closed : view.descriptors seen.reached = fault.afterRead := by
    unfold HeldMarkerChunkFailure.afterRead
    rw [seen.releasedCensus, failedCensus, inserted, DescriptorInventory.afterDrops_append, fault.finalizes,
      DescriptorInventory.insert_thenClose, DescriptorInventory.afterDrops_append, List.append_assoc]
  obtain ⟨_, cursor, bytes, inode, live, retired, owner, cache⟩ := fault.custody
  have atOpen : fault.slot ∈ (view.descriptors seen.opened).slots := by
    rw [inserted]
    exact List.mem_cons_self
  have atChunk : fault.slot ∈ (view.descriptors seen.afterChunk).slots := by
    rw [seen.afterChunkCensus, inserted]
    exact live _ _ seen.duringRead
  have atError : fault.slot ∈ (view.descriptors seen.failed).slots := by
    rw [failedCensus, inserted]
    exact live _ [] (by simp)
  refine ⟨returned, congrArg (fun slot : CheckpointOpenHandle => slot.2.1) opened, ?_, ?_, cursor ▸ bytes,
    seen.failedHandle, ⟨atOpen, atChunk, atError⟩, closed, closed.symm ▸ retired, closed.symm ▸ ⟨owner, cache⟩,
    ((seen.openFrame.trans seen.firstFrame).trans seen.failedFrame).trans seen.releasedFrame⟩
  · rw [inserted]
    exact inode
  · rw [seen.afterChunkHandle, cursor]

/-- The marked worker reaches the exact reported error after the
absent checkpoint. No marker decoding, listing, or WAL payload runs. -/
theorem stopsMarkedWorker
    (directoryCalls : MarkedDirectoryReadCalls heap stream) (callbacks : AlignedKeeperCacheCallbacks heap)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit) (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (cache : DiskTable.OpenSyncFiles) :
    calls.recoverMarkedWithCacheRefs fileCalls directoryCalls callbacks seed.directoryRef seed.activeRef seed.pendingRef
      remove write rename bootstrap directory cache seed.afterPending = .error fault.cause seen.reached := by
  have route : optionalMetadataWith (calls.lookup (directory.file .walBoundary)) seed.afterPending =
      .ok (some fault.metadata) seed.afterPending := by
    simp only [optionalMetadataWith, Bind.bind, EStateM.bind, ← seen.sameLookup, seen.statMarker, Pure.pure, EStateM.pure]
  simp only [RawOpenAdmissionCallbacks.recoverMarkedWithCacheRefs, recoverSegmentedWalWith, rejectFlatWalWith,
    reopenMarkedBoundedWithCachedExtents, prepareBoundedMarkedFromReaders, readIntegrityCheckpointSized,
    Bind.bind, EStateM.bind, seen.flat, route, Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
    ↓reduceIte, Pure.pure, EStateM.pure, seen.missingManifest, seen.releasesSelected.returned]

end RawMarkerChunkReadError

section

variable {admission : CensusOpenAdmissionReports input directory (view.descriptors entry) (view.files entry)}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {fault : HeldMarkerChunkFailure admission}
  {release : IO.FS.Handle → heap → heap}

/-- Carry this read error through the same cache drop, unlock and final
lock drop as other finalized retries. -/
noncomputable def RawMarkerChunkReadError.finalizedAttempt
    (seen : RawMarkerChunkReadError (admitted := admitted) fault seed fileCalls)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed seen.reached)
    (directoryCalls : MarkedDirectoryReadCalls heap stream) (callbacks : AlignedKeeperCacheCallbacks heap)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit) (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap DiskTable)
    (finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner disposal.reached) :
    RawFinalizedOpenAttempt view directory calls init release input entry :=
  RawFinalizedOpenAttempt.ofMarkedRejection seen.releasesSelected.frame (by
      rw [seen.releasesSelected.census]
      rfl)
    disposal directoryCalls callbacks remove write rename bootstrap install
    (seen.stopsMarkedWorker directoryCalls callbacks remove write rename bootstrap) finalized

end

end Alvoki.Storage.DiskSession
