import Alvoki.Storage.Disk.Proofs.Recovery.NativeRawCheckpointExtentError
import Alvoki.Storage.Disk.Proofs.Recovery.NativeTemporaryChunkReadFailure

namespace Alvoki.Storage.DiskSession

open System Manifest WalSegmentRepair SyncHandleRouting

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {fileCalls : MarkedTemporaryReadCalls heap}

private abbrev runPath (selected : RawSelectedCheckpointRunStat (admitted := admitted) seed fileCalls) : FilePath :=
  directory.file (.run selected.reads.manifest.header.generation selected.index)

private abbrev beforeRun (selected : RawSelectedCheckpointRunStat (admitted := admitted) seed fileCalls) : heap :=
  selected.reads.atRun selected.index

/-- A selected run passes its stamped extent before the raw reads. -/
structure RawCheckpointChunkReadError (selected : RawSelectedCheckpointRunStat (admitted := admitted) seed fileCalls)
    extends RawTemporaryChunkReadFailure seed fileCalls (runPath selected) selected.child selected.stamp.byteCount.toNat
      (beforeRun selected) where
  extent : selected.metadata.byteSize.toNat = selected.stamp.byteCount.toNat
  fits : selected.stamp.byteCount.toNat < USize.size
  contents : selected.reads.reads.objectBytes (admission.view.modelObject selected.child.child) = some bytes
  physicalExtent : bytes.size = selected.metadata.byteSize.toNat

namespace RawCheckpointChunkReadError

variable {selected : RawSelectedCheckpointRunStat (admitted := admitted) seed fileCalls}

structure Released (seen : RawCheckpointChunkReadError selected) : Prop where
  returned : fileCalls.runPrefix (runPath selected) selected.stamp.byteCount.toNat (beforeRun selected) =
    .error seen.cause seen.reached
  inode : (view.handle seen.opened seen.handle).1.inode (view.handle seen.opened seen.handle).2.1.description =
    admission.view.modelObject selected.child.child
  bytes : selected.reads.reads.objectBytes (admission.view.modelObject selected.child.child) = some seen.bytes
  extent : seen.bytes.size = selected.stamp.byteCount.toNat
  prefixBytes : seen.chunk = seen.bytes.extract 0 seen.chunk.size
  afterChunk : view.handle seen.afterChunk seen.handle = (view.descriptors seen.opened, seen.slot, seen.chunk.size)
  failedHandle : (view.handle seen.failed seen.handle).1 = view.descriptors seen.opened ∧
    (view.handle seen.failed seen.handle).2.1 = seen.slot
  live : seen.slot ∈ (view.descriptors seen.opened).slots ∧
    seen.slot ∈ (view.descriptors seen.afterChunk).slots ∧ seen.slot ∈ (view.descriptors seen.failed).slots
  census : view.descriptors seen.reached = (view.descriptors (beforeRun selected)).afterDrops
    (seen.beforeOpen ++ [seen.slot.closeEvent])
  retired : (view.descriptors seen.reached).references seen.slot.description = []
  frame : MarkedReadCacheFrame seed (beforeRun selected) seen.reached

theorem releasesSelected (seen : RawCheckpointChunkReadError selected) : seen.Released := by
  have body := readExactPrefixWith_shortThenError (IO.userError checkpointIntegrityMismatch)
    (fileCalls.readChunk seen.handle) seen.positive seen.short seen.first seen.second
  have failed := fileCalls.readWith_error (runPath selected)
    (fun handle => readExactPrefixWith (IO.userError checkpointIntegrityMismatch) (fileCalls.readChunk handle)
      selected.stamp.byteCount.toNat ByteArray.empty) seen.openRaw body
  rw [seen.release] at failed
  have released := seen.toRawTemporaryChunkReadFailure.releases
  exact ⟨failed, released.inode, seen.contents, seen.physicalExtent.trans seen.extent, seen.firstBytes,
    released.afterChunk, released.failedHandle, released.live, released.census, released.retired, released.frame⟩

/-- A transient run read error returns after the same descriptor has
closed, before restoration, later runs or WAL recovery. -/
theorem rejects (seen : RawCheckpointChunkReadError selected) :
    readIntegrityCheckpointSized directory (fileCalls.readOptional directory (directory.file .manifest))
      fileCalls.runSize fileCalls.runPrefix seed.afterPending = .error seen.cause seen.reached ∧
    MarkedReadCacheFrame seed seed.afterPending seen.reached ∧
    (view.descriptors seen.reached).inode = admission.reached.inode := by
  have released := seen.releasesSelected
  obtain ⟨earlierFrame, inodes⟩ := selected.reads.frames (Nat.le_refl _)
  have sized := selected.measures
  rw [seen.extent] at sized
  refine ⟨readIntegrityCheckpointSized_rejectsRead directory _ _ _ selected.reads.readsManifest selected.reads.decoded
    selected.within selected.stamped selected.readsEarlier seen.fits sized released.returned,
    earlierFrame.trans released.frame, ?_⟩
  rw [released.census]
  exact inodes

end RawCheckpointChunkReadError

section

variable {admission : CensusOpenAdmissionReports input directory (view.descriptors entry) (view.files entry)}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {release : IO.FS.Handle → heap → heap}
  {selected : RawSelectedCheckpointRunStat (admitted := admitted) seed fileCalls}

/-- Scope the same failed reader with the original cache disposal,
the reported unlock, and final lock-slot drop. -/
noncomputable def RawCheckpointChunkReadError.finalizedAttempt
    (seen : RawCheckpointChunkReadError selected)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed seen.reached)
    (directoryCalls : MarkedDirectoryReadCalls heap stream) (callbacks : AlignedKeeperCacheCallbacks heap)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit) (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap DiskTable)
    (finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner disposal.reached) :
    RawFinalizedOpenAttempt view directory calls init release input entry :=
  selected.reads.finalizedAttempt seen.rejects.1 seen.rejects.2.1 seen.rejects.2.2 disposal
    directoryCalls callbacks remove write rename bootstrap install finalized

end

end Alvoki.Storage.DiskSession
