import Alvoki.Storage.Disk.Proofs.Recovery.NativeRawManifestChunkError

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {fileCalls : MarkedTemporaryReadCalls heap}

/-- The no-follow stat succeeds. The read-only open of the same path
reports an error and leaves its selected binding and reached custody intact. -/
structure RawManifestOpenError
    (seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock)
    (fileCalls : MarkedTemporaryReadCalls heap)
    extends RawPresentManifestReadStat (admitted := admitted) seed fileCalls where
  bytes : ByteArray
  bound : retry.image.directory.active.manifest = some bytes
  contents : observations.objectBytes (admission.view.modelObject child.child) = some bytes
  extent : metadata.byteSize.toNat = bytes.size
  cause : IO.Error
  reached : heap
  openFailed : fileCalls.openRead (directory.file .manifest) seed.afterPending = .error cause reached
  census : view.descriptors reached = view.descriptors seed.afterPending
  frame : MarkedReadCacheFrame seed seed.afterPending reached

namespace RawManifestOpenError

variable (seen : RawManifestOpenError (admitted := admitted) seed fileCalls)

/-- The admitted reader returns the observed open error. Since no handle
was returned, it never enters the bounded read or the handle finalizer. -/
theorem rejectsSelected :
    fileCalls.readOptional directory (directory.file .manifest) seed.afterPending = .error seen.cause seen.reached ∧
    retry.image.directory.active.manifest = some seen.bytes ∧
    seen.observations.objectBytes (admission.view.modelObject seen.child.child) = some seen.bytes ∧
    seen.metadata.byteSize.toNat = seen.bytes.size := by
  refine ⟨?_, seen.bound, seen.contents, seen.extent⟩
  rw [seen.toRawPresentManifestReadStat.readEffects]
  simp only [MarkedTemporaryReadCalls.readWith, Bind.bind, EStateM.bind, seen.openFailed]

theorem rejectsCheckpoint :
    readIntegrityCheckpointSized directory (fileCalls.readOptional directory (directory.file .manifest))
      fileCalls.runSize fileCalls.runPrefix seed.afterPending = .error seen.cause seen.reached := by
  simp only [readIntegrityCheckpointSized, Bind.bind, EStateM.bind, seen.rejectsSelected.1]

end RawManifestOpenError

section

variable {admission : CensusOpenAdmissionReports input directory (view.descriptors entry) (view.files entry)}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {release : IO.FS.Handle → heap → heap}

/-- The original caller sees the same open diagnostic unless the
reported outer unlock fails. No manifest-handle release is required. -/
noncomputable def RawManifestOpenError.finalizedAttempt
    (seen : RawManifestOpenError (admitted := admitted) seed fileCalls)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed seen.reached)
    (directoryCalls : MarkedDirectoryReadCalls heap stream) (callbacks : AlignedKeeperCacheCallbacks heap)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit) (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap DiskTable)
    (finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner disposal.reached) :
    RawFinalizedOpenAttempt view directory calls init release input entry :=
  RawFinalizedOpenAttempt.ofMarkedRejection seen.frame (by
      rw [seen.census, seed.pendingSlots, seed.activeSlots, seed.directorySlots, seed.openedSlots]
      rfl)
    disposal directoryCalls callbacks remove write rename bootstrap install
    (seen.toRawPresentManifestReadStat.stopsMarkedWorker seen.rejectsCheckpoint directoryCalls callbacks
      remove write rename bootstrap) finalized

end

end Alvoki.Storage.DiskSession
