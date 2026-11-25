import Alvoki.Storage.Disk.NativeRawManifestChunkError

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {admission : CensusOpenAdmissionReports input directory (view.descriptors entry) (view.files entry)}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {fileCalls : MarkedTemporaryReadCalls heap} {release : IO.FS.Handle → heap → heap}

/-- A reported lookup error other than ENOENT is returned before the
optional reader attempts any open. Its reached heap carries the error. -/
theorem MarkedTemporaryReadCalls.readOptionalStatError (fileCalls : MarkedTemporaryReadCalls heap)
    (directory : DiskDirectory) (path : FilePath) {before reached : heap} {cause : IO.Error}
    (stat : fileCalls.stat path before = .ok (.error cause) reached)
    (notMissing : ∀ name message, cause ≠ .noFileOrDirectory name 2 message) :
    fileCalls.readOptional directory path before = .error cause reached := by
  simp only [MarkedTemporaryReadCalls.readOptional, readOptionalDatabaseFileWithMetadata,
    Bind.bind, EStateM.bind, stat]
  cases cause <;> try rfl
  case noFileOrDirectory name code message =>
    have codeNotMissing : code ≠ 2 := fun same => notMissing name message (by rw [same])
    simp [codeNotMissing, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- On the selected marked route the no-follow MANIFEST lookup reports
an error without identifying any child or opening a manifest handle. -/
structure RawManifestStatError
    (seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock)
    (fileCalls : MarkedTemporaryReadCalls heap) where
  flat : optionalMetadataWith (calls.lookup (directory.file .wal)) seed.afterPending = .ok none seed.afterPending
  marker : IO.FS.Metadata
  marked : optionalMetadataWith (calls.lookup (directory.file .walBoundary)) seed.afterPending =
    .ok (some marker) seed.afterPending
  sameLookup : fileCalls.stat = calls.lookup
  cause : IO.Error
  reached : heap
  stat : calls.lookup (directory.file .manifest) seed.afterPending = .ok (.error cause) reached
  notMissing : ∀ name message, cause ≠ .noFileOrDirectory name 2 message
  census : view.descriptors reached = view.descriptors seed.afterPending
  frame : MarkedReadCacheFrame seed seed.afterPending reached

namespace RawManifestStatError

variable (seen : RawManifestStatError (admitted := admitted) seed fileCalls)

theorem rejectsCheckpoint :
    readIntegrityCheckpointSized directory (fileCalls.readOptional directory (directory.file .manifest))
      fileCalls.runSize fileCalls.runPrefix seed.afterPending = .error seen.cause seen.reached := by
  have stat : fileCalls.stat (directory.file .manifest) seed.afterPending = .ok (.error seen.cause) seen.reached := by
    rw [seen.sameLookup, seen.stat]
  simp only [readIntegrityCheckpointSized, Bind.bind, EStateM.bind,
    fileCalls.readOptionalStatError directory _ stat seen.notMissing]

/-- No manifest descriptor was opened. The cache scope drop, unlock and
final lock drop begin at the exact reached heap of the failed lookup. -/
noncomputable def finalizedAttempt
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
    (RawOpenAdmissionCallbacks.stopsMarkedAtCheckpoint seen.flat seen.marked seen.rejectsCheckpoint directoryCalls callbacks
      remove write rename bootstrap) finalized

end RawManifestStatError

end Alvoki.Storage.DiskSession
