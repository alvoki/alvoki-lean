import Alvoki.Storage.Disk.NativeRawManifestChunkError
import Alvoki.Storage.Disk.NativeMarkedOpenInterpreter

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

/-- The fixed marked worker's read and replay prefix at this attempt's
allocated pending cell. Repair and installation follow this action. -/
abbrev RawMarkedOpenInterpreter.prepareMarkedRead
    (source : RawMarkedOpenInterpreter heap stream) (directory : DiskDirectory)
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) : EStateM IO.Error heap (Plan × Reopened × Nat) :=
  let sync := source.keeperCallbacks.withFileReads source.fileCalls
  prepareBoundedMarkedFromReaders directory
    (readIntegrityCheckpointSized directory (source.fileCalls.readOptional directory (directory.file .manifest))
      source.fileCalls.runSize source.fileCalls.runPrefix)
    (source.fileCalls.readOptional directory)
    (fun watermark length => readSelectedWithCachedExtents directory watermark length source.directoryCalls.run
      (MarkedWalExtentReports.inspect source.fileCalls) source.fileCalls.seal (source.fileCalls.readKeeperWithRelease
        (fun path handle => sync.modifyPending pending (SyncHandleRouting.pushPending path handle))))

/-- Any ordinary error from the actual preparation reaches the worker
return before repair or installation. -/
theorem RawMarkedOpenInterpreter.workerRejectsPreparation
    (source : RawMarkedOpenInterpreter heap stream)
    (directory : DiskDirectory) (lock : IO.FS.Handle) (cache : DiskTable.OpenSyncFiles)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    {before checked atCheckpoint reached : heap} {metadata : IO.FS.Metadata} {cause : IO.Error}
    (flat : rejectFlatWalWith directory (optionalMetadataWith (source.calls.lookup (directory.file .wal)))
      before = .ok () checked)
    (marked : optionalMetadataWith (source.calls.lookup (directory.file .walBoundary)) checked =
      .ok (some metadata) atCheckpoint)
    (rejected : source.prepareMarkedRead directory pending atCheckpoint = .error cause reached) :
    source.worker cached active pending directory lock cache before = .error cause reached := by
  unfold RawMarkedOpenInterpreter.prepareMarkedRead at rejected
  simp only [RawMarkedOpenInterpreter.worker, recoverHealthyMarkedWithRefs, recoverSegmentedWalWith,
    reopenMarkedBoundedWithCachedExtents, Bind.bind, EStateM.bind, flat, marked, Option.isSome_some, ↓reduceIte, rejected]

/-- The actual marked checkpoint error stops the worker at the read's
return. Marker payload, WAL selection and installation have not run. -/
theorem RawMarkedOpenInterpreter.workerRejectsCheckpoint
    (source : RawMarkedOpenInterpreter heap stream)
    (directory : DiskDirectory) (lock : IO.FS.Handle) (cache : DiskTable.OpenSyncFiles)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    {before checked atCheckpoint reached : heap} {metadata : IO.FS.Metadata} {cause : IO.Error}
    (flat : rejectFlatWalWith directory (optionalMetadataWith (source.calls.lookup (directory.file .wal)))
      before = .ok () checked)
    (marked : optionalMetadataWith (source.calls.lookup (directory.file .walBoundary)) checked =
      .ok (some metadata) atCheckpoint)
    (rejected : readIntegrityCheckpointSized directory
      (source.fileCalls.readOptional directory (directory.file .manifest))
      source.fileCalls.runSize source.fileCalls.runPrefix atCheckpoint = .error cause reached) :
    source.worker cached active pending directory lock cache before = .error cause reached := by
  apply source.workerRejectsPreparation directory lock cache cached active pending flat marked
  simp only [RawMarkedOpenInterpreter.prepareMarkedRead, prepareBoundedMarkedFromReaders, Bind.bind, EStateM.bind,
    rejected]

section FixedInterpreter

variable (source : RawMarkedOpenInterpreter heap stream)
  {admission : CensusOpenAdmissionReports input directory (view.descriptors entry) (view.files entry)}
  {raw : RawOpenAdmissionReport admission view source.calls entry}
  {allocation : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock}
  (seen : RawManifestStatError (admitted := raw) allocation source.fileCalls)

private theorem RawManifestStatError.rejectsFixedWorker (cache : DiskTable.OpenSyncFiles) :
    source.worker allocation.directoryRef allocation.activeRef allocation.pendingRef directory raw.lock cache
      allocation.afterPending = .error seen.cause seen.reached := by
  have flat : rejectFlatWalWith directory (optionalMetadataWith (source.calls.lookup (directory.file .wal)))
      allocation.afterPending = .ok () allocation.afterPending := by
    simp [rejectFlatWalWith, seen.flat, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  exact source.workerRejectsCheckpoint directory raw.lock cache allocation.directoryRef allocation.activeRef
    allocation.pendingRef flat seen.marked seen.rejectsCheckpoint

/-- The fixed opener returns a held MANIFEST lookup error through the
same finalizers as a failed repair. The image seen by the next attempt
is unchanged. -/
theorem RawManifestStatError.finalizesWithInterpreter
    (disposal : RawOpenCacheDisposal (admitted := raw) allocation seen.reached)
    (sameDisposal : source.dispose = disposal.dispose)
    (finalized : RawOpenErrorLockFinalization view directory source.release raw.lock admission.owner disposal.reached) :
    ∃ failed : RawFinalizedOpenAttempt view directory source.calls source.init source.release input entry,
      source.openTable input entry = .error failed.diagnostic failed.reached ∧
      failed.diagnostic = disposal.diagnostic seen.cause ∧ failed.reached = finalized.reached := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, held, _⟩ := allocation.installs
  have stopped := seen.rejectsFixedWorker source
  have inodes : (view.descriptors seen.reached).inode = (view.descriptors entry).inode := by
    rw [seen.census, allocation.pendingSlots, allocation.activeSlots, allocation.directorySlots, allocation.openedSlots]
    rfl
  let failed : RawFinalizedOpenAttempt view directory source.calls source.init source.release input entry :=
    { admission := admission
      admitted := raw
      seed := allocation
      beforeCleanup := seen.reached
      disposed := disposal
      recover := source.worker allocation.directoryRef allocation.activeRef allocation.pendingRef
      cause := seen.cause
      rejected := disposal.returns _ _ stopped (seen.frame.files.trans held)
      workerInodes := inodes
      finalized := finalized }
  exact ⟨failed, disposal.returnsMarkedInterpreter source sameDisposal (stopped _) finalized, rfl, rfl⟩

end FixedInterpreter

end Alvoki.Storage.DiskSession
