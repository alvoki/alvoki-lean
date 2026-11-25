import Alvoki.Storage.Disk.FailedCheckpointDigestCensus
import Alvoki.Storage.Disk.NativeFinalizedOpenRetries
import Alvoki.Storage.Disk.NativeMarkedTableOpen

namespace Alvoki.Storage.DiskSession

open System Manifest WalSegmentRepair

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {fileCalls : MarkedTemporaryReadCalls heap}

/-- A decoded manifest can select regular runs of the expected extents
whose exact acquired bytes fail digest validation. All selected run
handles are released before the decoder can return that mismatch. -/
structure RawCheckpointDigestRead
    (seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock)
    (fileCalls : MarkedTemporaryReadCalls heap) where
  flat : optionalMetadataWith (calls.lookup (directory.file .wal)) seed.afterPending = .ok none seed.afterPending
  sameLookup : fileCalls.stat = calls.lookup
  marker : IO.FS.Metadata
  marked : optionalMetadataWith (calls.lookup (directory.file .walBoundary)) seed.afterPending =
    .ok (some marker) seed.afterPending
  reads : CheckpointRunChunkReads
  bytes : ByteArray
  bound : retry.image.directory.active.manifest = some bytes
  manifest : IntegrityCheckpoint
  decoded : IntegrityCheckpoint.decode bytes = .ok manifest
  file : HeldMetadataFile reads (directory.file .manifest) "MANIFEST" admission.view admission.root bytes
  atRun : Nat → heap
  manifestDrops : List LockReferenceDrop
  manifestStat : calls.lookup (directory.file .manifest) seed.afterPending =
    .ok ((reads.stat (directory.file .manifest)).map Prod.fst) seed.afterPending
  manifestCustody : TemporaryPrefixCustody file.calls admission.reached manifestDrops
  manifestRead : RawTemporaryReadReport reads seed fileCalls (directory.file .manifest) manifestDrops
    (fun handle => readIntegrityManifestPrefixWith (fileCalls.readChunk handle) file.calls.metadata.byteSize.toNat)
    bytes seed.afterPending (atRun 0)
  payload : Nat → ByteArray
  runDrops : Nat → List LockReferenceDrop
  run : ∀ index < manifest.header.runCount.toNat,
    ReachedDigestRun reads directory admission.view admission.root manifest index (payload index)
      (view.descriptors (atRun index)) (runDrops index)
  runStat : ∀ index < manifest.header.runCount.toNat,
    let path := directory.file (.run manifest.header.generation index)
    calls.lookup path (atRun index) = .ok ((reads.stat path).map Prod.fst) (atRun index)
  runRead : ∀ index (within : index < manifest.header.runCount.toNat),
    RawTemporaryReadReport reads seed fileCalls (directory.file (.run manifest.header.generation index)) (runDrops index)
      (fun handle => readExactPrefixWith (IO.userError checkpointIntegrityMismatch) (fileCalls.readChunk handle)
        (run index within).stamp.byteCount.toNat ByteArray.empty) (payload index) (atRun index) (atRun (index + 1))
  index : Nat
  within : index < manifest.header.runCount.toNat
  mismatch : checksumRun (payload index) ≠ (run index within).stamp.checksum

namespace RawCheckpointDigestRead

def afterRead (seen : RawCheckpointDigestRead (admitted := admitted) seed fileCalls) : heap :=
  seen.atRun seen.manifest.header.runCount.toNat

theorem readsRun (seen : RawCheckpointDigestRead (admitted := admitted) seed fileCalls)
    {index : Nat} (within : index < seen.manifest.header.runCount.toNat) :
    let path := directory.file (.run seen.manifest.header.generation index)
    let report := seen.run index within
    fileCalls.runSize path (seen.atRun index) = .ok report.stamp.byteCount.toNat (seen.atRun index) ∧
    fileCalls.runPrefix path report.stamp.byteCount.toNat (seen.atRun index) = .ok (seen.payload index) (seen.atRun (index + 1)) ∧
    MarkedReadCacheFrame seed (seen.atRun index) (seen.atRun (index + 1)) ∧
    view.descriptors (seen.atRun (index + 1)) =
      (view.descriptors (seen.atRun index)).afterDrops (report.custody.beforeOpen ++ seen.runDrops index) ∧
    (view.descriptors (seen.atRun (index + 1))).references report.file.slot.description = [] := by
  intro path report
  have stat := seen.runStat index within
  change calls.lookup path (seen.atRun index) = .ok ((seen.reads.stat path).map Prod.fst) (seen.atRun index) at stat
  rw [report.file.stat] at stat
  have size : fileCalls.runSize path (seen.atRun index) = .ok (seen.payload index).size (seen.atRun index) :=
    fileCalls.measuresRun (by simpa only [seen.sameLookup, Except.map] using stat) report.file.regular
      (report.file.observesFile report.bound report.contents).extent
  let raw := seen.runRead index within
  obtain ⟨returned, frame⟩ := raw.returns
  obtain ⟨census, released, _⟩ := raw.censusAfter report.custody
  exact ⟨by simpa only [report.extent] using size, returned, frame, census, released⟩

/-- The native sized reader acquires the exact selected generation and
validates the completed array only after the last temporary release. -/
theorem rejects (seen : RawCheckpointDigestRead (admitted := admitted) seed fileCalls) :
    readIntegrityCheckpointSized directory (fileCalls.readOptional directory (directory.file .manifest))
      fileCalls.runSize fileCalls.runPrefix seed.afterPending =
      .error (IO.userError checkpointIntegrityMismatch) seen.afterRead ∧
    MarkedReadCacheFrame seed seed.afterPending seen.afterRead ∧
    (view.descriptors seen.afterRead).inode = admission.reached.inode := by
  have stat := seen.manifestStat
  rw [seen.file.calls.stat] at stat
  have manifest := fileCalls.readOptionalManifest directory (by simpa only [seen.sameLookup, Except.map] using stat)
    seen.file.calls.regular seen.manifestRead.returns.1
  have runs := readIntegrityRunBytesSized_effects directory seen.manifest fileCalls.runSize fileCalls.runPrefix
    seen.atRun seen.payload (by
      intro index within
      let run := seen.run index within
      exact ⟨run.stamp, run.stamped, run.fits, run.extent, (seen.readsRun within).1, (seen.readsRun within).2.1⟩)
  let payloads := (List.range seen.manifest.header.runCount.toNat).map seen.payload
  have corrupt : payloads[seen.index]? = some (seen.payload seen.index) := by simp [payloads, seen.within]
  have rejected := IntegrityCheckpoint.rejects_run (seen.run seen.index seen.within).stamped corrupt (.inr seen.mismatch)
  have rejectedLoad : loadIntegrityRunSet seen.manifest payloads = .error checkpointIntegrityMismatch := by
    simp [loadIntegrityRunSet, rejected]
  have reached : ∀ index ≤ seen.manifest.header.runCount.toNat,
      MarkedReadCacheFrame seed seed.afterPending (seen.atRun index) ∧
        (view.descriptors (seen.atRun index)).inode = admission.reached.inode := by
    intro index
    induction index with
    | zero =>
      intro _
      refine ⟨seen.manifestRead.returns.2, ?_⟩
      rw [(seen.manifestRead.censusAfter seen.manifestCustody).1]
      rfl
    | succ index prior =>
      intro within
      have visited := Nat.lt_of_succ_le within
      obtain ⟨_, _, frame, census, _⟩ := seen.readsRun visited
      obtain ⟨oldFrame, oldInodes⟩ := prior (Nat.le_of_lt visited)
      refine ⟨oldFrame.trans frame, ?_⟩
      rw [census]
      exact oldInodes
  obtain ⟨frame, inodes⟩ := reached _ (Nat.le_refl _)
  refine ⟨?_, frame, inodes⟩
  simp [readIntegrityCheckpointSized, manifest, seen.decoded, runs, payloads, rejectedLoad, afterRead, Bind.bind,
    EStateM.bind, liftExcept, Except.mapError, throw, throwThe, MonadExceptOf.throw, EStateM.throw, Pure.pure, EStateM.pure]

/-- Digest verification returns before reading the marker payload or
calling any listing, WAL payload, repair, or installation operation. -/
theorem stopsMarkedWorker (seen : RawCheckpointDigestRead (admitted := admitted) seed fileCalls)
    (directoryCalls : MarkedDirectoryReadCalls heap stream) (callbacks : AlignedKeeperCacheCallbacks heap)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit) (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (cache : DiskTable.OpenSyncFiles) :
    calls.recoverMarkedWithCacheRefs fileCalls directoryCalls callbacks seed.directoryRef seed.activeRef seed.pendingRef
      remove write rename bootstrap directory cache seed.afterPending =
        .error (IO.userError checkpointIntegrityMismatch) seen.afterRead := by
  simp only [RawOpenAdmissionCallbacks.recoverMarkedWithCacheRefs, recoverSegmentedWalWith, rejectFlatWalWith,
    reopenMarkedBoundedWithCachedExtents, prepareBoundedMarkedFromReaders, Bind.bind, EStateM.bind, seen.flat, seen.marked,
    Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte, Pure.pure, EStateM.pure, seen.rejects.1]

end RawCheckpointDigestRead

section

variable {admission : CensusOpenAdmissionReports input directory (view.descriptors entry) (view.files entry)}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {release : IO.FS.Handle → heap → heap}

/-- The same read-only failed attempt can be retried after its reported
cache disposal, unlock, and final close of the exact acquired slot. -/
noncomputable def RawCheckpointDigestRead.finalizedAttempt
    (seen : RawCheckpointDigestRead (admitted := admitted) seed fileCalls)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed seen.afterRead)
    (directoryCalls : MarkedDirectoryReadCalls heap stream) (callbacks : AlignedKeeperCacheCallbacks heap)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit) (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap DiskTable)
    (finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner disposal.reached) :
    RawFinalizedOpenAttempt view directory calls init release input entry where
  admission := admission
  admitted := admitted
  seed := seed
  beforeCleanup := seen.afterRead
  disposed := disposal
  recover := fun resolved lock cache =>
    calls.recoverMarkedWithCacheRefs fileCalls directoryCalls callbacks seed.directoryRef seed.activeRef seed.pendingRef
      remove write rename bootstrap resolved cache >>= install resolved lock cache
  cause := IO.userError checkpointIntegrityMismatch
  rejected := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, files, _⟩ := seed.installs
    refine disposal.returns _ _ ?_ (seen.rejects.2.1.files.trans files)
    intro cache
    simp only [Bind.bind, EStateM.bind, seen.stopsMarkedWorker directoryCalls callbacks remove write rename bootstrap]
  workerInodes := seen.rejects.2.2
  finalized := finalized

end

end Alvoki.Storage.DiskSession
