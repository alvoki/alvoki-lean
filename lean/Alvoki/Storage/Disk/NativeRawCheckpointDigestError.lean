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

/-- A marked opener reads the live manifest, then each selected run
in the requested prefix. Every successful read closes its own raw slot. -/
structure RawCheckpointRunPrefix
    (seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock)
    (fileCalls : MarkedTemporaryReadCalls heap) (stop : IntegrityCheckpoint → Nat) where
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
  run : ∀ index < stop manifest,
    ReachedDigestRun reads directory admission.view admission.root manifest index (payload index)
      (view.descriptors (atRun index)) (runDrops index)
  runStat : ∀ index < stop manifest,
    let path := directory.file (.run manifest.header.generation index)
    calls.lookup path (atRun index) = .ok ((reads.stat path).map Prod.fst) (atRun index)
  runRead : ∀ index (within : index < stop manifest),
    RawTemporaryReadReport reads seed fileCalls (directory.file (.run manifest.header.generation index)) (runDrops index)
      (fun handle => readExactPrefixWith (IO.userError checkpointIntegrityMismatch) (fileCalls.readChunk handle)
        (run index within).stamp.byteCount.toNat ByteArray.empty) (payload index) (atRun index) (atRun (index + 1))

namespace RawCheckpointRunPrefix

variable {stop : IntegrityCheckpoint → Nat}

theorem readsRun (seen : RawCheckpointRunPrefix (admitted := admitted) seed fileCalls stop)
    {index : Nat} (within : index < stop seen.manifest) :
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

theorem readsManifest (seen : RawCheckpointRunPrefix (admitted := admitted) seed fileCalls stop) :
    fileCalls.readOptional directory (directory.file .manifest) seed.afterPending =
      .ok (some seen.bytes) (seen.atRun 0) := by
  have stat := seen.manifestStat
  rw [seen.file.calls.stat] at stat
  exact fileCalls.readOptionalManifest directory (by simpa only [seen.sameLookup, Except.map] using stat)
    seen.file.calls.regular seen.manifestRead.returns.1

theorem readsPrefix (seen : RawCheckpointRunPrefix (admitted := admitted) seed fileCalls stop)
    {manifest : IntegrityCheckpoint} (sameStamps : manifest.runs = seen.manifest.runs)
    (sameGeneration : manifest.header.generation = seen.manifest.header.generation)
    (count : manifest.header.runCount.toNat = stop seen.manifest) :
    readIntegrityRunBytesSized directory manifest fileCalls.runSize fileCalls.runPrefix (seen.atRun 0) =
      .ok ((List.range (stop seen.manifest)).map seen.payload) (seen.atRun (stop seen.manifest)) := by
  rw [← count]
  apply readIntegrityRunBytesSized_effects
  intro index within
  have selected : index < stop seen.manifest := count ▸ within
  let run := seen.run index selected
  rw [sameStamps, sameGeneration]
  exact ⟨run.stamp, run.stamped, run.fits, run.extent, (seen.readsRun selected).1, (seen.readsRun selected).2.1⟩

theorem frames (seen : RawCheckpointRunPrefix (admitted := admitted) seed fileCalls stop)
    {index : Nat} (within : index ≤ stop seen.manifest) :
    MarkedReadCacheFrame seed seed.afterPending (seen.atRun index) ∧
      (view.descriptors (seen.atRun index)).inode = admission.reached.inode := by
  induction index with
  | zero =>
    refine ⟨seen.manifestRead.returns.2, ?_⟩
    rw [(seen.manifestRead.censusAfter seen.manifestCustody).1]
    rfl
  | succ index prior =>
    have visited := Nat.lt_of_succ_le within
    obtain ⟨_, _, frame, census, _⟩ := seen.readsRun visited
    obtain ⟨oldFrame, oldInodes⟩ := prior (Nat.le_of_lt visited)
    refine ⟨oldFrame.trans frame, ?_⟩
    rw [census]
    exact oldInodes

/-- A checkpoint reader that rejects before returning never reaches
the marker payload, listing, WAL reads, or repair. -/
theorem stopsMarkedWorker (seen : RawCheckpointRunPrefix (admitted := admitted) seed fileCalls stop)
    {cause : IO.Error} {reached : heap}
    (rejected : readIntegrityCheckpointSized directory (fileCalls.readOptional directory (directory.file .manifest))
      fileCalls.runSize fileCalls.runPrefix seed.afterPending = .error cause reached)
    (directoryCalls : MarkedDirectoryReadCalls heap stream) (callbacks : AlignedKeeperCacheCallbacks heap)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit) (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (cache : DiskTable.OpenSyncFiles) :
    calls.recoverMarkedWithCacheRefs fileCalls directoryCalls callbacks seed.directoryRef seed.activeRef seed.pendingRef
      remove write rename bootstrap directory cache seed.afterPending = .error cause reached := by
  simp only [RawOpenAdmissionCallbacks.recoverMarkedWithCacheRefs, recoverSegmentedWalWith, rejectFlatWalWith,
    reopenMarkedBoundedWithCachedExtents, prepareBoundedMarkedFromReaders, Bind.bind, EStateM.bind, seen.flat, seen.marked,
    Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte, Pure.pure, EStateM.pure, rejected]

end RawCheckpointRunPrefix

/-- All selected run handles close before the decoder can return a digest mismatch. -/
structure RawCheckpointDigestRead
    (seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock)
    (fileCalls : MarkedTemporaryReadCalls heap)
    extends RawCheckpointRunPrefix (admitted := admitted) seed fileCalls (fun manifest => manifest.header.runCount.toNat) where
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
    (view.descriptors (seen.atRun (index + 1))).references report.file.slot.description = [] :=
  seen.toRawCheckpointRunPrefix.readsRun within

/-- The sized reader validates the completed array after its last release. -/
theorem rejects (seen : RawCheckpointDigestRead (admitted := admitted) seed fileCalls) :
    readIntegrityCheckpointSized directory (fileCalls.readOptional directory (directory.file .manifest))
      fileCalls.runSize fileCalls.runPrefix seed.afterPending =
      .error (IO.userError checkpointIntegrityMismatch) seen.afterRead ∧
    MarkedReadCacheFrame seed seed.afterPending seen.afterRead ∧
    (view.descriptors seen.afterRead).inode = admission.reached.inode := by
  let payloads := (List.range seen.manifest.header.runCount.toNat).map seen.payload
  have corrupt : payloads[seen.index]? = some (seen.payload seen.index) := by simp [payloads, seen.within]
  have rejected := IntegrityCheckpoint.rejects_run (seen.run seen.index seen.within).stamped corrupt (.inr seen.mismatch)
  have rejectedLoad : loadIntegrityRunSet seen.manifest payloads = .error checkpointIntegrityMismatch := by
    simp [loadIntegrityRunSet, rejected]
  let reports := seen.toRawCheckpointRunPrefix
  have manifestRead : fileCalls.readOptional directory (directory.file .manifest) seed.afterPending =
      .ok (some seen.bytes) (seen.atRun 0) := reports.readsManifest
  have runs : readIntegrityRunBytesSized directory seen.manifest fileCalls.runSize fileCalls.runPrefix (seen.atRun 0) =
      .ok payloads seen.afterRead := reports.readsPrefix rfl rfl rfl
  refine ⟨?_, reports.frames (Nat.le_refl _)⟩
  simp [readIntegrityCheckpointSized, manifestRead, seen.decoded, runs, rejectedLoad, Bind.bind,
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
        .error (IO.userError checkpointIntegrityMismatch) seen.afterRead :=
  seen.toRawCheckpointRunPrefix.stopsMarkedWorker seen.rejects.1 directoryCalls callbacks remove write rename bootstrap cache

end RawCheckpointDigestRead

section

variable {admission : CensusOpenAdmissionReports input directory (view.descriptors entry) (view.files entry)}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {release : IO.FS.Handle → heap → heap}

/-- A read-only checkpoint rejection uses the ordinary cache disposal,
unlock, and final close of the exact acquired slot. -/
noncomputable def RawCheckpointRunPrefix.finalizedAttempt {stop : IntegrityCheckpoint → Nat} {cause : IO.Error} {reached : heap}
    (seen : RawCheckpointRunPrefix (admitted := admitted) seed fileCalls stop)
    (rejected : readIntegrityCheckpointSized directory (fileCalls.readOptional directory (directory.file .manifest))
      fileCalls.runSize fileCalls.runPrefix seed.afterPending = .error cause reached)
    (frame : MarkedReadCacheFrame seed seed.afterPending reached)
    (inodes : (view.descriptors reached).inode = admission.reached.inode)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed reached)
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
  beforeCleanup := reached
  disposed := disposal
  recover := fun resolved lock cache =>
    calls.recoverMarkedWithCacheRefs fileCalls directoryCalls callbacks seed.directoryRef seed.activeRef seed.pendingRef
      remove write rename bootstrap resolved cache >>= install resolved lock cache
  cause := cause
  rejected := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, files, _⟩ := seed.installs
    refine disposal.returns _ _ ?_ (frame.files.trans files)
    intro cache
    simp only [Bind.bind, EStateM.bind, seen.stopsMarkedWorker rejected directoryCalls callbacks remove write rename bootstrap]
  workerInodes := inodes
  finalized := finalized

/-- Finalize a digest rejection of the original selected checkpoint. -/
noncomputable def RawCheckpointDigestRead.finalizedAttempt
    (seen : RawCheckpointDigestRead (admitted := admitted) seed fileCalls)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed seen.afterRead)
    (directoryCalls : MarkedDirectoryReadCalls heap stream) (callbacks : AlignedKeeperCacheCallbacks heap)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit) (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap DiskTable)
    (finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner disposal.reached) :
    RawFinalizedOpenAttempt view directory calls init release input entry :=
  seen.toRawCheckpointRunPrefix.finalizedAttempt seen.rejects.1 seen.rejects.2.1 seen.rejects.2.2 disposal
    directoryCalls callbacks remove write rename bootstrap install finalized

end

end Alvoki.Storage.DiskSession
