import Alvoki.Storage.Disk.NativeRawCheckpointDigestError
import Alvoki.Storage.Disk.NativeTemporaryChunkReadFailure

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {fileCalls : MarkedTemporaryReadCalls heap}

/-- The marked route observes a present regular manifest before it
attempts to open that child for the bounded reader. -/
structure RawPresentManifestReadStat
    (seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock)
    (fileCalls : MarkedTemporaryReadCalls heap) where
  flat : optionalMetadataWith (calls.lookup (directory.file .wal)) seed.afterPending = .ok none seed.afterPending
  marker : IO.FS.Metadata
  marked : optionalMetadataWith (calls.lookup (directory.file .walBoundary)) seed.afterPending =
    .ok (some marker) seed.afterPending
  sameLookup : fileCalls.stat = calls.lookup
  observations : CheckpointRunChunkReads
  child : RunChildLookup admission.root "MANIFEST" admission.view
  metadata : IO.FS.Metadata
  regular : metadata.type = .file
  stat : observations.stat (directory.file .manifest) = .ok (metadata, admission.view.modelObject child.child)
  statRaw : calls.lookup (directory.file .manifest) seed.afterPending =
    .ok ((observations.stat (directory.file .manifest)).map Prod.fst) seed.afterPending
namespace RawPresentManifestReadStat

variable (seen : RawPresentManifestReadStat (admitted := admitted) seed fileCalls)

theorem readEffects :
    fileCalls.readOptional directory (directory.file .manifest) seed.afterPending =
      ((fileCalls.readWith (directory.file .manifest) fun file =>
        readIntegrityManifestPrefixWith (fileCalls.readChunk file) seen.metadata.byteSize.toNat) >>= fun bytes => pure (some bytes))
        seed.afterPending := by
  have stat : fileCalls.stat (directory.file .manifest) seed.afterPending = .ok (.ok seen.metadata) seed.afterPending := by
    simpa only [seen.sameLookup, seen.stat, Except.map] using seen.statRaw
  exact fileCalls.readOptionalManifest_effects directory stat seen.regular

/-- The marked worker passes a checkpoint read error through before
the marker payload, listing or repairs. -/
theorem stopsMarkedWorker (report : RawPresentManifestReadStat (admitted := admitted) seed fileCalls)
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
    reopenMarkedBoundedWithCachedExtents, prepareBoundedMarkedFromReaders, Bind.bind, EStateM.bind, report.flat, report.marked,
    Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte, Pure.pure, EStateM.pure, rejected]

end RawPresentManifestReadStat

/-- The physical manifest header returns a positive short chunk and
the following request fails. -/
structure RawManifestHeaderChunkError
    (seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock)
    (fileCalls : MarkedTemporaryReadCalls heap)
    extends RawPresentManifestReadStat (admitted := admitted) seed fileCalls where
  read : RawTemporaryChunkReadFailure seed fileCalls (directory.file .manifest) child (min 48 metadata.byteSize.toNat)
    seed.afterPending
  bound : retry.image.directory.active.manifest = some read.bytes
  contents : observations.objectBytes (admission.view.modelObject child.child) = some read.bytes
  extent : metadata.byteSize.toNat = read.bytes.size

namespace RawManifestHeaderChunkError

variable (seen : RawManifestHeaderChunkError (admitted := admitted) seed fileCalls)

/-- The failing remainder request is part of header acquisition.
The same short bytes came from the selected manifest's opened inode. -/
structure Released : Prop where
  returned : fileCalls.readOptional directory (directory.file .manifest) seed.afterPending =
    .error seen.read.cause seen.read.reached
  custody : seen.read.Released
  selectedBytes : retry.image.directory.active.manifest = some seen.read.bytes ∧
    seen.observations.objectBytes (admission.view.modelObject seen.child.child) = some seen.read.bytes ∧
    seen.metadata.byteSize.toNat = seen.read.bytes.size
  prefixBytes : seen.read.chunk = seen.read.bytes.extract 0 seen.read.chunk.size

theorem releasesSelected : seen.Released := by
  let raw := seen.read
  have header := readExactPrefixWith_shortThenError (IO.userError "integrity manifest extent changed while reading")
    (fileCalls.readChunk raw.handle) raw.positive raw.short raw.first raw.second
  have failed := readIntegrityManifestPrefixWith_headerError (fileCalls.readChunk raw.handle) seen.metadata.byteSize.toNat header
  have scopedError := fileCalls.readWith_error (directory.file .manifest)
    (fun file => readIntegrityManifestPrefixWith (fileCalls.readChunk file) seen.metadata.byteSize.toNat) raw.openRaw failed
  rw [raw.release] at scopedError
  refine ⟨?_, raw.releases, ⟨seen.bound, seen.contents, seen.extent⟩, raw.firstBytes⟩
  rw [seen.toRawPresentManifestReadStat.readEffects]
  simp only [Bind.bind, EStateM.bind, scopedError]
  rfl

theorem rejectsCheckpoint :
    readIntegrityCheckpointSized directory (fileCalls.readOptional directory (directory.file .manifest))
      fileCalls.runSize fileCalls.runPrefix seed.afterPending = .error seen.read.cause seen.read.reached := by
  simp only [readIntegrityCheckpointSized, Bind.bind, EStateM.bind, seen.releasesSelected.returned]

/-- Failed header acquisition skips manifest decoding, selected run
metadata and payloads, the marker payload, listing, and repair. -/
theorem stopsMarkedWorker
    (directoryCalls : MarkedDirectoryReadCalls heap stream) (callbacks : AlignedKeeperCacheCallbacks heap)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit) (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (cache : DiskTable.OpenSyncFiles) :
    calls.recoverMarkedWithCacheRefs fileCalls directoryCalls callbacks seed.directoryRef seed.activeRef seed.pendingRef
      remove write rename bootstrap directory cache seed.afterPending = .error seen.read.cause seen.read.reached :=
  seen.toRawPresentManifestReadStat.stopsMarkedWorker seen.rejectsCheckpoint directoryCalls callbacks remove write rename bootstrap cache

end RawManifestHeaderChunkError

section

variable {admission : CensusOpenAdmissionReports input directory (view.descriptors entry) (view.files entry)}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {release : IO.FS.Handle → heap → heap}

/-- The same reached manifest error follows the admitted cache and lock
drops, with the exact reported choice of caller-visible diagnostic. -/
noncomputable def RawManifestHeaderChunkError.finalizedAttempt
    (seen : RawManifestHeaderChunkError (admitted := admitted) seed fileCalls)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed seen.read.reached)
    (directoryCalls : MarkedDirectoryReadCalls heap stream) (callbacks : AlignedKeeperCacheCallbacks heap)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit) (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap DiskTable)
    (finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner disposal.reached) :
    RawFinalizedOpenAttempt view directory calls init release input entry :=
  RawFinalizedOpenAttempt.ofMarkedRejection seen.releasesSelected.custody.frame (by
      rw [seen.releasesSelected.custody.census, seed.pendingSlots, seed.activeSlots, seed.directorySlots, seed.openedSlots]
      rfl)
    disposal directoryCalls callbacks remove write rename bootstrap install
    (seen.stopsMarkedWorker directoryCalls callbacks remove write rename bootstrap) finalized

end

end Alvoki.Storage.DiskSession
