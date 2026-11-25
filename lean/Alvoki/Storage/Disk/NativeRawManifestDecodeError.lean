import Alvoki.Storage.Disk.NativeManifestDecodeError
import Alvoki.Storage.Disk.NativeMarkedTableOpen
import Alvoki.Storage.Disk.NativeRawMarkerRouteError

namespace Alvoki.Storage.DiskSession

open System Manifest WalSegmentRepair

variable {heap : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {admitted : RawOpenAdmissionReport admission view calls entry}

/-- The malformed selected manifest is acquired by the original bounded
reader. Release of that same temporary handle supplies the decoder's heap. -/
structure RawManifestDecodeRead (fault : NativeManifestDecodeError admission)
    (seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock)
    (fileCalls : MarkedTemporaryReadCalls heap) where
  flat : optionalMetadataWith (calls.lookup (directory.file .wal)) seed.afterPending = .ok none seed.afterPending
  marker : calls.lookup (directory.file .walBoundary) seed.afterPending = .ok (.ok fault.marker) seed.afterPending
  sameLookup : fileCalls.stat = calls.lookup
  stat : calls.lookup (directory.file .manifest) seed.afterPending =
    .ok ((fault.reads.stat (directory.file .manifest)).map Prod.fst) seed.afterPending
  file : IO.FS.Handle
  opened : heap
  finished : heap
  closed : heap
  openedRaw : fileCalls.openRead (directory.file .manifest) seed.afterPending = .ok file opened
  sameOpened : fault.reads.openRead (directory.file .manifest) = .ok (view.handle opened file)
  readRaw : readIntegrityManifestPrefixWith (fileCalls.readChunk file) fault.manifest.calls.metadata.byteSize.toNat opened =
    .ok (fault.bytes.extract 0 (IntegrityCheckpoint.acquisitionSize fault.bytes)) finished
  sameSlot : (view.handle finished file).2.1 = (view.handle opened file).2.1
  releasedRaw : fileCalls.release file finished = .ok () closed
  census : view.descriptors closed = (view.handle opened file).1.afterDrops (fault.release (directory.file .manifest))
  frame : MarkedReadCacheFrame seed seed.afterPending closed

namespace RawManifestDecodeRead

variable {fault : NativeManifestDecodeError admission}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {fileCalls : MarkedTemporaryReadCalls heap}

theorem readsSelected (seen : RawManifestDecodeRead (admitted := admitted) fault seed fileCalls) :
    fileCalls.readOptional directory (directory.file .manifest) seed.afterPending =
      .ok (some (fault.bytes.extract 0 (IntegrityCheckpoint.acquisitionSize fault.bytes))) seen.closed ∧
    view.handle seen.opened seen.file = (fault.manifest.calls.inventory, fault.manifest.calls.slot, 0) ∧
    (view.handle seen.finished seen.file).2.1 = fault.manifest.calls.slot ∧
    (view.handle seen.opened seen.file).1.inode (view.handle seen.opened seen.file).2.1.description =
      admission.view.modelObject fault.manifest.object ∧
    view.descriptors seen.closed = fault.afterRead ∧
    (view.descriptors seen.closed).references fault.manifest.calls.slot.description = [] := by
  have opened := Except.ok.inj (seen.sameOpened.symm.trans fault.manifest.calls.opened)
  have census : view.descriptors seen.closed = fault.afterRead := by
    rw [seen.census, opened]
    exact fault.custody.closes.1
  have stat : fileCalls.stat (directory.file .manifest) seed.afterPending =
      .ok (.ok fault.manifest.calls.metadata) seed.afterPending := by
    simp only [seen.sameLookup, seen.stat, fault.manifest.calls.stat, Except.map]
  exact ⟨fileCalls.readOptionalManifest directory stat fault.manifest.calls.regular (by
      simp only [MarkedTemporaryReadCalls.readWith, seen.openedRaw, seen.readRaw, SyncHandleRouting.dataErrorDropState,
        seen.releasedRaw]), opened,
    seen.sameSlot.trans (congrArg (fun handle : CheckpointOpenHandle => handle.2.1) opened),
    opened.symm ▸ fault.readsManifest.2.2.1, census, census.symm ▸ fault.readsManifest.2.2.2.2⟩

/-- The source marked worker returns the exact decoder error after the
temporary release, before every run, marker-payload or repair callback. -/
theorem stopsBeforeWal {stream : Type}
    (seen : RawManifestDecodeRead (admitted := admitted) fault seed fileCalls)
    (directoryCalls : MarkedDirectoryReadCalls heap stream) (callbacks : AlignedKeeperCacheCallbacks heap)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (cache : DiskTable.OpenSyncFiles) :
    calls.recoverMarkedWithCacheRefs fileCalls directoryCalls callbacks seed.directoryRef seed.activeRef seed.pendingRef
      remove write rename bootstrap directory cache seed.afterPending = .error (IO.userError fault.cause) seen.closed := by
  have marker : optionalMetadataWith (calls.lookup (directory.file .walBoundary)) seed.afterPending =
      .ok (some fault.marker) seed.afterPending := by
    simp only [optionalMetadataWith, Bind.bind, EStateM.bind, seen.marker, Pure.pure, EStateM.pure]
  simp only [RawOpenAdmissionCallbacks.recoverMarkedWithCacheRefs, recoverSegmentedWalWith, rejectFlatWalWith,
    reopenMarkedBoundedWithCachedExtents, prepareBoundedMarkedFromReaders, readIntegrityCheckpointSized,
    Bind.bind, EStateM.bind, seen.flat, marker, Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
    ↓reduceIte, Pure.pure, EStateM.pure, seen.readsSelected.1, IntegrityCheckpoint.decode_acquisitionPrefix,
    fault.invalid, Except.mapError, liftExcept, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

end RawManifestDecodeRead

variable {fault : NativeManifestDecodeError admission}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {fileCalls : MarkedTemporaryReadCalls heap}

/-- The earlier error view keeps the reported synchronization cache
live through local unlock. The decoder itself needs only its read report. -/
structure RawManifestDecodeFailure (fault : NativeManifestDecodeError admission)
    (seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock)
    (fileCalls : MarkedTemporaryReadCalls heap)
    extends RawManifestDecodeRead (admitted := admitted) fault seed fileCalls where
  cleanup : NativeOpenErrorUnlock admission fault.afterRead
  unlock : RawHeldOpenCleanup (admitted := admitted) cleanup seed closed

/-- The acquired lock is unlocked at that exact post-release heap. The
open reports the decoder error or the error from unlocking the same lock. -/
theorem RawManifestDecodeFailure.returns {stream α : Type} (seen : RawManifestDecodeFailure (admitted := admitted) fault seed fileCalls)
    (directoryCalls : MarkedDirectoryReadCalls heap stream) (callbacks : AlignedKeeperCacheCallbacks heap)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap α) :
    let recover := fun resolved lock cache =>
      calls.recoverMarkedWithCacheRefs fileCalls directoryCalls callbacks seed.directoryRef seed.activeRef seed.pendingRef
        remove write rename bootstrap resolved cache >>= install resolved lock cache
    seen.unlock.Returned recover (IO.userError fault.cause) ∧
    (view.files seen.unlock.reached).image.directory.active.manifest = some fault.bytes ∧
    (view.descriptors seen.unlock.reached).references fault.manifest.calls.slot.description = [] := by
  intro recover
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, cache, files, _⟩ := seed.installs
  obtain ⟨_, _, _, _, census, released⟩ := seen.toRawManifestDecodeRead.readsSelected
  have returned := seen.unlock.returnsErrorAt recover (IO.userError fault.cause) (fun rawCache => by
    simp only [recover, Bind.bind, EStateM.bind,
      seen.toRawManifestDecodeRead.stopsBeforeWal directoryCalls callbacks remove write rename bootstrap])
    (seen.frame.files.trans files) census (seen.frame.keepsInitialCache.trans cache)
  refine ⟨returned, ?_, seen.unlock.census.symm ▸ released⟩
  have image := seen.unlock.image.trans (congrArg LockedFileState.image (seen.frame.files.trans files))
  exact (congrArg (fun image => image.directory.active.manifest) image).trans fault.selected

end Alvoki.Storage.DiskSession
