import Alvoki.Storage.Disk.NativeOpenCacheReferences
import Alvoki.Storage.Disk.LockCensusOpenAdmission

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting

structure RawOpenAdmissionCallbacks (heap : Type) where
  realPath : FilePath → EStateM IO.Error heap FilePath
  lookup : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata)
  openAppend : FilePath → EStateM IO.Error heap IO.FS.Handle
  flock : IO.FS.Handle → EStateM IO.Error heap Bool
  unlock : IO.FS.Handle → EStateM IO.Error heap Unit

variable {heap image : Type} {input : FilePath} {directory : DiskDirectory} {initial : DescriptorInventory}
  {files : LockedFileState image}

/-- Report a successful held admission at the same primitive calls as
the projected census. The raw append handle is the handle on which
the exclusive lock is acquired. -/
structure RawOpenAdmissionReport (admission : CensusOpenAdmissionReports input directory initial files)
    (view : OpenCloseHeapView heap image) (calls : RawOpenAdmissionCallbacks heap) (entry : heap) where
  lock : IO.FS.Handle
  afterAppend : heap
  afterFlock : heap
  entryFiles : view.files entry = files
  entryCensus : view.descriptors entry = initial
  resolved : calls.realPath input entry = .ok directory.path entry
  flat : optionalMetadataWith (calls.lookup (directory.file .wal)) entry = .ok none entry
  lockProbe : optionalMetadataWith (calls.lookup (directory.file .lock)) entry = .ok admission.lockMetadata entry
  appended : calls.openAppend (directory.file .lock) entry = .ok lock afterAppend
  appendFiles : view.files afterAppend = files
  appendCensus : view.descriptors afterAppend = initial.insert admission.owner admission.free
  appendHandle : view.handle afterAppend lock = (initial.insert admission.owner admission.free, admission.owner, 0)
  acquired : calls.flock lock afterAppend = .ok true afterFlock
  lockedFiles : view.files afterFlock = admission.held
  lockedCensus : view.descriptors afterFlock = view.descriptors afterAppend
  sameLock : view.handle afterFlock lock = view.handle afterAppend lock

variable {admission : CensusOpenAdmissionReports input directory initial files}
  {view : OpenCloseHeapView heap image} {calls : RawOpenAdmissionCallbacks heap} {entry : heap}

/-- Run the shared native admission, then the raw cache initialization
from the lock acquisition's reached heap. Use the exact opened lock
and synchronization record for the held continuation, with the native
unlock-on-error handler still attached. -/
theorem RawOpenAdmissionReport.admitsWithCache
    (seen : RawOpenAdmissionReport admission view calls entry)
    (init : OpenSyncCacheCallbacks heap)
    (seed : OpenSyncCacheAllocations admission.opened view init seen.afterFlock) :
    ∃ (cache : DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
      (cacheOpen : IO DiskTable.OpenSyncFiles),
      DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      cache.UsesCacheReferences seed.activeRef seed.pendingRef seed.directoryRef ∧ cache.AtDirectory directory.path ∧
      view.handle seen.afterFlock seen.lock = (initial.insert admission.owner admission.free, admission.owner, 0) ∧
      view.files seen.afterFlock = admission.held ∧ view.descriptors seen.afterFlock = initial.insert admission.owner admission.free ∧
      view.cacheAt seed.afterPending seed.directoryRef seed.activeRef seed.pendingRef = admission.cache ∧
      (view.descriptors seed.afterPending, view.files seed.afterPending) = (admission.reached, admission.held) ∧
      ∀ {α : Type} (recovery : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α),
        DiskTable.withOpenAdmission input calls.realPath calls.lookup calls.openAppend
          (fun resolved lock =>
            openWithLock (calls.flock lock) (fun _ => IO.userError s!"database already open: {resolved.path}")
              (fun _ => calls.unlock lock) fun _ => do
                let opened ← openSyncFilesWith (init.openDirectory resolved.path) init.newRef init.newRef init.newRef makeCache
                recovery resolved lock opened) entry =
          (tryCatchThe IO.Error (recovery directory seen.lock cache) fun cause => do
            calls.unlock seen.lock
            throw cause) seed.afterPending := by
  obtain ⟨action, makeCache, cache, isOpen, source, initialized, references, atPath, _, _, _, captured, files, census,
    _, _, _, _⟩ := seed.installs
  refine ⟨cache, makeCache, action, isOpen, source, references, atPath, seen.sameLock.trans seen.appendHandle,
    seen.lockedFiles, seen.lockedCensus.trans seen.appendCensus, captured, Prod.ext census files, ?_⟩
  intro α recovery
  rw [DiskTable.withOpenAdmission_lockOpen calls.realPath calls.lookup calls.openAppend _
    seen.resolved seen.flat seen.lockProbe admission.safe, seen.appended]
  simp only [openWithLock, Bind.bind, EStateM.bind, seen.acquired, ↓reduceIte, initialized,
    MonadExcept.tryCatch, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch]

/-- Run the shared native admission, repeat the flat-WAL guard under
the acquired lock, then initialize the cache from that reached heap. Use the exact opened lock
and synchronization record for the held continuation, with the native
unlock-on-error handler still attached. -/
theorem RawOpenAdmissionReport.admitsWithCacheAfterFlatGuard
    (seen : RawOpenAdmissionReport admission view calls entry)
    (init : OpenSyncCacheCallbacks heap)
    (seed : OpenSyncCacheAllocations admission.opened view init seen.afterFlock)
    (flatAfterLock : optionalMetadataWith (calls.lookup (directory.file .wal)) seen.afterFlock =
      .ok none seen.afterFlock) :
    ∃ (cache : DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
      (cacheOpen : IO DiskTable.OpenSyncFiles),
      DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      cache.UsesCacheReferences seed.activeRef seed.pendingRef seed.directoryRef ∧ cache.AtDirectory directory.path ∧
      view.handle seen.afterFlock seen.lock = (initial.insert admission.owner admission.free, admission.owner, 0) ∧
      view.files seen.afterFlock = admission.held ∧ view.descriptors seen.afterFlock = initial.insert admission.owner admission.free ∧
      view.cacheAt seed.afterPending seed.directoryRef seed.activeRef seed.pendingRef = admission.cache ∧
      (view.descriptors seed.afterPending, view.files seed.afterPending) = (admission.reached, admission.held) ∧
      ∀ {α : Type} (recovery : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α),
        DiskTable.withOpenAdmission input calls.realPath calls.lookup calls.openAppend
          (fun resolved lock =>
            openWithLock (calls.flock lock) (fun _ => IO.userError s!"database already open: {resolved.path}")
              (fun _ => calls.unlock lock) fun _ => do
                rejectFlatWalWith resolved (optionalMetadataWith (calls.lookup (resolved.file .wal)))
                let opened ← openSyncFilesWith (init.openDirectory resolved.path) init.newRef init.newRef init.newRef makeCache
                recovery resolved lock opened) entry =
          (tryCatchThe IO.Error (recovery directory seen.lock cache) fun cause => do
            calls.unlock seen.lock
            throw cause) seed.afterPending := by
  obtain ⟨action, makeCache, cache, isOpen, source, initialized, references, atPath, _, _, _, captured, files, census,
    _, _, _, _⟩ := seed.installs
  refine ⟨cache, makeCache, action, isOpen, source, references, atPath, seen.sameLock.trans seen.appendHandle,
    seen.lockedFiles, seen.lockedCensus.trans seen.appendCensus, captured, Prod.ext census files, ?_⟩
  intro α recovery
  rw [DiskTable.withOpenAdmission_lockOpen calls.realPath calls.lookup calls.openAppend _
    seen.resolved seen.flat seen.lockProbe admission.safe, seen.appended]
  have guardPassed : rejectFlatWalWith directory (optionalMetadataWith (calls.lookup (directory.file .wal)))
      seen.afterFlock = .ok () seen.afterFlock := by
    simp [rejectFlatWalWith, Bind.bind, EStateM.bind, flatAfterLock, Pure.pure, EStateM.pure]
  simp only [openWithLock, Bind.bind, EStateM.bind, seen.acquired, ↓reduceIte, guardPassed, initialized,
    MonadExcept.tryCatch, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch]

end Alvoki.Storage.DiskSession
