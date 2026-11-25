import Alvoki.Storage.Disk.NativeOpenEarlyError
import Alvoki.Storage.Disk.NativeRawOpenAdmission

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {admitted : RawOpenAdmissionReport admission view calls entry}

/-- A held read-only failure reaches local unlock with the same acquired
lock. The report ends at its return, before any later reference drops. -/
structure RawHeldOpenCleanup {census : DescriptorInventory} (cleanup : NativeOpenErrorUnlock admission census)
    (seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock)
    (before : heap := seed.afterPending) where
  reached : heap
  lockFrame : (view.handle before admitted.lock).2 = (view.handle admitted.afterFlock admitted.lock).2
  unlock : calls.unlock admitted.lock before =
    match cleanup.result with
    | .ok () => .ok () reached
    | .error cause => .error cause reached
  image : (view.files reached).image = (view.files before).image
  owners : (view.files reached).owners =
    match cleanup.result with
    | .ok () => (view.files before).owners.set (directory.file .lock) none
    | .error _ => (view.files before).owners
  census : view.descriptors reached = view.descriptors before
  cache : view.cacheAt reached seed.directoryRef seed.activeRef seed.pendingRef =
    view.cacheAt before seed.directoryRef seed.activeRef seed.pendingRef

namespace RawHeldOpenCleanup

variable {census : DescriptorInventory} {cleanup : NativeOpenErrorUnlock admission census} {before : heap}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}

/-- The raw error return and its existing file, lock and cache projection. -/
def Returned (seen : RawHeldOpenCleanup (admitted := admitted) cleanup seed before)
    (recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α)
    (cause : IO.Error) : Prop :=
  ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
      (cache : DiskTable.OpenSyncFiles),
      DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      openSyncFilesWith (init.openDirectory directory.path) init.newRef init.newRef init.newRef makeCache
        admitted.afterFlock = .ok cache seed.afterPending ∧
      cache.UsesCacheReferences seed.activeRef seed.pendingRef seed.directoryRef ∧
      (view.handle before admitted.lock).2.1 = admission.owner ∧
      calls.runOpen input init makeCache recover entry =
        .error (cleanup.diagnostic cause) seen.reached ∧
      (view.descriptors seen.reached, view.files seen.reached) = (census, cleanup.files) ∧
      view.cacheAt seen.reached seed.directoryRef seed.activeRef seed.pendingRef = admission.cache ∧
      (view.files seen.reached).image = retry.image ∧
      (TryLockObserves (view.files seen.reached).owners directory (.ok true) ↔ cleanup.result = .ok ())

/-- The actual open's error handler uses the heap reached by the failed
worker. The local unlock selects the diagnostic and the current owner. -/
theorem returnsErrorAt (seen : RawHeldOpenCleanup (admitted := admitted) cleanup seed before)
    (recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α)
    (cause : IO.Error)
    (rejected : ∀ cache, recover directory admitted.lock cache seed.afterPending = .error cause before)
    (heldFiles : view.files before = admission.held) (heldCensus : view.descriptors before = census)
    (heldCache : view.cacheAt before seed.directoryRef seed.activeRef seed.pendingRef = admission.cache) :
    seen.Returned recover cause := by
  obtain ⟨cacheOpen, makeCache, cache, isOpen, source, initialized, uses, _⟩ := seed.installs
  have opened := admitted.startsHeldWorker init seed initialized recover
  have returned : calls.runOpen input init makeCache recover entry =
      .error (cleanup.diagnostic cause) seen.reached := by
    rw [opened]
    simp only [tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, rejected cache, EStateM.Backtrackable.restore,
      EStateM.dummyRestore, Bind.bind, EStateM.bind, seen.unlock]
    cases result : cleanup.result with
    | ok value =>
      cases value
      simp only [result, NativeOpenErrorUnlock.diagnostic, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
    | error cause => simp only [result, NativeOpenErrorUnlock.diagnostic]
  have reachedFiles : view.files seen.reached = cleanup.files := by
    have image := seen.image.trans (congrArg LockedFileState.image heldFiles)
    have owners : (view.files seen.reached).owners = cleanup.files.owners := by
      have framed := seen.owners
      rw [heldFiles] at framed
      cases result : cleanup.result with
      | ok value =>
        cases value
        simpa only [NativeOpenErrorUnlock.files, CensusOpenAdmissionReports.held, result] using framed
      | error cause => simpa only [NativeOpenErrorUnlock.files, CensusOpenAdmissionReports.held, result] using framed
    exact (LockedFileState.mk.injEq _ _ _ _).mpr ⟨image.trans cleanup.keepsFiles.symm, owners⟩
  have slot := congrArg Prod.fst seen.lockFrame
  rw [admitted.sameLock, admitted.appendHandle] at slot
  exact ⟨cacheOpen, makeCache, cache, isOpen, source, initialized, uses, slot, returned,
    Prod.ext (seen.census.trans heldCensus) reachedFiles, seen.cache.trans heldCache,
    (congrArg LockedFileState.image reachedFiles).trans cleanup.keepsFiles,
    reachedFiles.symm ▸ cleanup.admits⟩

/-- Rejections at the initialized heap take their frames directly from
the same cache allocation. -/
theorem returnsError {cleanup : NativeOpenErrorUnlock admission admission.reached}
    (seen : RawHeldOpenCleanup (admitted := admitted) cleanup seed)
    (recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α)
    (cause : IO.Error)
    (rejected : ∀ cache, recover directory admitted.lock cache seed.afterPending = .error cause seed.afterPending) :
    seen.Returned recover cause := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, cached, files, census, _⟩ := seed.installs
  exact seen.returnsErrorAt recover cause rejected files census cached

end RawHeldOpenCleanup

/-- A non-ENOENT no-follow error stops the optional metadata reader. -/
theorem rawOptionalMetadataError (lookup : EStateM IO.Error heap (Except IO.Error IO.FS.Metadata))
    {before : heap} {cause : IO.Error} (reported : lookup before = .ok (.error cause) before)
    (notMissing : ∀ path message, cause ≠ .noFileOrDirectory path 2 message) :
    optionalMetadataWith lookup before = .error cause before := by
  simp only [optionalMetadataWith, Bind.bind, EStateM.bind, reported]
  rfl

/-- The held source dispatcher runs its late guards before selecting
recovery, and installs only after the selected worker succeeds. -/
def RawOpenAdmissionCallbacks.recoverAndInstall (calls : RawOpenAdmissionCallbacks heap)
    (marked bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap α)
    (directory : DiskDirectory) (lock : IO.FS.Handle) (cache : DiskTable.OpenSyncFiles) : EStateM IO.Error heap α :=
  recoverSegmentedWalWith
    (rejectFlatWalWith directory (optionalMetadataWith (calls.lookup (directory.file .wal))))
    (optionalMetadataWith (calls.lookup (directory.file .walBoundary)))
    (marked directory cache) (bootstrap directory cache) >>= install directory lock cache

/-- The held flat guard allows the marker lookup, whose original error
selects the same local cleanup as the existing projected route. -/
structure RawMarkerRouteFailure (failure : NativeMarkerRouteError admission)
    (seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock)
    extends RawHeldOpenCleanup (admitted := admitted) failure.cleanup seed where
  flat : optionalMetadataWith (calls.lookup (directory.file .wal)) seed.afterPending = .ok none seed.afterPending
  marker : calls.lookup (directory.file .walBoundary) seed.afterPending = .ok (.error failure.cause) seed.afterPending

/-- The original marker diagnostic returns if cleanup unlocks the
acquired handle. A failed unlock returns its own diagnostic and keeps
projected ownership. Neither recovery worker nor the installer runs. -/
theorem RawMarkerRouteFailure.returns {failure : NativeMarkerRouteError admission}
    {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
    (seen : RawMarkerRouteFailure (admitted := admitted) failure seed)
    (marked bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap α) :
    seen.toRawHeldOpenCleanup.Returned (calls.recoverAndInstall marked bootstrap install) failure.cause := by
  have marker := rawOptionalMetadataError _ seen.marker failure.notMissing
  apply seen.toRawHeldOpenCleanup.returnsError
  intro cache
  simp only [RawOpenAdmissionCallbacks.recoverAndInstall, recoverSegmentedWalWith, rejectFlatWalWith, Bind.bind,
    EStateM.bind, seen.flat, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Pure.pure, EStateM.pure, marker]

end Alvoki.Storage.DiskSession
