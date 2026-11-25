import Alvoki.Storage.Disk.NativeOpenEarlyError
import Alvoki.Storage.Disk.NativeRawOpenAdmission

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {admitted : RawOpenAdmissionReport admission view calls entry}

/-- The marker lookup and local unlock run with the same raw lock and
initialized cache. The report ends at the unlock return. Later reference
drops have their own observations in the rejected-open lineage. -/
structure RawMarkerRouteFailure (failure : NativeMarkerRouteError admission)
    (seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock) where
  reached : heap
  flat : optionalMetadataWith (calls.lookup (directory.file .wal)) seed.afterPending = .ok none seed.afterPending
  marker : calls.lookup (directory.file .walBoundary) seed.afterPending = .ok (.error failure.cause) seed.afterPending
  lockFrame : (view.handle seed.afterPending admitted.lock).2 = (view.handle admitted.afterFlock admitted.lock).2
  unlock : calls.unlock admitted.lock seed.afterPending =
    match failure.cleanup.result with
    | .ok () => .ok () reached
    | .error cause => .error cause reached
  image : (view.files reached).image = (view.files seed.afterPending).image
  owners : (view.files reached).owners =
    match failure.cleanup.result with
    | .ok () => (view.files seed.afterPending).owners.set (directory.file .lock) none
    | .error _ => (view.files seed.afterPending).owners
  census : view.descriptors reached = view.descriptors seed.afterPending
  cache : view.cacheAt reached seed.directoryRef seed.activeRef seed.pendingRef =
    view.cacheAt seed.afterPending seed.directoryRef seed.activeRef seed.pendingRef

namespace RawMarkerRouteFailure

variable {failure : NativeMarkerRouteError admission}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}

/-- The original marker diagnostic returns if cleanup unlocks the
acquired handle. A failed unlock returns its own diagnostic and keeps
the projected ownership. Neither recovery worker nor the installer runs. -/
theorem returns
    (seen : RawMarkerRouteFailure (admitted := admitted) failure seed)
    (marked bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap α) :
    let recover := fun (resolved : DiskDirectory) (lock : IO.FS.Handle) (cache : DiskTable.OpenSyncFiles) =>
      recoverSegmentedWalWith
        (rejectFlatWalWith resolved (optionalMetadataWith (calls.lookup (resolved.file .wal))))
        (optionalMetadataWith (calls.lookup (resolved.file .walBoundary)))
        (marked resolved cache) (bootstrap resolved cache) >>= install resolved lock cache
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
      (view.handle seed.afterPending admitted.lock).2.1 = admission.owner ∧
      calls.runOpen input init makeCache recover entry =
        .error (failure.cleanup.diagnostic failure.cause) seen.reached ∧
      (view.descriptors seen.reached, view.files seen.reached) = (admission.reached, failure.cleanup.files) ∧
      view.cacheAt seen.reached seed.directoryRef seed.activeRef seed.pendingRef = admission.cache ∧
      (view.files seen.reached).image = retry.image ∧
      (TryLockObserves (view.files seen.reached).owners directory (.ok true) ↔ failure.cleanup.result = .ok ()) := by
  intro recover
  obtain ⟨cacheOpen, makeCache, cache, isOpen, source, initialized, uses, _, _, _, _, initialCache,
    heldFiles, heldCensus, _, _, _, _⟩ := seed.installs
  have optionalMarker : optionalMetadataWith (calls.lookup (directory.file .walBoundary)) seed.afterPending =
      .error failure.cause seed.afterPending := by
    have notMissing := failure.notMissing
    simp only [optionalMetadataWith, Bind.bind, EStateM.bind, seen.marker]
    rfl
  have rejected : recover directory admitted.lock cache seed.afterPending = .error failure.cause seed.afterPending := by
    simp only [recover, recoverSegmentedWalWith, rejectFlatWalWith, Bind.bind, EStateM.bind, seen.flat,
      Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Pure.pure, EStateM.pure, optionalMarker]
  have opened := admitted.startsHeldWorker init seed initialized recover
  have returned : calls.runOpen input init makeCache recover entry =
      .error (failure.cleanup.diagnostic failure.cause) seen.reached := by
    rw [opened]
    simp only [tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, rejected, EStateM.Backtrackable.restore,
      EStateM.dummyRestore, Bind.bind, EStateM.bind, seen.unlock]
    cases result : failure.cleanup.result with
    | ok value =>
      cases value
      simp only [result, NativeOpenErrorUnlock.diagnostic, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
    | error cause => simp only [result, NativeOpenErrorUnlock.diagnostic]
  have reachedFiles : view.files seen.reached = failure.cleanup.files := by
    have image := seen.image.trans (congrArg LockedFileState.image heldFiles)
    have owners : (view.files seen.reached).owners = failure.cleanup.files.owners := by
      have held : view.files seed.afterPending = admission.held := heldFiles
      have framed := seen.owners
      rw [held] at framed
      cases result : failure.cleanup.result with
      | ok value =>
        cases value
        simpa only [NativeOpenErrorUnlock.files, CensusOpenAdmissionReports.held, result] using framed
      | error cause => simpa only [NativeOpenErrorUnlock.files, CensusOpenAdmissionReports.held, result] using framed
    exact (LockedFileState.mk.injEq _ _ _ _).mpr ⟨image.trans failure.cleanup.keepsFiles.symm, owners⟩
  have slot := congrArg Prod.fst seen.lockFrame
  rw [admitted.sameLock, admitted.appendHandle] at slot
  exact ⟨cacheOpen, makeCache, cache, isOpen, source, initialized, uses, slot, returned,
    Prod.ext (seen.census.trans heldCensus) reachedFiles, seen.cache.trans initialCache,
    (congrArg LockedFileState.image reachedFiles).trans failure.cleanup.keepsFiles,
    reachedFiles.symm ▸ failure.cleanup.admits⟩

end RawMarkerRouteFailure

end Alvoki.Storage.DiskSession
