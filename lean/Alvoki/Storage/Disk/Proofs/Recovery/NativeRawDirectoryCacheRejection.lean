import Alvoki.Storage.Disk.Proofs.Recovery.NativeCacheOpenRejection
import Alvoki.Storage.Disk.NativeRawOpenPrefixReturn

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap : Type} {input : FilePath} {directory : DiskDirectory} {entry : heap}
  {calls : RawOpenAdmissionCallbacks heap} {init : OpenSyncCacheCallbacks heap}
  {lock : IO.FS.Handle} {afterAppend afterFlock afterOpen : heap}

/-- A failed directory open reaches cleanup before allocating any cache
reference. The exact reached heap enters unlock on the acquired handle. -/
theorem RawOpenAdmissionCallbacks.returnsDirectoryOpenError
    {cause : IO.Error}
    (appended : calls.beforeFlock input entry = .ok (directory, lock) afterAppend)
    (acquired : calls.flock lock afterAppend = .ok true afterFlock)
    (failed : init.openDirectory directory.path afterFlock = .error cause afterOpen)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
    (recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α) :
    calls.runOpen input init makeCache recover entry =
      match calls.unlock lock afterOpen with
      | .ok () reached => .error cause reached
      | .error cleanup reached => .error cleanup reached := by
  simp only [calls.runsAfterPrefix, appended, openWithLock, Bind.bind, EStateM.bind, acquired,
    ↓reduceIte, openSyncFilesWith, failed, MonadExcept.tryCatch, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch,
    EStateM.Backtrackable.restore, EStateM.dummyRestore, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  cases calls.unlock lock afterOpen with
  | ok value reached => cases value; rfl
  | error cleanup reached => rfl

/-- Report the attempted read-only cache open on the same canonical lock
handle as the public admission. The reached census includes any raw slot
created before a handle-wrapping error, and excludes later disposal. -/
structure RawDirectoryCacheRejection {before : CensusOpenState}
    (observed : NativeCacheOpenRejection input directory before) (view : OpenCloseHeapView heap FileImage)
    (calls : RawOpenAdmissionCallbacks heap) (init : OpenSyncCacheCallbacks heap) (entry : heap) where
  lock : IO.FS.Handle
  afterAppend : heap
  afterFlock : heap
  afterOpen : heap
  reached : heap
  appended : calls.beforeFlock input entry = .ok (directory, lock) afterAppend
  entryProjection : (view.descriptors entry, view.files entry) = before
  lockAtAppend : view.handle afterAppend lock = (observed.failure.initial, observed.failure.owner, 0)
  acquired : calls.flock lock afterAppend = .ok true afterFlock
  heldFiles : view.files afterFlock = ⟨before.2.image,
    before.2.owners.set (directory.file .lock) (some observed.failure.owner.description)⟩
  heldCensus : view.descriptors afterFlock = observed.failure.initial
  failed : init.openDirectory directory.path afterFlock = .error observed.failure.cause afterOpen
  lockAtCleanup : (view.handle afterOpen lock).2 = (view.handle afterAppend lock).2
  openFiles : view.files afterOpen = view.files afterFlock
  openCensus : view.descriptors afterOpen = observed.failure.reached
  unlock : calls.unlock lock afterOpen = match observed.failure.unlock with
    | .success => .ok () reached
    | .failure cause _ => .error cause reached
  census : view.descriptors reached = view.descriptors afterOpen
  image : (view.files reached).image = (view.files afterOpen).image
  owners : (view.files reached).owners = match observed.failure.unlock with
    | .success => (view.files afterOpen).owners.set (directory.file .lock) none
    | .failure _ _ => (view.files afterOpen).owners

namespace RawDirectoryCacheRejection

variable {before : CensusOpenState} {view : OpenCloseHeapView heap FileImage}
  {observed : NativeCacheOpenRejection input directory before}

/-- The actual cache initializer uses the same lock, and its directory
failure never reaches recovery. The raw return projects to the existing
retry state's exact error, owner, file image and descriptor census. -/
theorem returns (seen : RawDirectoryCacheRejection observed view calls init entry)
    (recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α) :
    ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles),
      DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      calls.runOpen input init makeCache recover entry =
        .error observed.failure.projectedFailure.error seen.reached ∧
      (view.descriptors seen.reached, view.files seen.reached) =
        (observed.failure.reached, observed.failure.projectedFailure.after) ∧
      (view.handle seen.afterOpen seen.lock).2.1 = observed.failure.owner ∧
      (view.descriptors seen.reached).references observed.failure.owner.description =
        (view.descriptors seen.afterFlock).references observed.failure.owner.description := by
  obtain ⟨cacheOpen, makeCache, isOpen, source, _⟩ := DiskTable.openSyncCacheReferences directory.path
  refine ⟨cacheOpen, makeCache, isOpen, source, ?_, Prod.ext (seen.census.trans seen.openCensus) ?_, ?_, ?_⟩
  · rw [calls.returnsDirectoryOpenError seen.appended seen.acquired seen.failed makeCache recover, seen.unlock]
    cases reported : observed.failure.unlock <;>
      simp [DirectoryCacheOpenErrorReports.projectedFailure, DirectoryCacheOpenErrorReports.nativeFailure,
        CachedOpenPrefixFailure.projectFiles, CachedOpenPrefixFailure.error, reported]
  · apply (LockedFileState.mk.injEq _ _ _ _).mpr
    have held := seen.openFiles.trans seen.heldFiles
    have image := seen.image.trans (congrArg LockedFileState.image held)
    have owners := seen.owners
    rw [held] at owners
    refine ⟨image, ?_⟩
    rw [owners]
    cases reported : observed.failure.unlock
    · funext path
      by_cases same : path = directory.file .lock <;>
        simp [DirectoryCacheOpenErrorReports.projectedFailure, DirectoryCacheOpenErrorReports.nativeFailure,
          CachedOpenPrefixFailure.projectFiles, LockOwners.set, reported, same]
    · simp [DirectoryCacheOpenErrorReports.projectedFailure, DirectoryCacheOpenErrorReports.nativeFailure,
        CachedOpenPrefixFailure.projectFiles, reported]
  · have slot := congrArg Prod.fst seen.lockAtCleanup
    simpa only [seen.lockAtAppend] using slot
  · rw [seen.census, seen.openCensus, seen.heldCensus]
    exact observed.failure.census.lockReferences observed.failure.lockLive

/-- The actual reached file projection is the next retry position. -/
theorem continuesRetry (seen : RawDirectoryCacheRejection observed view calls init entry)
    (recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α)
    {initial : LockedFileState FileImage} {admits : Target → Prop}
    (prior : BoundedReopenTrace directory admits initial (view.files entry)) :
    BoundedReopenTrace directory admits initial (view.files seen.reached) := by
  obtain ⟨_, _, _, _, _, reached, _, _⟩ := seen.returns recover
  have entryFiles : view.files entry = before.2 := congrArg Prod.snd seen.entryProjection
  have reachedFiles : view.files seen.reached = observed.failure.projectedFailure.after := congrArg Prod.snd reached
  rw [reachedFiles]
  rw [entryFiles] at prior
  exact .cachedPrefixFailed prior observed.failure.projectedFailure rfl

end RawDirectoryCacheRejection
end Alvoki.Storage.DiskSession
