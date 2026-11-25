import Alvoki.Storage.Disk.NativeRawOpenAdmission

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}

def RawOpenCacheDisposal.filesAfterUnlock (directory : DiskDirectory) (files : LockedFileState FileImage)
    (result : Except IO.Error Unit) : LockedFileState FileImage :=
  match result with
  | .ok () => { files with owners := files.owners.set (directory.file .lock) none }
  | .error _ => files

/-- Report destruction of the initialized cache record when the held
error scope exits. In this route its directory handle is unaliased,
while the lock remains live for the outer handler. -/
structure RawOpenCacheDisposal
    (seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock) (before : heap) where
  dispose : DiskTable.OpenSyncFiles → EStateM IO.Error heap Unit
  afterDisposal : heap
  disposed : ∀ cache, cache.UsesCacheReferences seed.activeRef seed.pendingRef seed.directoryRef →
    dispose cache before = .ok () afterDisposal
  cacheLive : admission.cached ∈ (view.descriptors before).slots
  census : view.descriptors afterDisposal = (view.descriptors before).afterDrops [admission.cached.closeEvent]
  files : view.files afterDisposal = view.files before
  lock : (view.handle afterDisposal admitted.lock).2 = (view.handle admitted.afterFlock admitted.lock).2
  ownerLive : admission.owner ∈ (view.descriptors afterDisposal).slots
  unlockResult : Except IO.Error Unit
  reached : heap
  unlocked : calls.unlock admitted.lock afterDisposal = match unlockResult with
    | .ok () => .ok () reached
    | .error cause => .error cause reached
  returnedCensus : view.descriptors reached = view.descriptors afterDisposal
  returnedFiles : view.files reached = RawOpenCacheDisposal.filesAfterUnlock directory (view.files afterDisposal) unlockResult

namespace RawOpenCacheDisposal

variable {before : heap}

def diagnostic (seen : RawOpenCacheDisposal (admitted := admitted) seed before) (workerError : IO.Error) : IO.Error :=
  match seen.unlockResult with
  | .ok () => workerError
  | .error cause => cause

/-- Interpret the native release of the cache record on error. This
interpreter accounts for the scoped runtime drop before outer unlock. -/
def errorScope (seen : RawOpenCacheDisposal (admitted := admitted) seed before)
    (recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α)
    (resolved : DiskDirectory) (handle : IO.FS.Handle) (cache : DiskTable.OpenSyncFiles) : EStateM IO.Error heap α :=
  tryCatchThe IO.Error (recover resolved handle cache) fun cause => do
    seen.dispose cache
    throw cause

/-- Project the direct unlock return with the cache's directory slot
disposed and the acquired lock still live. -/
def Returned (seen : RawOpenCacheDisposal (admitted := admitted) seed before)
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
      calls.runOpen input init makeCache (seen.errorScope recover) entry = .error (seen.diagnostic cause) seen.reached ∧
      (view.handle seen.afterDisposal admitted.lock).2.1 = admission.owner ∧
      view.descriptors seen.reached = (view.descriptors before).afterDrops [admission.cached.closeEvent] ∧
      admission.cached ∈ (view.descriptors before).slots ∧ admission.owner ∈ (view.descriptors seen.reached).slots ∧
      (view.files seen.reached).image = retry.image ∧
      (TryLockObserves (view.files seen.reached).owners directory (.ok true) ↔ seen.unlockResult = .ok ()) ∧
      (view.files seen.reached).owners (directory.file .lock) = match seen.unlockResult with
        | .ok () => none
        | .error _ => some admission.owner.description

/-- The report and fixed held schedule determine the error at the
outer unlock return. The final lock-handle drop is a later effect. -/
theorem returns (seen : RawOpenCacheDisposal (admitted := admitted) seed before)
    (recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α)
    (cause : IO.Error)
    (failed : ∀ cache, recover directory admitted.lock cache seed.afterPending = .error cause before)
    (held : view.files before = admission.held) : seen.Returned recover cause := by
  obtain ⟨cacheOpen, makeCache, cache, isOpen, source, initialized, uses, _⟩ := seed.installs
  have rawLock := congrArg Prod.fst (seen.lock.trans (congrArg Prod.snd (admitted.sameLock.trans admitted.appendHandle)))
  have files := seen.files.trans held
  refine ⟨cacheOpen, makeCache, cache, isOpen, source, initialized, uses, ?_, rawLock,
    seen.returnedCensus.trans seen.census, seen.cacheLive, seen.returnedCensus.symm ▸ seen.ownerLive, ?_, ?_, ?_⟩
  · rw [admitted.startsHeldWorker init seed initialized (seen.errorScope recover)]
    simp only [errorScope, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, failed cache, EStateM.Backtrackable.restore,
      EStateM.dummyRestore, Bind.bind, EStateM.bind, seen.disposed cache uses, throw, throwThe, MonadExceptOf.throw,
      EStateM.throw, seen.unlocked]
    cases reported : seen.unlockResult with
    | error exception => simp only [reported, diagnostic]
    | ok value =>
      cases value
      simp only [reported, diagnostic]
  · rw [seen.returnedFiles, files]
    cases seen.unlockResult <;> simp [filesAfterUnlock, CensusOpenAdmissionReports.held]
  · rw [seen.returnedFiles, files]
    cases seen.unlockResult <;> simp [filesAfterUnlock, TryLockObserves, CensusOpenAdmissionReports.held, LockOwners.set]
  · rw [seen.returnedFiles, files]
    cases seen.unlockResult <;> simp [filesAfterUnlock, CensusOpenAdmissionReports.held, LockOwners.set]

end RawOpenCacheDisposal

end Alvoki.Storage.DiskSession
