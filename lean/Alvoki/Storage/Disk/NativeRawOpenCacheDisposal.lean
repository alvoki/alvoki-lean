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

def diagnosticAfterUnlock (workerError : IO.Error) : Except IO.Error Unit → IO.Error
  | .ok () => workerError
  | .error cause => cause

def diagnostic (seen : RawOpenCacheDisposal (admitted := admitted) seed before) (workerError : IO.Error) : IO.Error :=
  diagnosticAfterUnlock workerError seen.unlockResult

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
def ReturnedAt (seen : RawOpenCacheDisposal (admitted := admitted) seed before)
    (recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α)
    (cause : IO.Error) (workerImage : FileImage) : Prop :=
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
      (view.files seen.reached).image = workerImage ∧
      (TryLockObserves (view.files seen.reached).owners directory (.ok true) ↔ seen.unlockResult = .ok ()) ∧
      (view.files seen.reached).owners (directory.file .lock) = match seen.unlockResult with
        | .ok () => none
        | .error _ => some admission.owner.description

/-- In the read-only case the worker retains the input image. -/
abbrev Returned (seen : RawOpenCacheDisposal (admitted := admitted) seed before)
    (recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α)
    (cause : IO.Error) : Prop := seen.ReturnedAt recover cause retry.image

/-- The report and fixed held schedule determine the error at the
outer unlock return. The final lock-handle drop is a later effect. -/
theorem returnsAt (seen : RawOpenCacheDisposal (admitted := admitted) seed before)
    (recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α)
    (cause : IO.Error)
    (failed : ∀ cache, recover directory admitted.lock cache seed.afterPending = .error cause before)
    {workerImage : FileImage} (image : (view.files before).image = workerImage)
    (held : (view.files before).owners = admission.held.owners) : seen.ReturnedAt recover cause workerImage := by
  obtain ⟨cacheOpen, makeCache, cache, isOpen, source, initialized, uses, _⟩ := seed.installs
  have rawLock := congrArg Prod.fst (seen.lock.trans (congrArg Prod.snd (admitted.sameLock.trans admitted.appendHandle)))
  have owner := (congrArg LockedFileState.owners seen.files).trans held
  refine ⟨cacheOpen, makeCache, cache, isOpen, source, initialized, uses, ?_, rawLock,
    seen.returnedCensus.trans seen.census, seen.cacheLive, seen.returnedCensus.symm ▸ seen.ownerLive, ?_, ?_, ?_⟩
  · rw [admitted.startsHeldWorker init seed initialized (seen.errorScope recover)]
    simp only [errorScope, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, failed cache, EStateM.Backtrackable.restore,
      EStateM.dummyRestore, Bind.bind, EStateM.bind, seen.disposed cache uses, throw, throwThe, MonadExceptOf.throw,
      EStateM.throw, seen.unlocked]
    cases reported : seen.unlockResult with
    | error exception => simp only [reported, diagnostic, diagnosticAfterUnlock]
    | ok value =>
      cases value
      simp only [reported, diagnostic, diagnosticAfterUnlock]
  · rw [seen.returnedFiles]
    cases seen.unlockResult <;> simp [filesAfterUnlock, seen.files, image]
  · rw [seen.returnedFiles]
    cases seen.unlockResult <;> simp [filesAfterUnlock, TryLockObserves, owner, CensusOpenAdmissionReports.held, LockOwners.set]
  · rw [seen.returnedFiles]
    cases seen.unlockResult <;> simp [filesAfterUnlock, owner, CensusOpenAdmissionReports.held, LockOwners.set]

/-- A failed read-only worker retains the admitted file image. -/
theorem returns (seen : RawOpenCacheDisposal (admitted := admitted) seed before)
    (recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α)
    (cause : IO.Error)
    (failed : ∀ cache, recover directory admitted.lock cache seed.afterPending = .error cause before)
    (held : view.files before = admission.held) : seen.Returned recover cause :=
  seen.returnsAt recover cause failed (by simpa [CensusOpenAdmissionReports.held] using congrArg LockedFileState.image held)
    (congrArg LockedFileState.owners held)

end RawOpenCacheDisposal

end Alvoki.Storage.DiskSession
