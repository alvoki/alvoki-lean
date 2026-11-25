import Alvoki.Storage.Disk.NativeRawFinalizedOpenError
import Alvoki.Storage.Disk.NativeRawOpenReturn

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap : Type} {view : OpenCloseHeapView heap FileImage} {directory : DiskDirectory}
  {calls : RawOpenAdmissionCallbacks heap} {init : OpenSyncCacheCallbacks heap}
  {release : IO.FS.Handle → heap → heap} {input : FilePath} {entry : heap}

/-- A held read-only rejection whose caller sees the finalized result.
The entry census and files are those at this actual raw heap. -/
structure RawFinalizedOpenAttempt (view : OpenCloseHeapView heap FileImage) (directory : DiskDirectory)
    (calls : RawOpenAdmissionCallbacks heap) (init : OpenSyncCacheCallbacks heap)
    (release : IO.FS.Handle → heap → heap) (input : FilePath) (entry : heap) where
  admission : CensusOpenAdmissionReports input directory (view.descriptors entry) (view.files entry)
  admitted : RawOpenAdmissionReport admission view calls entry
  seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock
  beforeCleanup : heap
  disposed : RawOpenCacheDisposal (admitted := admitted) seed beforeCleanup
  recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap DiskTable
  cause : IO.Error
  rejected : disposed.Returned recover cause
  workerInodes : (view.descriptors beforeCleanup).inode = (view.descriptors entry).inode
  finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner disposed.reached

namespace RawFinalizedOpenAttempt

variable (seen : RawFinalizedOpenAttempt view directory calls init release input entry)

def diagnostic : IO.Error := seen.disposed.diagnostic seen.cause

def reached : heap := seen.finalized.reached

/-- The attempt uses the same native cache initializer and returns its
chosen error with both drops already accounted for. -/
theorem returns :
    ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles),
      DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      finishFailedOpen (calls.runOpen input init makeCache (seen.disposed.errorScope seen.recover))
        release seen.admitted.lock entry = .error seen.diagnostic seen.reached ∧
      (view.descriptors seen.reached).inode = (view.descriptors entry).inode ∧
      (view.files seen.reached).image = (view.files entry).image ∧
      (TryLockObserves (view.files seen.reached).owners directory (.ok true) ↔
        seen.disposed.unlockResult = .ok () ∨
          (view.descriptors seen.reached).references seen.admission.owner.description = []) := by
  obtain ⟨cacheOpen, makeCache, _, isOpen, source, _, _, ran, census, files, vacant⟩ :=
    seen.disposed.returnsAfterLockFinalization seen.recover seen.cause seen.rejected seen.finalized
  refine ⟨cacheOpen, makeCache, isOpen, source, ran, ?_, files, vacant⟩
  change (view.descriptors seen.finalized.reached).inode = (view.descriptors entry).inode
  rw [census]
  exact seen.workerInodes

end RawFinalizedOpenAttempt

/-- An ordinary admission error before a lock handle is returned.
This route records failures whose local effects leave the tracked file
and descriptor projections unchanged. -/
structure RawBeforeFlockRejection (view : OpenCloseHeapView heap FileImage) (calls : RawOpenAdmissionCallbacks heap)
    (input : FilePath) (entry : heap) where
  cause : IO.Error
  reached : heap
  failed : calls.beforeFlock input entry = .error cause reached
  census : view.descriptors reached = view.descriptors entry
  files : view.files reached = view.files entry

/-- Classify the actual first failed prefix and return its error on
its reached heap. The held callbacks cannot run before a lock handle
has been returned. -/
theorem RawBeforeFlockRejection.returns
    (seen : RawBeforeFlockRejection view calls input entry)
    (init : OpenSyncCacheCallbacks heap)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
    (recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α) :
    RawOpenPrefixReturn calls input entry (.error seen.cause seen.reached) ∧
    calls.runOpen input init makeCache recover entry = .error seen.cause seen.reached ∧
    RawOpenReturn calls input entry
      (fun resolved => openSyncFilesWith (init.openDirectory resolved.path) init.newRef init.newRef init.newRef makeCache)
      recover (calls.runOpen input init makeCache recover entry) := by
  have prefixFailed : RawOpenPrefixReturn calls input entry (.error seen.cause seen.reached) :=
    seen.failed ▸ calls.classifiesBeforeFlock input entry
  have returned : calls.runOpen input init makeCache recover entry = .error seen.cause seen.reached := by
    rw [calls.runsAfterPrefix, seen.failed]
  exact ⟨prefixFailed, returned, returned.symm ▸ .beforeFlock prefixFailed⟩

/-- The next attempt receives the exact caller-visible heap of its
predecessor. A surviving lock alias after failed unlock can stop an
admitted retry at the current result. -/
inductive RawFinalizedOpenAttempts (view : OpenCloseHeapView heap FileImage) (directory : DiskDirectory)
    (calls : RawOpenAdmissionCallbacks heap) (init : OpenSyncCacheCallbacks heap)
    (release : IO.FS.Handle → heap → heap) (start : heap) : List (FilePath × IO.Error) → heap → Prop where
  | empty : RawFinalizedOpenAttempts view directory calls init release start [] start
  | beforeFlock {earlier : List (FilePath × IO.Error)} {entry : heap}
      (prior : RawFinalizedOpenAttempts view directory calls init release start earlier entry)
      (input : FilePath) (seen : RawBeforeFlockRejection view calls input entry) :
      RawFinalizedOpenAttempts view directory calls init release start (earlier ++ [(input, seen.cause)]) seen.reached
  | attempt {earlier : List (FilePath × IO.Error)} {entry : heap}
      (prior : RawFinalizedOpenAttempts view directory calls init release start earlier entry)
      (vacant : TryLockObserves (view.files entry).owners directory (.ok true))
      (input : FilePath) (seen : RawFinalizedOpenAttempt view directory calls init release input entry) :
      RawFinalizedOpenAttempts view directory calls init release start (earlier ++ [(input, seen.diagnostic)]) seen.reached

/-- Every recorded error belongs to its own executed attempt. A sequence
of these read-only failures leaves the original file image and inode
map at the actual heap for the next opening. -/
theorem RawFinalizedOpenAttempts.preserves {start reached : heap} {returns : List (FilePath × IO.Error)}
    (seen : RawFinalizedOpenAttempts view directory calls init release start returns reached) :
    (view.descriptors reached).inode = (view.descriptors start).inode ∧
    (view.files reached).image = (view.files start).image := by
  induction seen with
  | empty => exact ⟨rfl, rfl⟩
  | beforeFlock _ _ refused earlier =>
    exact ⟨(congrArg DescriptorInventory.inode refused.census).trans earlier.1,
      (congrArg LockedFileState.image refused.files).trans earlier.2⟩
  | attempt _ _ _ attempt earlier =>
    obtain ⟨_, _, _, _, _, sameInodes, sameFiles, _⟩ := attempt.returns
    exact ⟨sameInodes.trans earlier.1, sameFiles.trans earlier.2⟩

end Alvoki.Storage.DiskSession
