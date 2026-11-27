import Alvoki.Storage.Disk.Proofs.Recovery.NativeRawFinalizedOpenError
import Alvoki.Storage.Disk.NativeRawOpenReturn

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap : Type} {view : OpenCloseHeapView heap FileImage} {directory : DiskDirectory}
  {calls : RawOpenAdmissionCallbacks heap} {init : OpenSyncCacheCallbacks heap}
  {release : IO.FS.Handle → heap → heap} {input : FilePath} {entry : heap}

/-- A held rejection whose caller sees the finalized result. The
worker image defaults to the input image for a read-only attempt. -/
structure RawFinalizedOpenAttempt (view : OpenCloseHeapView heap FileImage) (directory : DiskDirectory)
    (calls : RawOpenAdmissionCallbacks heap) (init : OpenSyncCacheCallbacks heap)
    (release : IO.FS.Handle → heap → heap) (input : FilePath) (entry : heap)
    (workerImage : FileImage := (view.files entry).image) where
  admission : CensusOpenAdmissionReports input directory (view.descriptors entry) (view.files entry)
  admitted : RawOpenAdmissionReport admission view calls entry
  seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock
  beforeCleanup : heap
  disposed : RawOpenCacheDisposal (admitted := admitted) seed beforeCleanup
  recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap DiskTable
  cause : IO.Error
  rejected : disposed.ReturnedAt recover cause workerImage
  workerInodes : (view.descriptors beforeCleanup).inode = (view.descriptors entry).inode
  finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner disposed.reached

namespace RawFinalizedOpenAttempt

variable {workerImage : FileImage}
  (seen : RawFinalizedOpenAttempt view directory calls init release input entry workerImage)

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
      (view.files seen.reached).image = workerImage ∧
      (TryLockObserves (view.files seen.reached).owners directory (.ok true) ↔
        seen.disposed.unlockResult = .ok () ∨
          (view.descriptors seen.reached).references seen.admission.owner.description = []) := by
  obtain ⟨cacheOpen, makeCache, _, isOpen, source, _, _, ran, census, files, vacant⟩ :=
    seen.disposed.returnsAfterLockFinalizationAt seen.recover seen.cause seen.rejected seen.finalized
  refine ⟨cacheOpen, makeCache, isOpen, source, ran, ?_, files, vacant⟩
  change (view.descriptors seen.finalized.reached).inode = (view.descriptors entry).inode
  rw [census]
  exact seen.workerInodes

end RawFinalizedOpenAttempt

/-- Classify the exact failed worker return, then let the same cache and
lock finalizers expose the worker's reached file image to the caller. -/
def RawFinalizedOpenAttempt.fromWorkerError
    {admission : CensusOpenAdmissionReports input directory (view.descriptors entry) (view.files entry)}
    (admitted : RawOpenAdmissionReport admission view calls entry)
    (seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock) {before : heap}
    (disposed : RawOpenCacheDisposal (admitted := admitted) seed before)
    (recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap DiskTable)
    (cause : IO.Error)
    (failed : ∀ cache, recover directory admitted.lock cache seed.afterPending = .error cause before)
    (owner : (view.files before).owners = admission.held.owners)
    (workerInodes : (view.descriptors before).inode = (view.descriptors entry).inode)
    (finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner disposed.reached) :
    RawFinalizedOpenAttempt view directory calls init release input entry (view.files before).image :=
  ⟨admission, admitted, seed, before, disposed, recover, cause, disposed.returnsAt recover cause failed rfl owner,
    workerInodes, finalized⟩

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

/-- An ordinary flock error after a file-preserving append-open. The
open allocates one fresh description and the caller finalizes that
same slot. The existing lock owner, if any, is live in the census. -/
structure RawFlockRejection (view : OpenCloseHeapView heap FileImage) (calls : RawOpenAdmissionCallbacks heap)
    (directory : DiskDirectory) (release : IO.FS.Handle → heap → heap) (input : FilePath) (entry : heap) where
  report : RawOpenFlockError calls view input entry
  sameDirectory : report.directory = directory
  free : ∀ old ∈ (view.descriptors entry).slots, old.address ≠ (view.handle report.atFlock report.handle).2.1.address
  fresh : (view.descriptors entry).references (view.handle report.atFlock report.handle).2.1.description = []
  appendCensus : view.descriptors report.atFlock =
    (view.descriptors entry).insert (view.handle report.atFlock report.handle).2.1 free
  appendFiles : view.files report.atFlock = view.files entry
  ownerLive : ∀ description, (view.files entry).owners (directory.file .lock) = some description →
    (view.descriptors entry).references description ≠ []
  finalized : RawOpenErrorLockFinalization view directory release report.handle
    (view.handle report.atFlock report.handle).2.1 report.reached

namespace RawFlockRejection

variable (seen : RawFlockRejection view calls directory release input entry)

abbrev slot : DescriptorSlot := (view.handle seen.report.atFlock seen.report.handle).2.1

def reached : heap := seen.finalized.reached

private theorem closeInserted (before : DescriptorInventory) (slot : DescriptorSlot)
    (free : ∀ old ∈ before.slots, old.address ≠ slot.address) :
    (before.insert slot free).afterDrops [slot.closeEvent] = before := by
  have closed := DescriptorInventory.insert_thenClose before slot free []
  simp only [List.nil_append] at closed
  have survives : ∀ old ∈ before.slots, (!slot.closeEvent.removes old.reference) = true := by
    intro old live
    cases removed : slot.closeEvent.removes old.reference with
    | false => rfl
    | true =>
      exfalso
      apply free old live
      simpa [DescriptorSlot.address, DescriptorSlot.closeEvent, LockReferenceDrop.removes,
        Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq] using removed
  rw [closed]
  cases before with
  | mk slots distinct inode =>
    simp only [DescriptorInventory.afterDrops, List.all_cons, List.all_nil, Bool.and_true,
      List.filter_eq_self.mpr survives]

/-- Closing the just-opened slot restores the original inventory and
locked file projection. If the failed flock acquired the lock, that
slot was its only reference and closing it restores prior vacancy. -/
theorem preserves : view.descriptors seen.reached = view.descriptors entry ∧
    view.files seen.reached = view.files entry := by
  have census : view.descriptors seen.reached = view.descriptors entry := by
    change view.descriptors seen.finalized.reached = _
    rw [seen.finalized.census, seen.report.census, seen.appendCensus]
    exact closeInserted _ _ seen.free
  have live : (view.descriptors seen.report.reached).references seen.slot.description ≠ [] :=
    List.ne_nil_of_mem ((view.descriptors seen.report.reached).mem_references.mpr
      ⟨seen.slot, seen.finalized.live, rfl, rfl⟩)
  refine ⟨census, ?_⟩
  change view.files seen.finalized.reached = _
  rw [seen.finalized.files, DescriptorInventory.dropLockState, dite_eq_left live]
  cases effect : seen.report.tookEffect with
  | false =>
    have unowned : (view.files entry).owners (directory.file .lock) ≠ some seen.slot.description :=
      fun owner => seen.ownerLive seen.slot.description owner seen.fresh
    have files : view.files seen.report.reached = view.files entry := by
      have owners : (view.files seen.report.reached).owners = (view.files entry).owners := by
        simpa only [effect, Bool.false_eq_true, ↓reduceIte, seen.appendFiles] using seen.report.owners
      exact (LockedFileState.mk.injEq _ _ _ _).mpr ⟨seen.report.files.trans (congrArg LockedFileState.image seen.appendFiles), owners⟩
    exact (((view.descriptors seen.report.reached).held seen.slot.description live).afterFileDrops_unowned
      (files.symm ▸ unowned)).trans files
  | true =>
    have vacant : (view.files entry).owners (directory.file .lock) = none := by
      simpa only [seen.sameDirectory, seen.appendFiles] using seen.report.vacant effect
    have owners : (view.files seen.report.reached).owners =
        (view.files entry).owners.set (directory.file .lock) (some seen.slot.description) := by
      simpa only [effect, ↓reduceIte, seen.sameDirectory, seen.appendFiles] using seen.report.owners
    have held : (view.files seen.report.reached).owners.Owns directory seen.slot.description := by
      simp [LockOwners.Owns, owners, LockOwners.set]
    have refs : ((view.descriptors seen.report.reached).afterDrops [seen.slot.closeEvent]).references
        seen.slot.description = [] := by
      have finalCensus := seen.finalized.census
      change view.descriptors seen.reached = _ at finalCensus
      rw [← finalCensus, census]
      exact seen.fresh
    have last := (view.descriptors seen.report.reached).held_remaining seen.slot.description live [seen.slot.closeEvent]
    rw [((view.descriptors seen.report.reached).held seen.slot.description live).afterFileDrops_released held (last.trans refs)]
    have restored : ((view.files entry).owners.set (directory.file .lock) (some seen.slot.description)).set
        (directory.file .lock) none = (view.files entry).owners := by
      funext path
      by_cases same : path = directory.file .lock
      · simp [LockOwners.set, same, vacant]
      · simp [LockOwners.set, same]
    exact (LockedFileState.mk.injEq _ _ _ _).mpr
      ⟨seen.report.files.trans (congrArg LockedFileState.image seen.appendFiles),
        by rw [owners]; exact restored⟩

/-- The actual flock result prevents cache initialization, recovery
and explicit unlock. The reported finalizer closes the same handle
without changing the source diagnostic. -/
theorem returns (init : OpenSyncCacheCallbacks heap)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
    (recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α) :
    RawOpenReturn calls input entry
      (fun resolved => openSyncFilesWith (init.openDirectory resolved.path) init.newRef init.newRef init.newRef makeCache)
      recover (calls.runOpen input init makeCache recover entry) ∧
    finishFailedOpen (calls.runOpen input init makeCache recover) release seen.report.handle entry =
      .error seen.report.cause seen.reached := by
  have ran : calls.runOpen input init makeCache recover entry = .error seen.report.cause seen.report.reached := by
    rw [calls.runsAfterFlock input seen.report.opened init makeCache recover, seen.report.flock]
  refine ⟨ran.symm ▸ .flockError seen.report.opened seen.report.flock, ?_⟩
  simp only [finishFailedOpen, ran, seen.finalized.finalized, reached]

end RawFlockRejection

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
  | flockError {earlier : List (FilePath × IO.Error)} {entry : heap}
      (prior : RawFinalizedOpenAttempts view directory calls init release start earlier entry)
      (input : FilePath) (seen : RawFlockRejection view calls directory release input entry) :
      RawFinalizedOpenAttempts view directory calls init release start (earlier ++ [(input, seen.report.cause)]) seen.reached
  | attempt {earlier : List (FilePath × IO.Error)} {entry : heap}
      (prior : RawFinalizedOpenAttempts view directory calls init release start earlier entry)
      (vacant : TryLockObserves (view.files entry).owners directory (.ok true))
      (input : FilePath) (seen : RawFinalizedOpenAttempt view directory calls init release input entry) :
      RawFinalizedOpenAttempts view directory calls init release start (earlier ++ [(input, seen.diagnostic)]) seen.reached

/-- Compose a frame at the caller-visible endpoints of the failed
opens. Each local frame belongs to the reached heap of its own attempt. -/
theorem RawFinalizedOpenAttempts.frames {start reached : heap} {returns : List (FilePath × IO.Error)}
    (seen : RawFinalizedOpenAttempts view directory calls init release start returns reached)
    {frame : heap → heap → Prop} (empty : ∀ atHeap, frame atHeap atHeap)
    (compose : ∀ {a b c}, frame a b → frame b c → frame a c)
    (beforeFlock : ∀ input entry (refused : RawBeforeFlockRejection view calls input entry), frame entry refused.reached)
    (flockError : ∀ input entry (refused : RawFlockRejection view calls directory release input entry), frame entry refused.reached)
    (attempt : ∀ input entry (failed : RawFinalizedOpenAttempt view directory calls init release input entry),
      frame entry failed.reached) :
    frame start reached := by
  induction seen with
  | empty => exact empty _
  | beforeFlock _ input refused prior => exact compose prior (beforeFlock input _ refused)
  | flockError _ input refused prior => exact compose prior (flockError input _ refused)
  | attempt _ _ input failed prior => exact compose prior (attempt input _ failed)

/-- Every recorded error belongs to its own executed attempt. A sequence
of these read-only failures leaves the original file image and inode
map at the actual heap for the next opening. -/
theorem RawFinalizedOpenAttempts.preserves {start reached : heap} {returns : List (FilePath × IO.Error)}
    (seen : RawFinalizedOpenAttempts view directory calls init release start returns reached) :
    (view.descriptors reached).inode = (view.descriptors start).inode ∧
    (view.files reached).image = (view.files start).image := by
  refine seen.frames (frame := fun first last => (view.descriptors last).inode = (view.descriptors first).inode ∧
      (view.files last).image = (view.files first).image)
    (fun _ => ⟨rfl, rfl⟩) (fun first later => ⟨later.1.trans first.1, later.2.trans first.2⟩)
    (fun _ _ refused => ⟨congrArg DescriptorInventory.inode refused.census, congrArg LockedFileState.image refused.files⟩)
    (fun _ _ refused => ?_) (fun _ _ attempt => ?_)
  · obtain ⟨sameCensus, sameFiles⟩ := refused.preserves
    exact ⟨congrArg DescriptorInventory.inode sameCensus, congrArg LockedFileState.image sameFiles⟩
  · obtain ⟨_, _, _, _, _, sameInodes, sameFiles, _⟩ := attempt.returns
    exact ⟨sameInodes, sameFiles⟩

end Alvoki.Storage.DiskSession
