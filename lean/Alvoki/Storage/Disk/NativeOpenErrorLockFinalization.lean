import Alvoki.Storage.Disk.NativeOpenClose
import Alvoki.Storage.Disk.LockCensusTrace

namespace Alvoki.Storage.DiskSession

variable {heap image α : Type}

/-- Interpret a reported nonthrowing lock finalizer at the failed open's
return boundary. The successful path transfers its handle to the table. -/
def finishFailedOpen (openTable : EStateM IO.Error heap α) (release : IO.FS.Handle → heap → heap)
    (lock : IO.FS.Handle) : EStateM IO.Error heap α := fun entry =>
  match openTable entry with
  | .ok table reached => .ok table reached
  | .error cause reached => .error cause (release lock reached)

/-- Observe the close of the exact lock slot after the unlock syscall.
Other descriptions and any subsequent acquisition are outside this
finalization event. Aliases of the same description can remain live. -/
structure RawOpenErrorLockFinalization (view : OpenCloseHeapView heap image) (directory : DiskDirectory)
    (release : IO.FS.Handle → heap → heap) (lock : IO.FS.Handle) (slot : DescriptorSlot) (before : heap) where
  reached : heap
  sameSlot : (view.handle before lock).2.1 = slot
  live : slot ∈ (view.descriptors before).slots
  finalized : release lock before = reached
  census : view.descriptors reached = (view.descriptors before).afterDrops [slot.closeEvent]
  files : view.files reached = (view.descriptors before).dropLockState slot.description [slot.closeEvent]
    directory (view.files before)

/-- The caller gets the selected diagnostic after the observed slot
close. Explicit successful unlock already made the lock vacant. On
error, the last reference to the same description releases ownership. -/
theorem RawOpenErrorLockFinalization.returns
    {view : OpenCloseHeapView heap image} {directory : DiskDirectory}
    {release : IO.FS.Handle → heap → heap} {lock : IO.FS.Handle} {slot : DescriptorSlot} {before entry : heap}
    (seen : RawOpenErrorLockFinalization view directory release lock slot before)
    (openTable : EStateM IO.Error heap α) {cause : IO.Error} (ran : openTable entry = .error cause before)
    (unlockResult : Except IO.Error Unit)
    (owner : (view.files before).owners (directory.file .lock) = match unlockResult with
      | .ok () => none
      | .error _ => some slot.description) :
    finishFailedOpen openTable release lock entry = .error cause seen.reached ∧
    (view.handle before lock).2.1 = slot ∧
    (view.descriptors seen.reached).inode = (view.descriptors before).inode ∧
    (view.files seen.reached).image = (view.files before).image ∧
    (TryLockObserves (view.files seen.reached).owners directory (.ok true) ↔
      unlockResult = .ok () ∨ (view.descriptors seen.reached).references slot.description = []) := by
  have live : (view.descriptors before).references slot.description ≠ [] :=
    List.ne_nil_of_mem ((view.descriptors before).mem_references.mpr ⟨slot, seen.live, rfl, rfl⟩)
  have frame : (view.files seen.reached).image = (view.files before).image := by
    rw [seen.files]
    simp [DescriptorInventory.dropLockState, live, HeldLockReferences.afterFileDrops]
  refine ⟨by simp only [finishFailedOpen, ran, seen.finalized], seen.sameSlot, ?_, frame, ?_⟩
  · rw [seen.census]
    rfl
  · cases result : unlockResult with
    | ok value =>
      cases value
      have vacant : (view.files before).owners (directory.file .lock) = none := by simpa only [result] using owner
      have unowned : (view.files before).owners (directory.file .lock) ≠ some slot.description := by simp [vacant]
      have untouched : (view.files seen.reached).owners = (view.files before).owners := by
        simp only [seen.files, DescriptorInventory.dropLockState, dite_eq_left live,
          HeldLockReferences.afterFileDrops_unowned _ unowned]
      simp [TryLockObserves, untouched, vacant]
    | error diagnostic =>
      have held : (view.files before).owners.Owns directory slot.description := by
        simpa only [result, LockOwners.Owns] using owner
      have trace := (LockCensusTrace.start held live).drops [slot.closeEvent]
      simpa [seen.census, seen.files] using trace.freshFlockAllowed

end Alvoki.Storage.DiskSession
