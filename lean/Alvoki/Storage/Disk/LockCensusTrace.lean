import Alvoki.Storage.Disk.DescriptorFork
import Alvoki.Storage.Disk.BatchRecoveryPrefix

namespace Alvoki.Storage.DiskSession

open WalSegmentRepair

/-- Use the same current descriptor inventory for the lock drop and for
the census after that drop. An already ended owner has no references to
release. A later lock acquisition is a separate operation. -/
def DescriptorInventory.dropLockState (inventory : DescriptorInventory)
    (description : Nat) (drops : List LockReferenceDrop) (directory : DiskDirectory)
    (before : LockedFileState image) : LockedFileState image :=
  if live : inventory.references description ≠ [] then
    (inventory.held description live).afterFileDrops drops directory before
  else before

/-- A chronological observation of one lock description, with a single
descriptor inventory carried across allocations, private forks and drops.
The caller reports successful slot events in order, with stable process
identities and a complete census for the tracked description. A new alias
requires that description to be live. This projection holds the lock file
binding fixed and excludes explicit unlock, reacquisition and non-slot
references. File effects of handle creation and finalization are tracked
by the corresponding filesystem observations. -/
inductive LockCensusTrace (directory : DiskDirectory) (description : Nat)
    (initial : DescriptorInventory) (source : LockedFileState image) :
    DescriptorInventory → LockedFileState image → Prop where
  | start (held : source.owners.Owns directory description)
      (live : initial.references description ≠ []) :
      LockCensusTrace directory description initial source initial source
  | insert {inventory before}
      (prior : LockCensusTrace directory description initial source inventory before)
      (slot : DescriptorSlot) (free : ∀ previous ∈ inventory.slots, previous.address ≠ slot.address)
      (aliasLive : slot.description = description → inventory.references description ≠ []) :
      LockCensusTrace directory description initial source (inventory.insert slot free) before
  | fork {inventory before}
      (prior : LockCensusTrace directory description initial source inventory before)
      (parent child : Nat) (fresh : ∀ slot ∈ inventory.slots, slot.reference.process ≠ child) :
      LockCensusTrace directory description initial source (inventory.forkPrivate parent child fresh) before
  | drops {inventory before}
      (prior : LockCensusTrace directory description initial source inventory before)
      (events : List LockReferenceDrop) :
      LockCensusTrace directory description initial source (inventory.afterDrops events)
        (inventory.dropLockState description events directory before)

private theorem references_fork_empty (inventory : DescriptorInventory) (parent child description : Nat)
    (fresh : ∀ slot ∈ inventory.slots, slot.reference.process ≠ child) :
    (inventory.forkPrivate parent child fresh).references description = [] ↔
      inventory.references description = [] := by
  constructor
  · intro empty
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro reference member
    obtain ⟨slot, present, sameRef, desc⟩ := inventory.mem_references.mp member
    have inherited := (inventory.mem_forkPrivate parent child fresh).mpr (.inl present)
    have present := (inventory.forkPrivate parent child fresh).mem_references.mpr ⟨slot, inherited, sameRef, desc⟩
    simp only [empty, List.not_mem_nil] at present
  · intro empty
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro reference member
    obtain ⟨slot, present, _, desc⟩ := (inventory.forkPrivate parent child fresh).mem_references.mp member
    rcases (inventory.mem_forkPrivate parent child fresh).mp present with existing | ⟨old, earlier, _, same⟩
    · have live := inventory.mem_references.mpr ⟨slot, existing, rfl, desc⟩
      simp only [empty, List.not_mem_nil] at live
    · subst slot
      have live := inventory.mem_references.mpr ⟨old, earlier, rfl, desc⟩
      simp only [empty, List.not_mem_nil] at live

/-- Slot events preserve the file image and every other lock. They
release this owner exactly when its chronological census is empty. -/
theorem LockCensusTrace.reached {initial inventory : DescriptorInventory}
    {directory : DiskDirectory} {description : Nat} {source after : LockedFileState image}
    (observed : LockCensusTrace directory description initial source inventory after) :
    source.owners.Owns directory description ∧ inventory.inode = initial.inode ∧
      after = if inventory.references description = [] then
        ⟨source.image, source.owners.set (directory.file .lock) none⟩
      else source := by
  induction observed with
  | start held live =>
    exact ⟨held, rfl, by simp only [ite_eq_right live]⟩
  | insert _ slot free aliasLive ih =>
    refine ⟨ih.1, ih.2.1, ?_⟩
    by_cases same : slot.description = description
    · simp [DescriptorInventory.references_insert, same, ih.2.2, aliasLive same]
    · simpa only [DescriptorInventory.references_insert, ite_eq_right same] using ih.2.2
  | fork _ parent child fresh ih =>
    exact ⟨ih.1, ih.2.1, by simpa only [references_fork_empty _ parent child description fresh] using ih.2.2⟩
  | @drops inventory before prior events ih =>
    refine ⟨ih.1, ih.2.1, ?_⟩
    by_cases live : inventory.references description ≠ []
    · have same : before = source := by simpa only [ite_eq_right live] using ih.2.2
      have refs := inventory.held_remaining description live events
      by_cases last : (inventory.afterDrops events).references description = []
      · rw [DescriptorInventory.dropLockState, dite_eq_left live, same,
          (inventory.held description live).afterFileDrops_released ih.1 (refs.trans last), ite_eq_left last]
      · rw [DescriptorInventory.dropLockState, dite_eq_left live,
          (inventory.held description live).afterFileDrops_surviving (fun empty => last (refs.symm.trans empty)),
          same, ite_eq_right last]
    · have empty := Classical.not_not.mp live
      have nextEmpty : (inventory.afterDrops events).references description = [] := by
        simp [DescriptorInventory.references_afterDrops, empty]
      simpa only [DescriptorInventory.dropLockState, dite_eq_right live, ite_eq_left empty, ite_eq_left nextEmpty]
        using ih.2.2

/-- The lock on the same stable file is vacant for a fresh competing
description exactly when the earlier description has no reported slots. -/
theorem LockCensusTrace.freshFlockAllowed {directory : DiskDirectory} {description : Nat}
    {source after : LockedFileState image} {initial inventory : DescriptorInventory}
    (observed : LockCensusTrace directory description initial source inventory after) :
    TryLockObserves after.owners directory (.ok true) ↔ inventory.references description = [] := by
  obtain ⟨held, _, reached⟩ := observed.reached
  by_cases last : inventory.references description = []
  · rw [reached, ite_eq_left last]
    simp [TryLockObserves, LockOwners.set, last]
  · rw [reached, ite_eq_right last]
    simp [TryLockObserves, LockOwners.Owns, last] at held ⊢
    exact fun vacant => by rw [held] at vacant; contradiction

/-- The same ordered census supplies the retry prefix's reference drops.
Each drop comes from the inventory reached by the preceding slot events.
The prefix retains their lock and file projection. -/
theorem LockCensusTrace.reopenTrace {directory : DiskDirectory} {description : Nat}
    {origin source after : LockedFileState FileImage} {initial inventory : DescriptorInventory} {keeper : Nat}
    (observed : LockCensusTrace directory description initial source inventory after)
    (earlier : ReportedReopenPrefix directory keeper origin source) :
    ReportedReopenPrefix directory keeper origin after := by
  induction observed with
  | start => exact earlier
  | insert _ _ _ _ ih | fork _ _ _ _ ih => exact ih
  | @drops census before _ events ih =>
    by_cases live : census.references description ≠ []
    · simpa only [DescriptorInventory.dropLockState, dite_eq_left live] using
        ih.referenceDrops (census.held description live) events
    · simpa only [DescriptorInventory.dropLockState, dite_eq_right live] using ih

end Alvoki.Storage.DiskSession
