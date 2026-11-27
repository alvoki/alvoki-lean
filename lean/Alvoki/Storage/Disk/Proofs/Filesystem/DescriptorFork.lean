import Alvoki.Storage.Disk.Proofs.Filesystem.DescriptorInventory

namespace Alvoki.Storage.DiskSession

open WalSegmentRepair

private def DescriptorSlot.inherit (slot : DescriptorSlot) (child : Nat) : DescriptorSlot :=
  { slot with reference := { slot.reference with process := child } }

namespace DescriptorInventory

/-- Interpret a reported Linux fork with a fresh process epoch and a
private copy of the parent's descriptor table. The copy preserves numeric
fds, close-on-exec flags and open-description identities. -/
def forkPrivate (inventory : DescriptorInventory) (parent child : Nat)
    (fresh : ∀ slot ∈ inventory.slots, slot.reference.process ≠ child) : DescriptorInventory := by
  let parent's := inventory.slots.filter fun slot => slot.reference.process == parent
  refine ⟨inventory.slots ++ parent's.map (·.inherit child), ?_, inventory.inode⟩
  have distinct : (parent's.map DescriptorSlot.address).Nodup :=
    (List.filter_sublist.map DescriptorSlot.address).nodup inventory.distinct
  rw [List.map_append, List.nodup_append, List.map_map]
  refine ⟨inventory.distinct, ?_, ?_⟩
  · rw [List.Nodup, List.pairwise_map] at distinct ⊢
    refine distinct.imp_of_mem ?_
    intro a b memberA memberB notSame same
    have parentA : a.reference.process = parent := beq_iff_eq.mp (List.mem_filter.mp memberA).2
    have parentB : b.reference.process = parent := beq_iff_eq.mp (List.mem_filter.mp memberB).2
    have sameFd : a.reference.fd = b.reference.fd := by
      have equal := congrArg (fun address : Nat × Nat => address.2) same
      exact equal
    apply notSame
    exact Prod.ext (parentA.trans parentB.symm) sameFd
  · intro existing memberExisting inherited memberInherited coincide
    obtain ⟨a, known, equalA⟩ := List.mem_map.mp memberExisting
    obtain ⟨b, _, equalB⟩ := List.mem_map.mp memberInherited
    have same := equalA.trans (coincide.trans equalB.symm)
    exact fresh a known (congrArg Prod.fst same)

theorem mem_forkPrivate (inventory : DescriptorInventory) (parent child : Nat)
    (fresh : ∀ slot ∈ inventory.slots, slot.reference.process ≠ child) {slot : DescriptorSlot} :
    slot ∈ (inventory.forkPrivate parent child fresh).slots ↔ slot ∈ inventory.slots ∨
      ∃ original ∈ inventory.slots, original.reference.process = parent ∧ original.inherit child = slot := by
  simp only [forkPrivate, List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro (kept | ⟨original, ⟨present, fromParent⟩, inherited⟩)
    · exact Or.inl kept
    · exact Or.inr ⟨original, present, fromParent, inherited⟩
  · rintro (kept | ⟨original, present, fromParent, inherited⟩)
    · exact Or.inl kept
    · exact Or.inr ⟨original, ⟨present, fromParent⟩, inherited⟩

/-- With the lock description confined to the parent's close-on-exec
slots, the modeled private fork and parent exit leave an inherited
reference. A successful child exec drops the last group, with no new
aliases, flag changes or explicit unlocks between the two drops. A
reported healthy open then enters the shared recovery interpreter. -/
theorem forkExitExecReopen (inventory : DescriptorInventory) (parent child : Nat)
    (fresh : ∀ slot ∈ inventory.slots, slot.reference.process ≠ child)
    {image : Type} {directory : DiskDirectory} {before : LockedFileState image} {owner opener nextRef : Nat}
    (owns : before.owners.Owns directory owner) {parentSlot : LockReference}
    (liveParent : parentSlot ∈ inventory.references owner)
    (lockSlots : ∀ slot ∈ inventory.references owner, slot.process = parent ∧ slot.closeOnExec = true)
    (acquired : Except IO.Error Bool) (acquisition : TryLockObserves before.owners directory acquired)
    (unlock : UnlockReport) (recover : EStateM IO.Error image Reopened)
    {opened : Reopened} {after : image} (recovered : recover before.image = .ok opened after) :
    ∃ (refs : HeldLockReferences owner) (cause : IO.Error),
      refs.live = (inventory.forkPrivate parent child fresh).references owner ∧
      refs.remaining [.exited parent] ≠ [] ∧
      refs.afterFileDrops [.exited parent] directory before = before ∧
      runOpenWithInstallation directory opener nextRef acquired unlock recover
        (refs.afterFileDrops [.exited parent] directory before) = .error cause before ∧
      refs.remaining [.exited parent, .executed child] = [] ∧
      TryLockObserves (refs.afterFileDrops [.exited parent, .executed child] directory before).owners
        directory (.ok true) ∧
      runOpenWithInstallation directory opener nextRef (.ok true) unlock recover
        (refs.afterFileDrops [.exited parent, .executed child] directory before) =
          .ok ⟨directory, opener, .ready opened.installed, nextRef, nextRef + 1⟩
            ⟨after, before.owners.set (directory.file .lock) (some opener)⟩ := by
  let forked := inventory.forkPrivate parent child fresh
  obtain ⟨original, present, same, identity⟩ := inventory.mem_references.mp liveParent
  obtain ⟨parentProcess, _⟩ := lockSlots parentSlot liveParent
  have originalProcess : original.reference.process = parent := same ▸ parentProcess
  have distinct : parent ≠ child := originalProcess ▸ fresh original present
  let inherited := original.inherit child
  have copied : inherited ∈ forked.slots :=
    (inventory.mem_forkPrivate parent child fresh).mpr (.inr ⟨original, present, originalProcess, rfl⟩)
  have childKnown : inherited.reference ∈ forked.references owner :=
    forked.mem_references.mpr ⟨inherited, copied, rfl, identity⟩
  let refs := forked.held owner (List.ne_nil_of_mem childKnown)
  have childLeft : inherited.reference ∈ refs.remaining [.exited parent] :=
    (refs.mem_remaining _ _).mpr ⟨childKnown, by simp [inherited, DescriptorSlot.inherit, LockReferenceDrop.removes, distinct.symm]⟩
  have surviving := List.ne_nil_of_mem childLeft
  have noChange := refs.afterFileDrops_surviving (directory := directory) (before := before) surviving
  have last : refs.remaining [.exited parent, .executed child] = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro slot stillLive
    obtain ⟨known, remaining⟩ := (refs.mem_remaining _ _).mp stillLive
    obtain ⟨entry, presentEntry, rfl, description⟩ := forked.mem_references.mp known
    rcases (inventory.mem_forkPrivate parent child fresh).mp presentEntry with earlier | ⟨source, earlier, _, copiedAs⟩
    · have originalSlot := inventory.mem_references.mpr ⟨entry, earlier, rfl, description⟩
      have didNotExit := remaining (.exited parent) (by simp)
      simp [LockReferenceDrop.removes, (lockSlots entry.reference originalSlot).1] at didNotExit
    · subst entry
      have originalSlot := inventory.mem_references.mpr ⟨source, earlier, rfl, description⟩
      have didNotExec := remaining (.executed child) (by simp)
      simp [LockReferenceDrop.removes, DescriptorSlot.inherit, (lockSlots source.reference originalSlot).2] at didNotExec
  obtain ⟨cause, refused⟩ :=
    runOpenWithInstallation_whileReferenceSurvives (descriptor := opener) (nextRef := nextRef)
      refs owns surviving (by simpa only [noChange] using acquisition) unlock recover
  obtain ⟨canAcquire, reopened⟩ := runOpenWithInstallation_afterLastReferenceDrop refs owns last unlock recovered
  exact ⟨refs, cause, rfl, surviving, noChange, refused, last, canAcquire, reopened⟩

end DescriptorInventory
end Alvoki.Storage.DiskSession
