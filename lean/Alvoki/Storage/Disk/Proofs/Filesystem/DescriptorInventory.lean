import Alvoki.Storage.Disk.Proofs.Recovery.SegmentedDatabaseTrace
import Alvoki.Storage.Disk.Proofs.Filesystem.SyncHandleEffects

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- A descriptor-table slot and its stable open-description identity. -/
structure DescriptorSlot where
  reference : LockReference
  description : Nat

namespace DescriptorSlot

def address (slot : DescriptorSlot) : Nat × Nat := (slot.reference.process, slot.reference.fd)

end DescriptorSlot

/-- One complete observation of the private descriptor tables in scope.
Identities remain stable across the observed drop interval. No new aliases
or independent unlocks occur within that interval. The object map uses the
same identity namespace as the filesystem observations. -/
structure DescriptorInventory where
  slots : List DescriptorSlot
  distinct : (slots.map DescriptorSlot.address).Nodup
  inode : Nat → Nat

namespace DescriptorInventory

def references (inventory : DescriptorInventory) (description : Nat) : List LockReference :=
  (inventory.slots.filter fun slot => slot.description == description).map DescriptorSlot.reference

theorem mem_references (inventory : DescriptorInventory) {description : Nat} {reference : LockReference} :
    reference ∈ inventory.references description ↔
      ∃ slot ∈ inventory.slots, slot.reference = reference ∧ slot.description = description := by
  simp only [references, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨slot, ⟨present, identity⟩, same⟩
    exact ⟨slot, present, same, identity⟩
  · rintro ⟨slot, present, same, identity⟩
    exact ⟨slot, ⟨present, identity⟩, same⟩

def held (inventory : DescriptorInventory) (description : Nat)
    (live : inventory.references description ≠ []) : HeldLockReferences description where
  live := inventory.references description
  nonempty := live
  distinct := by
    simp only [references, List.map_map]
    change ((inventory.slots.filter fun slot => slot.description == description).map DescriptorSlot.address).Nodup
    exact (List.filter_sublist.map DescriptorSlot.address).nodup inventory.distinct

/-- A close, successful exec or final table exit drops slots in every
observed description, including descriptions that do not own the flock. -/
def afterDrops (inventory : DescriptorInventory) (drops : List LockReferenceDrop) : DescriptorInventory where
  slots := inventory.slots.filter fun slot => drops.all fun event => !event.removes slot.reference
  distinct := (List.filter_sublist.map DescriptorSlot.address).nodup inventory.distinct
  inode := inventory.inode

theorem references_afterDrops (inventory : DescriptorInventory) (description : Nat)
    (drops : List LockReferenceDrop) :
    (inventory.afterDrops drops).references description =
      (inventory.references description).filter (fun reference => drops.all fun event => !event.removes reference) := by
  simp only [afterDrops, references, List.filter_map, List.filter_filter, Function.comp_def, Bool.and_comm]

theorem held_remaining (inventory : DescriptorInventory) (description : Nat)
    (live : inventory.references description ≠ []) (drops : List LockReferenceDrop) :
    (inventory.held description live).remaining drops = (inventory.afterDrops drops).references description :=
  (inventory.references_afterDrops description drops).symm

theorem wasLive {inventory : DescriptorInventory} {drops : List LockReferenceDrop} {description : Nat}
    {issuer : LockReference} (issuing : issuer ∈ (inventory.afterDrops drops).references description) :
    inventory.references description ≠ [] := by
  rw [inventory.references_afterDrops description drops] at issuing
  exact List.ne_nil_of_mem (List.mem_filter.mp issuing).1

private theorem slot_eq {inventory : DescriptorInventory} {left right : DescriptorSlot}
    (presentLeft : left ∈ inventory.slots) (presentRight : right ∈ inventory.slots)
    (same : left.address = right.address) : left = right := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp presentLeft
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp presentRight
  have hi' : i < (inventory.slots.map DescriptorSlot.address).length := by simpa
  have hj' : j < (inventory.slots.map DescriptorSlot.address).length := by simpa
  have eq := (inventory.distinct.getElem_inj (hi := hi') (hj := hj')).mp
    (by simpa only [List.getElem_map] using same)
  subst j
  rfl

/-- A numeric slot in a process epoch cannot be evidence for two different
open descriptions in a single observation. -/
theorem description_unique {inventory : DescriptorInventory} {left right : Nat}
    {first second : LockReference} (presentLeft : first ∈ inventory.references left)
    (presentRight : second ∈ inventory.references right)
    (same : (first.process, first.fd) = (second.process, second.fd)) : left = right := by
  obtain ⟨a, ha, rfl, rfl⟩ := inventory.mem_references.mp presentLeft
  obtain ⟨b, hb, rfl, rfl⟩ := inventory.mem_references.mp presentRight
  exact congrArg DescriptorSlot.description (slot_eq ha hb same)

/-- If the original description's final slot is gone, every address
that belonged to it is free in the reached drop-only table. -/
theorem addressFreeAfterLastDrop (inventory : DescriptorInventory) (drops : List LockReferenceDrop)
    {description : Nat} {previous : LockReference} (present : previous ∈ inventory.references description)
    (ended : (inventory.afterDrops drops).references description = []) :
    ∀ slot ∈ (inventory.afterDrops drops).slots, slot.address ≠ (previous.process, previous.fd) := by
  intro slot surviving same
  obtain ⟨old, wasPresent, previousSlot, oldDescription⟩ := inventory.mem_references.mp present
  have before : slot ∈ inventory.slots := (List.mem_filter.mp surviving).1
  have address : slot.address = old.address := by simpa only [DescriptorSlot.address, previousSlot] using same
  have sameSlot := slot_eq before wasPresent address
  subst slot
  have stillPresent := (inventory.afterDrops drops).mem_references.mpr
    ⟨old, surviving, previousSlot, oldDescription⟩
  rw [ended] at stillPresent
  exact List.not_mem_nil stillPresent

/-- Record an observed allocation or duplication into an unused slot.
The new slot's description and object identity come from that observation.
A raw slot can be recorded even if wrapping it in a Lean handle failed. -/
def insert (inventory : DescriptorInventory) (slot : DescriptorSlot)
    (free : ∀ previous ∈ inventory.slots, previous.address ≠ slot.address) : DescriptorInventory where
  slots := slot :: inventory.slots
  distinct := by
    rw [List.map_cons, List.nodup_cons]
    exact ⟨fun taken => by
      obtain ⟨previous, present, same⟩ := List.mem_map.mp taken
      exact free previous present same, inventory.distinct⟩
  inode := inventory.inode

theorem references_insert (inventory : DescriptorInventory) (slot : DescriptorSlot)
    (free : ∀ previous ∈ inventory.slots, previous.address ≠ slot.address) (description : Nat) :
    (inventory.insert slot free).references description =
      if slot.description = description then slot.reference :: inventory.references description
      else inventory.references description := by
  by_cases same : slot.description = description <;> simp [insert, references, same]

/-- Given an observed raw allocation into the still-live private table,
the cooperating opener can receive the old numeric address and install
under its distinct description. The lock binding and recovery result are
reported separately. -/
theorem reopenOnReusedSlot (inventory : DescriptorInventory) (drops : List LockReferenceDrop)
    {image : Type} {directory : DiskDirectory} {before : LockedFileState image}
    {owner nextRef : Nat} {previous : LockReference} (present : previous ∈ inventory.references owner)
    (ownership : before.owners.Owns directory owner)
    (ended : (inventory.afterDrops drops).references owner = [])
    (openedSlot : DescriptorSlot) (address : openedSlot.address = (previous.process, previous.fd))
    (fresh : openedSlot.description ≠ owner)
    (allocation : LockReferenceDrop.exited openedSlot.reference.process ∉ drops ∧
      (inventory.afterDrops drops).references openedSlot.description = [])
    (bindings : FilePath → Option Nat)
    (object : bindings (directory.file .lock) = some (inventory.inode openedSlot.description))
    (sameLock : inventory.inode openedSlot.description = inventory.inode owner)
    (unlock : UnlockReport) (recover : EStateM IO.Error image Reopened)
    {opened : Reopened} {after : image} (recovered : recover before.image = .ok opened after) :
    let ownerLive := List.ne_nil_of_mem present
    let free := inventory.addressFreeAfterLastDrop drops present ended
    let reached := (inventory.afterDrops drops).insert openedSlot (fun _ member => address ▸ free _ member)
    let released := (inventory.held owner ownerLive).afterFileDrops drops directory before
    reached.references owner = [] ∧ reached.references openedSlot.description = [openedSlot.reference] ∧
      bindings (directory.file .lock) = some (inventory.inode owner) ∧
      TryLockObserves released.owners directory (.ok true) ∧
      runOpenWithInstallation directory openedSlot.description nextRef (.ok true) unlock recover released =
        .ok ⟨directory, openedSlot.description, .ready opened.installed, nextRef, nextRef + 1⟩
          ⟨after, before.owners.set (directory.file .lock) (some openedSlot.description)⟩ := by
  intro ownerLive free reached released
  have last : (inventory.held owner ownerLive).remaining drops = [] := by
    rwa [inventory.held_remaining]
  obtain ⟨acquires, reopened⟩ := runOpenWithInstallation_afterLastReferenceDrop
    (inventory.held owner ownerLive) ownership last unlock recovered
  refine ⟨?_, ?_, sameLock ▸ object, acquires, reopened⟩
  · simp [reached, references_insert, fresh, ended]
  · simp [reached, references_insert, allocation.2]

/-- Construct the delayed directory observation from the issuing slot in
the reached table. Its description and object are the ones observed in
that table rather than independently supplied lifetime witnesses. -/
def delayedDirectorySync (inventory : DescriptorInventory) (drops : List LockReferenceDrop)
    (directory : DiskDirectory) (description : Nat)
    (issuer : LockReference) (issuing : issuer ∈ (inventory.afterDrops drops).references description)
    (bindings : FilePath → Option Nat) (binding : bindings directory.path = some (inventory.inode description))
    (outcome : DelayedDirectorySyncOutcome) : DelayedDirectorySync directory where
  captured := ⟨description, inventory.inode description⟩
  references := inventory.held description (wasLive issuing)
  issuer := issuer
  drops := drops
  retained := by rwa [inventory.held_remaining]
  effectTarget := ⟨description, inventory.inode description⟩
  sameTarget := rfl
  statDirectory := bindings
  liveTarget := binding
  outcome := outcome

end DescriptorInventory

/-- The lock-release and delayed-sync evidence share one complete census
of the original descriptor slots and the same reached drop interval. The
filesystem report still supplies the directory binding and actual effect. -/
structure DirectoryDropObservation (directory : DiskDirectory) (writer : Nat) where
  inventory : DescriptorInventory
  drops : List LockReferenceDrop
  writerLive : inventory.references writer ≠ []
  writerEnded : (inventory.afterDrops drops).references writer = []
  syncing : Nat
  issuer : LockReference
  issuing : issuer ∈ (inventory.afterDrops drops).references syncing
  bindings : FilePath → Option Nat
  directoryBinding : bindings directory.path = some (inventory.inode syncing)
  outcome : DelayedDirectorySyncOutcome

namespace DirectoryDropObservation

def barrier {directory writer} (observed : DirectoryDropObservation directory writer) : DelayedDirectorySync directory :=
  observed.inventory.delayedDirectorySync observed.drops directory observed.syncing
    observed.issuer observed.issuing observed.bindings observed.directoryBinding observed.outcome

theorem last {directory writer} (observed : DirectoryDropObservation directory writer) :
    (observed.inventory.held writer observed.writerLive).remaining observed.barrier.drops = [] := by
  rw [observed.inventory.held_remaining]
  exact observed.writerEnded

theorem separate {directory writer} (observed : DirectoryDropObservation directory writer) :
    observed.barrier.captured.description ≠ writer := by
  intro same
  change observed.syncing = writer at same
  have live := observed.issuing
  rw [same, observed.writerEnded] at live
  exact List.not_mem_nil live

end DirectoryDropObservation

/-- Project the same observed descriptor inventory into the existing
mixed append-recovery edge. Readable durable bytes and repair outcomes
are still observed by the cached recovery interpreter. -/
theorem SegmentedDatabaseTrace.delayedDirectoryAppendFromInventory
    {directory initialDescriptor initial allowCollection log writer descriptor before}
    (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (initialReady : initial.RetainedReady directory initialDescriptor)
    (observed : DirectoryDropObservation directory writer) (failure : SegmentedAppendFailure directory before)
    {retry : LockedFileState FileImage}
    (attempts : BoundedReopenTrace directory (AppendRetryTarget before.history failure.event before.wal.active.first)
      (observed.barrier.after failure.released) retry)
    (reopen : BoundedReopenAttempt) (descriptorEq : reopen.descriptor = descriptor)
    (acquired : reopen.acquired = .ok true) (acquisition : TryLockObserves retry.owners directory (.ok true))
    (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < reopen.nextRef)
    (recover : EStateM IO.Error FileImage Reopened)
    (reads : DelayedDirectorySync.CachedAppendReads (descriptor := descriptor) failure retry reopen recover)
    (settles : reopen.sync #[directory.path] retry.image = .ok () retry.image.syncDirectory)
    (healthy : ∀ history, ∀ selected : CanonicalKeeperLayout retry.image history,
      (history = before.history ∨ history = before.history ++ [failure.event]) →
      selected.target.first = before.wal.active.first →
      ∀ action prior next,
        ReachesAction selected.target retry.image.syncDirectory selected.plan.finishActions action prior →
        prior.effect selected.target action = some next →
        performPaths directory selected.plan reopen.removeFile throw reopen.write reopen.sync reopen.renameFile action prior =
          .ok () next) :
    ∃ after,
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [⟨[], some failure.event⟩]) descriptor after ∧
      AppendRetryEndpoint directory before failure.event retry descriptor
        (runOpenWithInstallation directory reopen.descriptor reopen.nextRef reopen.acquired reopen.unlock recover retry) after ∧
      retry.image.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode after.history).size.toUInt64) ∧
      after.checkpoint = before.checkpoint ∧ after.installed.generation = before.installed.generation :=
  prior.delayedDirectoryAppendCached initialReady observed.barrier failure
    (observed.inventory.held writer observed.writerLive) observed.last observed.separate attempts
    reopen descriptorEq acquired acquisition liveRefs fresh recover reads settles healthy

end Alvoki.Storage.DiskSession

namespace Alvoki.Storage.SyncHandleRouting

open DiskSession

/-- Interpret a reached fsync using the exact surviving slot. The
handle-to-description lookup and the syscall outcome are observations.
Cache eviction itself does not remove a descriptor-table slot. -/
def FsyncObservation.ofInventory {handle state : Type} (inventory : DescriptorInventory)
    (drops : List LockReferenceDrop) (description inode : handle → Nat) (descriptor : handle)
    (issuer : LockReference)
    (issuing : issuer ∈ (inventory.afterDrops drops).references (description descriptor))
    (captured : inventory.inode (description descriptor) = inode descriptor)
    (before : state) (persist : Nat → state → state) {effective : Bool}
    {returned : EStateM.Result IO.Error state Unit}
    (effect : FsyncResult before (persist (inventory.inode (description descriptor)) before) effective returned) :
    FsyncObservation description inode descriptor before persist returned where
  references := inventory.held (description descriptor) (DescriptorInventory.wasLive issuing)
  issuer := issuer
  drops := drops
  live := by rwa [inventory.held_remaining]
  effectDescription := description descriptor
  effectInode := inventory.inode (description descriptor)
  sameDescription := rfl
  sameInode := captured
  effective := effective
  effect := effect

end Alvoki.Storage.SyncHandleRouting
