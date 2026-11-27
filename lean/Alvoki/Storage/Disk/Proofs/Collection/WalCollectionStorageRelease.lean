import Alvoki.Storage.Disk.Proofs.Collection.WalCollectionCompletePlan
import Alvoki.Storage.Disk.Proofs.WAL.WalSealedInodeLifetime

namespace Alvoki.Storage.DiskSession

open System

/-- The returned unlink that actually detached the original object at
the canonical planned address. The exact raw path lookup and local
effect are those of the same reported invocation. -/
structure IssuedSealUnlink (directory : DiskDirectory) (root : DeviceInode)
    (removeFile : FilePath → EStateM IO.Error WalSealedUnlinkImage (Except IO.Error Unit))
    (offset : Nat) (object : DeviceInode) where
  beforeView : DirectoryReadNamespace
  afterView : DirectoryReadNamespace
  before : WalSealedUnlinkImage
  after : WalSealedUnlinkImage
  result : Except IO.Error Unit
  call : removeFile (directory.file (.walSegment offset)) before = .ok result after
  effect : WalUnlinkEffect root offset beforeView before result afterView after
  target : effect.target = some object
  detached : effect.removed = true

/-- A successful full pass must actually detach a selected name that
was present at entry. Earlier unlinks frame its exact observed inode. -/
theorem WalUnlinkPrefix.detachesObservedObject {directory : DiskDirectory} {root : DeviceInode} {removeFile}
    {offsets pending removed : List Nat} {failure : Option IO.Error}
    {view afterView : DirectoryReadNamespace} {before after : WalSealedUnlinkImage}
    (reported : WalUnlinkPrefix directory root removeFile offsets view before pending failure afterView after removed)
    (finished : pending = []) (successful : failure = none) {offset : Nat} {object : DeviceInode}
    (selected : offset ∈ offsets) (bound : view.child root (renderWalSegmentName offset) = some object) :
    Nonempty (IssuedSealUnlink directory root removeFile offset object) := by
  induction reported with
  | pause => simp [finished] at selected
  | @next first _ _ _ _ _ _ _ _ _ _ call effect accepted tail ih =>
    by_cases same : offset = first
    · subst offset
      have target := effect.lookup.symm.trans bound
      rcases effect.accepted accepted with detached | missing
      · exact ⟨⟨_, _, _, _, _, call, effect, target, detached⟩⟩
      · rw [bound] at missing
        contradiction
    · have later := (List.mem_cons.mp selected).resolve_left same
      apply ih finished successful later
      rw [effect.lookupAfter]
      simp [same, bound]
  | failed | failedWithoutEffect => contradiction

/-- One observed drop interval for all descriptions that refer to an
inode. The final close, exec or exit event removes all slots still
referring to that inode. The census covers the actual tracked descriptor
tables and the interval has no new slots for this inode. -/
structure InodeLastObservedDrop (inode : Nat) (entry : DescriptorInventory) where
  earlier : List LockReferenceDrop
  event : LockReferenceDrop
  present : ∃ slot ∈ (entry.afterDrops earlier).slots, entry.inode slot.description = inode
  closes : ∀ slot ∈ (entry.afterDrops earlier).slots, entry.inode slot.description = inode →
    event.removes slot.reference = true

namespace InodeLastObservedDrop

variable {inode : Nat} {entry : DescriptorInventory}

def before (last : InodeLastObservedDrop inode entry) : DescriptorInventory :=
  entry.afterDrops last.earlier

def after (last : InodeLastObservedDrop inode entry) : DescriptorInventory :=
  last.before.afterDrops [last.event]

/-- Before the last event the inode has a descriptor reference. Applying
the event removes every remaining slot on that inode, including slots
from separate open descriptions. -/
theorem endsSlots (last : InodeLastObservedDrop inode entry) :
    (∃ slot ∈ last.before.slots, last.before.inode slot.description = inode) ∧
    last.after = entry.afterDrops (last.earlier ++ [last.event]) ∧
    (∀ slot ∈ last.after.slots, last.after.inode slot.description ≠ inode) := by
  let refs : WalSealedInodeReferences inode := ⟨last.before, [last.event],
    fun slot member same => ⟨last.event, List.mem_cons_self, last.closes slot member same⟩, []⟩
  exact ⟨last.present, DescriptorInventory.afterDrops_append .., refs.noSlots⟩

end InodeLastObservedDrop

/-- The filesystem allocation report for a completed eviction after the
descriptor interval. It follows only the blocks exclusive to the original
inode. The retention rule supplies the filesystem-specific effect of
completed eviction and excludes unrelated reallocation of those blocks
within this observation. Non-slot holders are reported separately. -/
structure InodeBlockEviction (inode : Nat) (visibleBefore : FilePath → Option Nat)
    (crashBefore : List (FilePath → Option Nat)) (afterDrop : DescriptorInventory) where
  visible : FilePath → Option Nat
  crashImages : List (FilePath → Option Nat)
  visibleFrame : ∀ path, visible path = some inode → visibleBefore path = some inode
  crashFrame : ∀ names ∈ crashImages, ∀ path, names path = some inode →
    ∃ earlier ∈ crashBefore, earlier path = some inode
  outside : List Nat
  exclusiveBlocks : List Nat
  ownersBefore : Nat → List Nat
  allocatedBefore : Nat → Prop
  allocatedAfter : Nat → Prop
  exclusive : ∀ block ∈ exclusiveBlocks, ownersBefore block = [inode]
  occupied : ∀ block ∈ exclusiveBlocks, allocatedBefore block
  retains : ∀ block ∈ exclusiveBlocks, allocatedAfter block →
    (∃ path, visible path = some inode) ∨
      (∃ names ∈ crashImages, ∃ path, names path = some inode) ∨
      (∃ slot ∈ afterDrop.slots, afterDrop.inode slot.description = inode) ∨ outside ≠ []

/-- An effective observed eviction releases the reported exclusive
blocks once there are no names or references that can keep the inode. -/
theorem InodeBlockEviction.releases {inode : Nat} {visibleBefore : FilePath → Option Nat}
    {crashBefore : List (FilePath → Option Nat)} {afterDrop : DescriptorInventory}
    (observed : InodeBlockEviction inode visibleBefore crashBefore afterDrop)
    (unlinked : ∀ path, visibleBefore path ≠ some inode)
    (durable : ∀ names ∈ crashBefore, ∀ path, names path ≠ some inode)
    (noSlots : ∀ slot ∈ afterDrop.slots, afterDrop.inode slot.description ≠ inode)
    (noOutside : observed.outside = []) :
    ∀ block ∈ observed.exclusiveBlocks,
      observed.ownersBefore block = [inode] ∧ observed.allocatedBefore block ∧ ¬observed.allocatedAfter block := by
  intro block member
  refine ⟨observed.exclusive block member, observed.occupied block member, ?_⟩
  intro allocated
  rcases observed.retains block member allocated with ⟨path, bound⟩ | ⟨names, present, path, bound⟩ |
    ⟨slot, present, object⟩ | outside
  · exact unlinked path (observed.visibleFrame path bound)
  · obtain ⟨earlier, survived, present⟩ := observed.crashFrame names present path bound
    exact durable earlier survived path present
  · exact noSlots slot present object
  · exact outside noOutside

/-- Start with the actual complete collection and follow the selected
canonical inode through the effective directory sync. Given the same
inode's observed link census and last descriptor drop, the filesystem's
completed eviction report accounts for its released exclusive blocks. -/
theorem SegmentedWriterState.RetainedReady.releasesCollectedWalSeal
    {directory : DiskDirectory} {descriptor : Nat} {state : SegmentedWriterState}
    (ready : state.RetainedReady directory descriptor) (calls : WalCollectionReads)
    (inventory : WalCollectionInventoryReport calls directory descriptor state.wal)
    (manifest : calls.paths.readOptional (directory.file .manifest) = .ok state.target.pair.manifest)
    (marker : calls.paths.readOptional (directory.file .walBoundary) = .ok state.target.pair.walBoundary)
    {effectView : DirectoryReadNamespace} {atBarrier : WalSealedUnlinkImage} {removed : List Nat}
    (removeFile : FilePath → EStateM IO.Error WalSealedUnlinkImage (Except IO.Error Unit))
    (unlinked : WalUnlinkPrefix directory inventory.lifetime.root removeFile state.wal.collectionOffsets
      inventory.lifetime.namespaceView (.start state.wal) [] none effectView atBarrier removed)
    (barrier : WalCollectionDirectoryFsync directory inventory.lifetime.root inventory.lifetime.namespaceView
      effectView descriptor atBarrier)
    (sameDirectory : barrier.handle.2.1 = inventory.lifetime.directorySlot)
    (sameWriter : barrier.writerSlot = inventory.owner)
    (effective : barrier.outcome.effective = true)
    (segment : WalSegment) (member : segment ∈ state.wal.sealed) (eligible : state.wal.Eligible segment) :
    let measured := inventory.extent segment (List.mem_append_left _ member)
    let child := measured.child.child
    let inode := inventory.lifetime.namespaceView.modelObject child
    ∀ (links : WalSealedInodeLinks directory segment.first inode measured.metadata calls.paths.lstat barrier.after)
      (last : InodeLastObservedDrop inode barrier.reached)
      (eviction : InodeBlockEviction inode links.visible links.crashImages last.after),
      eviction.outside = [] →
      Nonempty (IssuedSealUnlink directory inventory.lifetime.root removeFile segment.first child) ∧
      barrier.after.DurablyAbsent segment.first ∧
      inventory.lifetime.directorySlot ∈ barrier.reached.slots ∧
      inventory.owner ∈ barrier.reached.slots ∧
      (∀ path, links.visible path ≠ some inode) ∧
      (∀ names ∈ links.crashImages, ∀ path, names path ≠ some inode) ∧
      (∃ slot ∈ last.before.slots, last.before.inode slot.description = inode) ∧
      (∀ slot ∈ last.after.slots, last.after.inode slot.description ≠ inode) ∧
      (∀ block ∈ eviction.exclusiveBlocks,
        eviction.ownersBefore block = [inode] ∧ eviction.allocatedBefore block ∧ ¬eviction.allocatedAfter block) ∧
      calls.collectWithEffects directory removeFile barrier.syncDirectory
        (.ready state.installed, ⟨.start state.wal, state.owners⟩) =
        match barrier.outcome with
        | .completed => .ok () (.ready state.installed, ⟨barrier.after, state.owners⟩)
        | .errorBeforeEffect cause | .errorAfterEffect cause =>
          .error (IO.userError s!"sync failed for '{directory.path}': {cause}")
            (.poisoned, ⟨barrier.after, state.owners⟩) := by
  intro measured child inode links last eviction noOutside
  have offset : segment.first ∈ state.wal.collectionOffsets := List.mem_map.mpr
    ⟨segment, List.mem_filter.mpr ⟨member, WalSegmentImage.canRemove_iff.mpr eligible⟩, rfl⟩
  have issued := unlinked.detachesObservedObject rfl rfl offset (inventory.bound segment (List.mem_append_left _ member))
  obtain ⟨_, _, _, settles, _, returned⟩ := ready.reportedWalCollectionBarrier calls
    (ready.completeObservedWalPlan calls inventory manifest marker) (fun _ member => member)
    (fun segment member => by rw [inventory.bound segment (List.mem_append_left _ member)]; rfl)
    removeFile unlinked barrier
  obtain ⟨exactNames, allMissing⟩ := settles effective
  have absent (sealed : List WalSegment) (survived : sealed ∈ barrier.after.crashSealed) :
      segment.first ∉ sealed.map WalSegment.first := by
    intro found
    obtain ⟨other, contained, same⟩ := List.mem_map.mp found
    exact allMissing segment.first offset sealed survived other contained same
  have absentVisible : segment.first ∉ barrier.after.visible.sealed.map WalSegment.first := by
    rw [barrier.effect.sealed]
    exact absent atBarrier.visible.sealed (exactNames.symm ▸ List.mem_cons_self)
  have missing : barrier.after.DurablyAbsent segment.first := ⟨absentVisible, absent⟩
  obtain ⟨visible, crashes⟩ := links.noLinks measured.links missing
  refine ⟨issued, missing, ?_, ?_, visible, crashes, last.endsSlots.1, last.endsSlots.2.2,
    eviction.releases visible crashes last.endsSlots.2.2 noOutside, returned⟩
  · simpa only [sameDirectory] using barrier.directoryLive
  · simpa only [sameWriter] using barrier.writerLive

end Alvoki.Storage.DiskSession
