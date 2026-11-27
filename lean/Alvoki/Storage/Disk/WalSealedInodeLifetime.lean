import Alvoki.Storage.Disk.Proofs.Collection.SegmentedCollectionStep
import Alvoki.Storage.Disk.DescriptorInventory

namespace Alvoki.Storage

/-- The sealed name is absent from the visible list and all reported crash
lists, including a previously hidden name settled by a later barrier. -/
def WalSealedUnlinkImage.DurablyAbsent (image : WalSealedUnlinkImage) (first : Nat) : Prop :=
  first ∉ image.visible.sealed.map WalSegment.first ∧
  ∀ sealed ∈ image.crashSealed, first ∉ sealed.map WalSegment.first

theorem WalSealedUnlinkImage.completeSealed_absent (before : WalSealedUnlinkImage) (offsets : List Nat)
    {first : Nat} (eligible : first ∈ offsets ∨ first ∉ before.visible.sealed.map WalSegment.first) :
    ((RunCollection.steps offsets).foldl WalSealedUnlinkImage.applyCollectionStep before).DurablyAbsent first := by
  obtain ⟨visible, settled⟩ := before.completeSealed offsets
  have absent : first ∉ (before.visible.sealed.filter (fun segment => !offsets.contains segment.first)).map
      WalSegment.first := by
    intro present
    obtain ⟨segment, kept, start⟩ := List.mem_map.mp present
    obtain ⟨original, kept⟩ := List.mem_filter.mp kept
    subst first
    rcases eligible with selected | missing
    · exact (by simpa using kept : segment.first ∉ offsets) selected
    · exact missing (List.mem_map_of_mem original)
  refine ⟨visible.symm ▸ absent, ?_⟩
  intro sealed survives
  rw [settled] at survives
  exact (List.mem_singleton.mp survives).symm ▸ absent

end Alvoki.Storage

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- Follow the actual shared callback through an effective final barrier,
even when that callback reports an error after settling the names. -/
theorem SegmentedCollectionReport.reclaimsAtEffectiveBarrier {directory : DiskDirectory}
    {before : SegmentedWriterState} (report : SegmentedCollectionReport directory before)
    {initial atBarrier : WalSealedUnlinkImage} {first : Nat}
    (eligible : first ∈ report.offsets ∨ first ∉ initial.visible.sealed.map WalSegment.first) :
    let perform := WalSealedUnlinkImage.performPaths directory report.removeFile report.syncDirectory
    ((report.offsets.map RunCollection.Step.unlink).forM perform) initial = .ok () atBarrier →
    (perform .syncDirectory atBarrier = .ok () atBarrier.syncDirectory ∨
      ∃ cause, perform .syncDirectory atBarrier = .error cause atBarrier.syncDirectory) →
    (report.runFrom initial = .ok () atBarrier.syncDirectory ∨
      ∃ cause, report.runFrom initial = .error cause atBarrier.syncDirectory) ∧
      atBarrier.syncDirectory.DurablyAbsent first := by
  intro perform unlinked effective
  obtain ⟨returned, reached⟩ := report.effects.reachesBarrier report.offsets initial atBarrier unlinked
  change report.runFrom initial = perform .syncDirectory atBarrier at returned
  exact ⟨returned ▸ effective, reached.symm ▸ initial.completeSealed_absent report.offsets eligible⟩

/-- Complete link maps for the selected inode in the same stable object
domain as the no-follow probe. The entry link count belongs to the inode
bound to the selected path, including links outside the held directory.
No operation in the unlink stretch creates new links. -/
structure WalSealedInodeLinks (directory : DiskDirectory) (first inode : Nat) (metadata : IO.FS.Metadata)
    (lstat : FilePath → Except IO.Error IO.FS.Metadata) (reached : WalSealedUnlinkImage) where
  stat : Except IO.Error (IO.FS.Metadata × Nat)
  identified : stat = .ok (metadata, inode)
  projected : lstat (directory.file (.walSegment first)) = stat.map Prod.fst
  entry : FilePath → Option Nat
  entryLinks : List FilePath
  complete : ∀ path, path ∈ entryLinks ↔ entry path = some inode
  canonical : entry (directory.file (.walSegment first)) = some inode
  counted : entryLinks.length = metadata.numLinks.toNat
  visible : FilePath → Option Nat
  crashImages : List (FilePath → Option Nat)
  visibleFrame : ∀ path, visible path = some inode → entry path = some inode
  visibleProjects : visible (directory.file (.walSegment first)) = some inode →
    first ∈ reached.visible.sealed.map WalSegment.first
  crashProjects : ∀ bindings ∈ crashImages, ∃ sealed ∈ reached.crashSealed,
    (∀ path, bindings path = some inode → entry path = some inode) ∧
    (bindings (directory.file (.walSegment first)) = some inode → first ∈ sealed.map WalSegment.first)

/-- The one-link probe and complete census identify the only entry path. -/
theorem WalSealedInodeLinks.entryOnlyCanonical {directory first inode metadata lstat reached}
    (links : WalSealedInodeLinks directory first inode metadata lstat reached)
    (privateSeal : metadata.numLinks = 1) :
    ∀ path, links.entry path = some inode → path = directory.file (.walSegment first) := by
  have count : links.entryLinks.length = 1 := by rw [links.counted, privateSeal]; rfl
  obtain ⟨only, entries⟩ := List.length_eq_one_iff.mp count
  have unique (candidate : FilePath) (bound : links.entry candidate = some inode) : candidate = only := by
    have found := (links.complete candidate).mpr bound
    rw [entries] at found
    exact List.mem_singleton.mp found
  intro path bound
  exact (unique path bound).trans (unique _ links.canonical).symm

/-- The keeper path does not name this sealed inode in the same map.
The exclusion requires no existence report for the keeper binding. -/
theorem WalSealedInodeLinks.keeperEntryNotThisInode {directory first inode metadata lstat reached}
    (links : WalSealedInodeLinks directory first inode metadata lstat reached)
    (privateSeal : metadata.numLinks = 1) {keeper : Nat} (different : first ≠ keeper) :
    links.entry (directory.file (.walSegment keeper)) ≠ some inode := by
  intro found
  have samePath := links.entryOnlyCanonical privateSeal _ found
  exact different (directory.walSegment_path_injective samePath).symm

theorem WalSealedInodeLinks.noLinks {directory first inode metadata lstat reached}
    (links : WalSealedInodeLinks directory first inode metadata lstat reached)
    (privateSeal : metadata.numLinks = 1) (missing : reached.DurablyAbsent first) :
    (∀ path, links.visible path ≠ some inode) ∧
    ∀ bindings ∈ links.crashImages, ∀ path, bindings path ≠ some inode := by
  have sole := links.entryOnlyCanonical privateSeal
  refine ⟨?_, ?_⟩
  · intro path present
    have selected : path = directory.file (.walSegment first) := sole path (links.visibleFrame path present)
    exact missing.1 (links.visibleProjects (selected ▸ present))
  · intro bindings observed path present
    obtain ⟨sealed, survived, frame, projects⟩ := links.crashProjects bindings observed
    have selected : path = directory.file (.walSegment first) := sole path (frame path present)
    exact missing.2 sealed survived (projects (selected ▸ present))

/-- In the observed drop interval, every slot referring to the selected
inode has a reported drop. Outside references, such as file mappings or
other kernel references, need a separate complete observation at the end. -/
structure WalSealedInodeReferences (inode : Nat) where
  inventory : DescriptorInventory
  drops : List LockReferenceDrop
  covered : ∀ slot ∈ inventory.slots, inventory.inode slot.description = inode →
    ∃ event ∈ drops, event.removes slot.reference = true
  outside : List Nat

def WalSealedInodeReferences.referenced {inode : Nat} (refs : WalSealedInodeReferences inode) : Prop :=
  (∃ slot ∈ (refs.inventory.afterDrops refs.drops).slots,
    refs.inventory.inode slot.description = inode) ∨ refs.outside ≠ []

theorem WalSealedInodeReferences.noSlots {inode : Nat} (refs : WalSealedInodeReferences inode) :
    ∀ slot ∈ (refs.inventory.afterDrops refs.drops).slots,
      (refs.inventory.afterDrops refs.drops).inode slot.description ≠ inode := by
  intro slot alive same
  obtain ⟨present, survived⟩ := List.mem_filter.mp alive
  obtain ⟨event, occurred, removed⟩ := refs.covered slot present same
  have kept := List.all_eq_true.mp survived event occurred
  simp [removed] at kept

/-- A selected sealed WAL inode loses every observed name once the
actual unlink prefix reaches a reported effective barrier. The same held
inventory's no-follow probe supplies the one-link guard. A complete
reference census then isolates any remaining references outside slots.
This gives no filesystem allocation or block-release assertion. -/
theorem SegmentedCollectionReport.selectedSealInodeAfterBarrier {directory : DiskDirectory}
    {before : SegmentedWriterState} (report : SegmentedCollectionReport directory before)
    {descriptor : Nat} (ready : before.RetainedReady directory descriptor)
    {tail : ByteArray} (raw : HealthyBoundedWalReports directory before.owners descriptor before.wal before.target.pair
      before.target.range.watermark before.published.durable tail)
    (physical : ∀ segment ∈ before.wal.sealed, ∀ metadata,
      raw.reports.lstat (directory.file (.walSegment segment.first)) = .ok metadata →
        metadata.byteSize.toNat = segment.bytes.size)
    (planned : (raw.reports.walSegmentOffsets directory (raw.entries.toList.map (·.fileName))).map
      (fun offsets => raw.reports.walCollectionOffsets directory offsets before.installed.activeFirst
        before.target.pair) = .ok report.offsets)
    {first inode : Nat} (selected : first ∈ report.offsets)
    {metadata : IO.FS.Metadata} {atBarrier : WalSealedUnlinkImage}
    (links : WalSealedInodeLinks directory first inode metadata raw.reports.lstat atBarrier.syncDirectory)
    (refs : WalSealedInodeReferences inode) :
    let perform := WalSealedUnlinkImage.performPaths directory report.removeFile report.syncDirectory
    ((report.offsets.map RunCollection.Step.unlink).forM perform) (.start before.wal) = .ok () atBarrier →
    (perform .syncDirectory atBarrier = .ok () atBarrier.syncDirectory ∨
      ∃ cause, perform .syncDirectory atBarrier = .error cause atBarrier.syncDirectory) →
    report.offsets = before.wal.collectionOffsets ∧ first ≠ before.wal.active.first ∧
    links.entry (directory.file (.walSegment before.wal.active.first)) ≠ some inode ∧
    atBarrier.syncDirectory.DurablyAbsent first ∧
    (∀ path, links.visible path ≠ some inode) ∧
    (∀ bindings ∈ links.crashImages, ∀ path, bindings path ≠ some inode) ∧
    (∀ slot ∈ (refs.inventory.afterDrops refs.drops).slots,
      (refs.inventory.afterDrops refs.drops).inode slot.description ≠ inode) ∧
    (refs.referenced ↔ refs.outside ≠ []) ∧
    (report.run = .ok () atBarrier.syncDirectory ∨
      ∃ cause, report.run = .error cause atBarrier.syncDirectory) := by
  intro perform unlinked effective
  have exactPlan := Except.ok.inj (planned.symm.trans (ready.collectionOffsets_exact .start raw physical))
  have approved := report.approved first selected
  obtain ⟨⟨segment, member, atOffset⟩, allowed⟩ := ready.layout.collectionOffsets_approved approved
  have notActive : first ≠ before.wal.active.first := atOffset ▸ (allowed segment member atOffset).notActive
  obtain ⟨_, _, seen, _, privateSeal⟩ := WalSegmentImage.collectionOffsets_observed raw approved
  have looked : raw.reports.lstat (directory.file (.walSegment first)) = .ok metadata := by
    rw [links.projected, links.identified]
    rfl
  cases Except.ok.inj (looked.symm.trans seen)
  obtain ⟨returned, absent⟩ := report.reclaimsAtEffectiveBarrier (.inl selected) unlinked effective
  obtain ⟨visible, crashes⟩ := links.noLinks privateSeal absent
  refine ⟨exactPlan, notActive, links.keeperEntryNotThisInode privateSeal notActive,
    absent, visible, crashes, refs.noSlots, ?_, returned⟩
  constructor
  · rintro (⟨slot, alive, same⟩ | outside)
    · exact False.elim (refs.noSlots slot alive same)
    · exact outside
  · exact Or.inr

end Alvoki.Storage.DiskSession
