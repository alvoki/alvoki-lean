import Alvoki.Storage.Disk.DescriptorInventory
import Alvoki.Storage.Disk.SegmentedRunCollection

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication

/-- Observed name bindings and the run byte map for the same filesystem
image. A surviving name of this inode was already present at entry.
If the canonical link remains, its immutable synced bytes are in the run map. -/
def RunInodeLinkProjection (entry : FilePath → Option Nat) (canonical : FilePath)
    (name : RunAddress) (inode : Nat) (bindings : FilePath → Option Nat) (files : RunFiles) : Prop :=
  (∀ path, bindings path = some inode → entry path = some inode) ∧
  (bindings canonical = some inode → files name.1 name.2 ≠ none)

/-- The inode of a selected run, its sole link at entry and the exact
visible and crash observations at the reached collection state. The name
maps cover all links to this inode, including any outside the run directory.
The inode identity is in the same stable domain as the descriptor census. -/
structure RunInodeLinkReports (canonical : FilePath) (name : RunAddress) (inode : Nat)
    (before reached : RunUnlinkImage) where
  entry : FilePath → Option Nat
  visible : FilePath → Option Nat
  crashImages : List (FilePath → Option Nat)
  entryBound : entry canonical = some inode
  entryRun : before.visible name.1 name.2 ≠ none
  onlyEntryLink : ∀ path, entry path = some inode → path = canonical
  visibleProjects : RunInodeLinkProjection entry canonical name inode visible reached.visible
  crashProjects : ∀ bindings ∈ crashImages,
    ∃ files ∈ reached.crashImages, RunInodeLinkProjection entry canonical name inode bindings files

/-- Durable absence of the sole name excludes every binding of that inode
from the matching visible and crash name maps. -/
theorem RunInodeLinkReports.noLinks {canonical : FilePath} {name : RunAddress} {inode : Nat}
    {before reached : RunUnlinkImage} (links : RunInodeLinkReports canonical name inode before reached)
    (absent : reached.DurablyAbsent name) :
    (∀ path, links.visible path ≠ some inode) ∧
    ∀ bindings ∈ links.crashImages, ∀ path, bindings path ≠ some inode := by
  have excludes (bindings : FilePath → Option Nat) (files : RunFiles)
      (projects : RunInodeLinkProjection links.entry canonical name inode bindings files)
      (missing : files name.1 name.2 = none) (path : FilePath) : bindings path ≠ some inode := by
    intro found
    have samePath := links.onlyEntryLink path (projects.1 path found)
    exact projects.2 (samePath ▸ found) missing
  refine ⟨excludes _ _ links.visibleProjects absent.1, ?_⟩
  intro bindings observed
  obtain ⟨files, survived, projects⟩ := links.crashProjects bindings observed
  exact excludes _ _ projects (absent.2 files survived)

/-- For a selected run, every observed slot referring to its inode must
have a matching drop by the reached state or be covered by a reported
hold. A held generation cannot be selected. This includes independent
open descriptions of the same inode as well as aliases of one description. -/
theorem SegmentedRunCollectionReports.selectedInodeSlotsDropped
    {directory : DiskDirectory} {state : SegmentedWriterState} {before : RunUnlinkImage} {descriptor : Nat}
    (reports : SegmentedRunCollectionReports directory state before) (ready : state.RetainedReady directory descriptor)
    {name : RunAddress} (selected : name ∈ reports.selected)
    (inventory : DescriptorInventory) (drops : List LockReferenceDrop) (inode : Nat)
    (covered : ∀ slot ∈ inventory.slots, inventory.inode slot.description = inode →
      (∃ event ∈ drops, event.removes slot.reference = true) ∨ name.1 ∈ reports.held) :
    ∀ slot ∈ (inventory.afterDrops drops).slots, (inventory.afterDrops drops).inode slot.description ≠ inode := by
  obtain ⟨generation, index⟩ := name
  have unheld := ((reports.selected_eligible ready).mp selected).2.2.1
  intro slot alive target
  change inventory.inode slot.description = inode at target
  obtain ⟨present, survives⟩ := List.mem_filter.mp alive
  obtain ⟨event, inDrops, removes⟩ := (covered slot present target).resolve_right unheld
  have kept := List.all_eq_true.mp survives event inDrops
  simp [removes] at kept

/-- Compose the exact reached run map of the collector with complete name
and descriptor observations for one selected inode. The conclusion covers
links and descriptor slots in these observations. -/
theorem SegmentedRunCollectionReports.selectedInodeNoLinksOrSlots
    {directory : DiskDirectory} {state : SegmentedWriterState} {before : RunUnlinkImage} {descriptor : Nat}
    (reports : SegmentedRunCollectionReports directory state before) (ready : state.RetainedReady directory descriptor)
    {name : RunAddress} (selected : name ∈ reports.selected)
    (absent : reports.reached.DurablyAbsent name)
    (inventory : DescriptorInventory) (drops : List LockReferenceDrop) (inode : Nat)
    (covered : ∀ slot ∈ inventory.slots, inventory.inode slot.description = inode →
      (∃ event ∈ drops, event.removes slot.reference = true) ∨ name.1 ∈ reports.held)
    (links : RunInodeLinkReports (directory.file (.run name.1 name.2)) name inode before reports.reached) :
    (∀ path, links.visible path ≠ some inode) ∧
    (∀ bindings ∈ links.crashImages, ∀ path, bindings path ≠ some inode) ∧
    ∀ slot ∈ (inventory.afterDrops drops).slots, (inventory.afterDrops drops).inode slot.description ≠ inode := by
  obtain ⟨visible, crashes⟩ := links.noLinks absent
  exact ⟨visible, crashes, reports.selectedInodeSlotsDropped ready selected inventory drops inode covered⟩

end Alvoki.Storage.DiskSession
