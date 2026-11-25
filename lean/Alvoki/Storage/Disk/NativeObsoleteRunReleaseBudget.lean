import Alvoki.Storage.Disk.NativeObsoleteRunBlockRelease

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication

variable {state : NativeReadyState} {image : Type}
  {attempt : SegmentedCheckpointReport state.session.directory state.writer}
  {reports : CheckpointCompletionReports (CensusDirectoryCache × image) attempt}
  {checkpoint : NativeReadyCheckpoint state reports} {writer : SegmentedWriterState} {held : List UInt64}
  {seen : CheckpointRunCollectionReports checkpoint writer held}

/-- One old inode observed through this same completed collector, the
last descriptor drop and its subsequent filesystem eviction. -/
structure ObsoleteRunEvictionObservation (seen : CheckpointRunCollectionReports checkpoint writer held) where
  address : RunAddress
  unlink : NativeObsoleteRunInodeReport seen.collector address
  census : unlink.LinkCensus
  entry : (seen.collector.pathObject ((checkpoint.next writer).census, seen.collector.initial) unlink.path).map
    seen.collector.lifetime.namespaceView.modelObject = checkpoint.bindings reports.observed.completed.2 unlink.path
  last : InodeLastObservedDrop unlink.inode seen.collector.toNativeObsoleteRunPass.returnCensus
  eviction : InodeBlockEviction unlink.inode census.links.visible census.links.crashImages last.after
  outsideCleared : eviction.outside = []

namespace ObsoleteRunEvictionObservation

abbrev blocks (observation : ObsoleteRunEvictionObservation seen) : List Nat :=
  observation.eviction.exclusiveBlocks

theorem releases (observation : ObsoleteRunEvictionObservation seen) (completed : checkpoint.Completed writer) :
    ∀ block ∈ observation.blocks,
      observation.eviction.ownersBefore block = [observation.unlink.inode] ∧
      observation.eviction.allocatedBefore block ∧ ¬observation.eviction.allocatedAfter block :=
  (seen.releasesObsoleteBlocks completed observation.unlink observation.census observation.entry observation.last
    observation.eviction observation.outsideCleared).2.2.2.2.2.2

end ObsoleteRunEvictionObservation

private theorem uniqueBlocks {α : Type} (blocks : α → List Nat) (observations : List α)
    (unique : ∀ observation ∈ observations, (blocks observation).Nodup)
    (disjoint : observations.Pairwise (fun left right => ∀ block ∈ blocks left, block ∉ blocks right)) :
    (observations.flatMap blocks).Nodup := by
  induction observations with
  | nil => exact List.nodup_nil
  | cons first rest ih =>
    obtain ⟨disjointHead, disjointTail⟩ := List.pairwise_cons.mp disjoint
    apply List.nodup_append.mpr
    refine ⟨unique first List.mem_cons_self, ih (fun observation member =>
      unique observation (List.mem_cons_of_mem _ member)) disjointTail, ?_⟩
    intro left inFirst right inRest same
    obtain ⟨observation, member, inBlocks⟩ := List.mem_flatMap.mp inRest
    exact disjointHead observation member left inFirst (same.symm ▸ inBlocks)

private theorem sumBlockBytes {α : Type} (blocks : α → List Nat) (observations : List α) (bytesPerBlock : Nat) :
    (observations.flatMap blocks).length * bytesPerBlock =
      (observations.map (fun observation => (blocks observation).length * bytesPerBlock)).sum := by
  induction observations with
  | nil => simp
  | cons first rest ih =>
    simp only [List.flatMap_cons, List.length_append, Nat.add_mul, List.map_cons, List.sum_cons, ih]

/-- Every listed block was allocated at the common initial observation
and is unallocated at the common final observation. Reports must use
the same block identifiers and project their allocation predicates at
these blocks. The unique union counts the exact bytes of this observed
subset when its allocation units have the reported common size. -/
theorem CheckpointRunCollectionReports.accountsReleasedBlocks
    (seen : CheckpointRunCollectionReports checkpoint writer held) (completed : checkpoint.Completed writer)
    (observations : List (ObsoleteRunEvictionObservation seen)) (bytesPerBlock : Nat)
    (allocatedBefore allocatedAfter : Nat → Prop)
    (projects : ∀ observation ∈ observations, ∀ block ∈ observation.blocks,
      (observation.eviction.allocatedBefore block ↔ allocatedBefore block) ∧
      (observation.eviction.allocatedAfter block ↔ allocatedAfter block))
    (unique : ∀ observation ∈ observations, observation.blocks.Nodup)
    (disjoint : observations.Pairwise (fun left right => ∀ block ∈ left.blocks, block ∉ right.blocks)) :
    let blocks := observations.flatMap (·.blocks)
    blocks.Nodup ∧
    (∀ block ∈ blocks, allocatedBefore block ∧ ¬allocatedAfter block) ∧
    blocks.length * bytesPerBlock =
      (observations.map (fun observation => observation.blocks.length * bytesPerBlock)).sum := by
  intro blocks
  refine ⟨uniqueBlocks _ observations unique disjoint, ?_, sumBlockBytes _ observations bytesPerBlock⟩
  intro block member
  obtain ⟨observation, included, inBlocks⟩ := List.mem_flatMap.mp member
  obtain ⟨_, occupied, released⟩ := observation.releases completed block inBlocks
  obtain ⟨before, after⟩ := projects observation included block inBlocks
  exact ⟨before.mp occupied, fun allocated => released (after.mpr allocated)⟩

/-- If the eviction observations cover every approved name that was
visible, their address list represents exactly the initially present
older unheld run set. The completed collector itself derives that a
present eligible address is in its actual checked unlink schedule. -/
theorem CheckpointRunCollectionReports.observesEligibleRuns
    (seen : CheckpointRunCollectionReports checkpoint writer held) (completed : checkpoint.Completed writer)
    (observations : List (ObsoleteRunEvictionObservation seen))
    (covered : ∀ address ∈ seen.collector.reports.selected,
      seen.collector.initial.visible address.1 address.2 ≠ none →
      address ∈ observations.map (·.address)) (address : RunAddress) :
    address ∈ observations.map (·.address) ↔
      seen.collector.initial.visible address.1 address.2 ≠ none ∧
      address.1 < writer.installed.generation ∧ address.1 ∉ held := by
  constructor
  · intro member
    obtain ⟨observation, _, same⟩ := List.mem_map.mp member
    subst address
    exact ⟨observation.unlink.member, observation.unlink.older, by simpa only [seen.holds] using observation.unlink.unheld⟩
  · intro eligible
    obtain ⟨visible, older, unheld⟩ := eligible
    obtain ⟨bytes, bound⟩ := Option.ne_none_iff_exists'.mp visible
    have notHeld : address.1 ∉ seen.collector.reports.held := by simpa only [seen.holds] using unheld
    obtain ⟨listed, regular⟩ := seen.collector.complete address.1 address.2 bytes bound older notHeld
    have chosen := (seen.collector.reclaims completed.valid).1 address.1 address.2
    exact covered address (chosen.mpr ⟨listed, older, notHeld, regular⟩) visible

end Alvoki.Storage.DiskSession
