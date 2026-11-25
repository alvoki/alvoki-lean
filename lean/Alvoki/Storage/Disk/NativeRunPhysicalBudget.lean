import Alvoki.Storage.Disk.NativeObsoleteRunReleaseBudget

namespace Alvoki.Storage.DiskSession

open CheckpointPublication

/-- A finite set of block identifiers and two allocation observations
in its common block pool. The set can be any scoped subset supplied
by the observer. -/
structure BlockPoolObservation where
  blocks : List Nat
  distinct : blocks.Nodup
  before : Nat → Bool
  after : Nat → Bool

namespace BlockPoolObservation

def occupiedBefore (pool : BlockPoolObservation) : Nat :=
  (pool.blocks.filter pool.before).length

def occupiedAfter (pool : BlockPoolObservation) : Nat :=
  (pool.blocks.filter pool.after).length

def allocated (pool : BlockPoolObservation) : List Nat :=
  pool.blocks.filter (fun block => pool.after block && !pool.before block)

def freed (pool : BlockPoolObservation) : List Nat :=
  pool.blocks.filter (fun block => pool.before block && !pool.after block)

/-- The two observed footprints differ by allocation and release in
this exact block set. Blocks occupied in both snapshots cancel. -/
theorem balances (pool : BlockPoolObservation) :
    pool.occupiedAfter + pool.freed.length = pool.occupiedBefore + pool.allocated.length := by
  simp only [occupiedBefore, occupiedAfter, freed, allocated]
  induction pool.blocks with
  | nil => rfl
  | cons block rest ih =>
    cases before : pool.before block <;>
      cases after : pool.after block <;>
      simp only [List.filter_cons, before, after, Bool.and_false, Bool.and_true,
        Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, List.length_cons] <;>
      omega

end BlockPoolObservation

variable {state : NativeReadyState} {image : Type}
  {attempt : SegmentedCheckpointReport state.session.directory state.writer}
  {reports : CheckpointCompletionReports (CensusDirectoryCache × image) attempt}
  {checkpoint : NativeReadyCheckpoint state reports} {writer : SegmentedWriterState} {held : List UInt64}

/-- The certified releases of this same completed collector contribute
to the observed footprint balance. A block counts at most once. If new
allocations cost at most the certified releases, any initial byte
budget is preserved at the final observation. -/
theorem CheckpointRunCollectionReports.boundsFinalFootprint
    (seen : CheckpointRunCollectionReports checkpoint writer held) (completed : checkpoint.Completed writer)
    (observations : List (ObsoleteRunEvictionObservation seen)) (pool : BlockPoolObservation) (bytesPerBlock : Nat)
    (includes : ∀ observation ∈ observations, ∀ block ∈ observation.blocks, block ∈ pool.blocks)
    (projects : ∀ observation ∈ observations, ∀ block ∈ observation.blocks,
      (observation.eviction.allocatedBefore block ↔ pool.before block = true) ∧
      (observation.eviction.allocatedAfter block ↔ pool.after block = true))
    (unique : ∀ observation ∈ observations, observation.blocks.Nodup)
    (disjoint : observations.Pairwise (fun left right => ∀ block ∈ left.blocks, block ∉ right.blocks)) :
    let releasedBytes := (observations.map (fun observation => observation.blocks.length * bytesPerBlock)).sum
    pool.occupiedAfter * bytesPerBlock + releasedBytes ≤
      pool.occupiedBefore * bytesPerBlock + pool.allocated.length * bytesPerBlock ∧
    ∀ budget, pool.occupiedBefore * bytesPerBlock ≤ budget →
      pool.allocated.length * bytesPerBlock ≤ releasedBytes → pool.occupiedAfter * bytesPerBlock ≤ budget := by
  intro releasedBytes
  let certified := observations.flatMap (·.blocks)
  obtain ⟨distinct, released, bytes⟩ := seen.accountsReleasedBlocks completed observations bytesPerBlock
    (fun block => pool.before block = true) (fun block => pool.after block = true) projects unique disjoint
  have inFreed : certified ⊆ pool.freed := by
    intro block member
    obtain ⟨observation, present, known⟩ := List.mem_flatMap.mp member
    obtain ⟨occupied, vacant⟩ := released block member
    apply List.mem_filter.mpr
    exact ⟨includes observation present block known, by simp [occupied, Bool.eq_false_iff.mpr vacant]⟩
  have count := distinct.length_le_of_subset inFreed
  have releasedBound : releasedBytes ≤ pool.freed.length * bytesPerBlock := by
    rw [show releasedBytes = certified.length * bytesPerBlock from bytes.symm]
    exact Nat.mul_le_mul_right bytesPerBlock count
  have balance := congrArg (· * bytesPerBlock) pool.balances
  simp only [Nat.add_mul] at balance
  have bound : pool.occupiedAfter * bytesPerBlock + releasedBytes ≤
      pool.occupiedBefore * bytesPerBlock + pool.allocated.length * bytesPerBlock := by
    rw [← balance]
    exact Nat.add_le_add_left releasedBound _
  exact ⟨bound, fun budget initial net => by omega⟩

end Alvoki.Storage.DiskSession
