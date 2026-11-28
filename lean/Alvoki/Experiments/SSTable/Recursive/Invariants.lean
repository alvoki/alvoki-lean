import Alvoki.Experiments.SSTable.Recursive.Builder

namespace ImmutableSSTable.Recursive

open Unified (Ref checksumSize indexEntrySize)

/-- Every followed edge uses a nonempty, bounded extent strictly earlier
than its parent. In particular, repeating an offset would be impossible. -/
theorem checkedChild_bounds (child : Ref) (parent limit : Nat)
    (accepted : checkedChild child parent limit = .ok ()) :
    child.offset < parent ∧ child.size ≤ limit ∧ child.offset + child.size ≤ parent := by
  unfold checkedChild at accepted
  split at accepted
  · rename_i bounds
    have positive : 0 < child.size := by
      have := bounds.1
      simp [checksumSize] at this
      omega
    exact ⟨by omega, bounds.2⟩
  · contradiction

theorem checkedChild_chunks (child : Ref) (parent : Nat)
    (accepted : checkedChild child parent maxIndexSize = .ok ())
    (large : maxRowSize < child.size) :
    child.offset + maxRowSize < parent ∧
    child.size - maxRowSize ≤ maxRowSize ∧
    child.offset + maxRowSize + (child.size - maxRowSize) ≤ parent := by
  obtain ⟨_, bound, extent⟩ := checkedChild_bounds child parent maxIndexSize accepted
  unfold maxIndexSize at bound
  omega

theorem Page.flush_has_two (page : Page) (ref : Ref) (target : Nat)
    (flush : page.shouldFlush ref target = true) : 2 ≤ page.refs.size := by
  simpa [Page.shouldFlush] using (Bool.and_eq_true_iff.mp flush).1

theorem Page.pair_fits (left right : Ref)
    (leftFits : indexEntrySize left.lastKey + checksumSize ≤ maxRowSize)
    (rightFits : indexEntrySize right.lastKey + checksumSize ≤ maxRowSize) :
    ((Page.add (Page.add {} left) right).bytes + checksumSize) ≤ maxIndexSize := by
  simp only [Page.add, maxIndexSize]
  omega

/-- If every regular promotion consumes two children and only the final page
can be a singleton, a level with at least two children shrinks. -/
theorem fringe_shrinks (children regular fringe : Nat)
    (nontrivial : 2 ≤ children) (singleFringe : fringe ≤ 1)
    (covers : 2 * regular + fringe ≤ children) :
    regular + fringe < children := by
  omega

end ImmutableSSTable.Recursive
