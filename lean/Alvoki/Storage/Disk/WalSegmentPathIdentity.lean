import Alvoki.Storage.Disk.WalSegmentCollection
import Alvoki.Storage.Disk.WalSegmentFileName

namespace Alvoki.Storage

private theorem WalSegment.Chain.start_le_of_mem {history : List WAL.Write} {first : Nat}
    {segments : List WalSegment} (chain : Chain history first segments) {segment : WalSegment}
    (member : segment ∈ segments) : first ≤ segment.first := by
  induction chain with
  | endOfHistory => simp at member
  | cons ordered _ _ _ tail =>
    rcases List.mem_cons.mp member with rfl | later
    · exact Nat.le_refl _
    · exact Nat.le_trans ordered (tail later)

/-- The optional empty active segment can follow only a nonempty sealed
segment. Thus even an empty active file owns a distinct absolute start. -/
theorem WalSegment.Chain.startsStrict {history : List WAL.Write} {first : Nat} {segments : List WalSegment}
    (chain : Chain history first segments) : segments.Pairwise (fun left right => left.first < right.first) := by
  induction chain with
  | endOfHistory => exact .nil
  | @cons segment _ ordered empty _ tail strict =>
    refine .cons (fun later member => ?_) strict
    have lower := tail.start_le_of_mem member
    have different : segment.first ≠ segment.last := fun same => by simp [empty same] at member
    exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_ne ordered different) lower

/-- The immutable chain assigns its segments distinct locked file paths. -/
theorem WalSegment.Chain.filesNodup {history : List WAL.Write} {first : Nat} {segments : List WalSegment}
    (chain : Chain history first segments) (dir : DiskDirectory) :
    (segments.map fun segment => dir.file (.walSegment segment.first)).Nodup := by
  apply List.pairwise_map.mpr
  exact chain.startsStrict.imp fun before same =>
    (Nat.ne_of_lt before) (dir.walSegment_path_injective same)

end Alvoki.Storage
