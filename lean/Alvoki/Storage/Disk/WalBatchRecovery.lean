import Alvoki.Storage.Disk.WalBatchCommitEffects
import Alvoki.Storage.Disk.WalSegmentFirstReplay

namespace Alvoki.Storage

open WAL

/-- Once the surviving marker has selected the old or complete history, exact
sealed spans and the keeper prefix replay to the corresponding table. Pins
from the original writer need not survive reopening. -/
theorem replayPreparedBatchSelection {base prior live next : PackedTable}
    {covered acknowledged batch selected : List Write} {rows : List (UInt64 × Option UInt64)}
    {first : Nat} {sealed : List WalSegment} {keeper : WalSegment} {count : UInt64}
    (checkpointCount : covered.length = base.committed.toNat)
    (previous : replay base acknowledged = .ok prior) (same : prior.SameData live)
    (ordered : OrdinalsFrom 1 (covered ++ acknowledged))
    (committed : (covered ++ acknowledged).length = live.committed.toNat)
    (prepared : prepareBatch live rows = some (batch, next))
    (choice : selected = covered ++ acknowledged ∨ selected = (covered ++ acknowledged) ++ batch)
    (chain : WalSegment.Chain selected first (sealed ++ [keeper])) (tail : ByteArray)
    (marker : count.toNat = selected.length * frameSize) (covers : first ≤ base.committed.toNat) :
    ∃ recovered,
      recoverMarkedWalSegments base count
        (sealed.map (fun segment => (segment.first, segment.bytes)) ++ [(keeper.first, keeper.bytes ++ tail)]) =
        .ok (WAL.encode (selected.drop first), recovered) ∧
      ((selected = covered ++ acknowledged ∧ recovered.SameData live) ∨
        (selected = (covered ++ acknowledged) ++ batch ∧ recovered.SameData next)) := by
  rcases choice with rfl | rfl
  · have logical := (recoverSelected_encoded base covered acknowledged ordered checkpointCount).trans previous
    exact ⟨prior, chain.replaysMarked tail marker covers ordered logical, .inl ⟨rfl, same⟩⟩
  · have numbered := (prepareBatch_extends_history ordered committed prepared).2.1
    obtain ⟨recovered, applied, recoveredSame⟩ :=
      replay_sameData same batch (prepareBatch_spec prepared).2.1
    have logical : recoverSelected base (WAL.encode ((covered ++ acknowledged) ++ batch)) = .ok recovered := by
      rw [List.append_assoc, recoverSelected_encoded base covered (acknowledged ++ batch)
        (by simpa only [List.append_assoc] using numbered) checkpointCount,
        replay_append previous]
      exact applied
    exact ⟨recovered, chain.replaysMarked tail marker covers numbered logical, .inr ⟨rfl, recoveredSame⟩⟩

end Alvoki.Storage
