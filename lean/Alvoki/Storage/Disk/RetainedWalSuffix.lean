import Alvoki.Storage.Disk.CheckpointHistory

namespace Alvoki.Storage

open Sequential (SnapshotTable)
open WAL (Write frameSize)

/-- A candidate recovery worker for physically retained WAL data.
The loaded checkpoint supplies the absolute starting ordinal. The caller
must select the retained byte range using a durable boundary. -/
def recoverRetainedSuffix (base : PackedTable) (retained : ByteArray) : Except String PackedTable := do
  let events ← WAL.decodeOrdinalsFrom (base.committed.toNat + 1) retained
  let table ← replay base events
  if table.committed.toNat == base.committed.toNat + retained.size / frameSize then .ok table
  else .error "selected WAL frame count disagrees with the recovered sequence"

/-- The production worker on the original WAL and the suffix worker on the
same retained bytes have the same result. The removed bytes must already
have passed the complete-frame checks and end at the checkpoint watermark.
Errors in either worker's retained input propagate through this equality. -/
theorem recoverRetainedSuffix_eq_recoverSelected (base : PackedTable)
    {covered : List Write} {prefixBytes : ByteArray} (retained : ByteArray)
    (validated : WAL.decodeOrdinals prefixBytes = .ok covered)
    (aligned : prefixBytes.size % frameSize = 0) (watermark : covered.length = base.committed.toNat) :
    recoverRetainedSuffix base retained = recoverSelected base (prefixBytes ++ retained) := by
  have whole : prefixBytes.size / frameSize * frameSize = prefixBytes.size := by
    have splitBytes := Nat.mod_add_div prefixBytes.size frameSize
    simpa [aligned, Nat.mul_comm] using splitBytes
  have prefixExact := WAL.decodeOrdinals_reencode validated
  rw [whole, ByteArray.extract_zero_size] at prefixExact
  have count : (WAL.encode covered ++ retained).size / frameSize =
      base.committed.toNat + retained.size / frameSize := by
    rw [ByteArray.size_append, WAL.encode_size, ← watermark, Nat.mul_add_div (by decide : 0 < frameSize)]
  rw [← prefixExact, recoverSelected, WAL.decodeOrdinals_append_encoded covered retained
    (WAL.decodeOrdinals_sound validated), watermark, count, recoverRetainedSuffix]
  cases decoded : WAL.decodeOrdinalsFrom (base.committed.toNat + 1) retained with
  | error => rfl
  | ok events =>
    change (do
      let table ← replay base events
      if table.committed.toNat == base.committed.toNat + retained.size / frameSize then
        Except.ok table else Except.error _) =
      (do
        let table ← replay base ((covered ++ events).drop base.committed.toNat)
        if table.committed.toNat == base.committed.toNat + retained.size / frameSize then
          Except.ok table else Except.error _)
    rw [← watermark, List.drop_left]

/-- A physically retained exact suffix still represents the full original
history when the loaded checkpoint represents its removed prefix. The
packed result is exactly what production full-WAL recovery would return
with that same loaded checkpoint. -/
theorem recoverRetainedSuffix_refines {base : PackedTable} {model : SnapshotTable UInt64}
    {covered suffix : List Write} {retained : ByteArray}
    (refines : base.Refines model) (represents : RepresentsWalHistory covered model)
    (numbered : WAL.OrdinalsFrom (base.committed.toNat + 1) suffix)
    (exactRetained : retained = WAL.encode suffix) :
    ∃ table abstract,
      recoverRetainedSuffix base retained = .ok table ∧
      recoverSelected base (WAL.encode (covered ++ suffix)) = .ok table ∧
      table.Refines abstract ∧ RepresentsWalHistory (covered ++ suffix) abstract ∧
      table.committed.toNat = covered.length + suffix.length := by
  have watermark : covered.length = base.committed.toNat := by
    rw [refines.committed, represents.committed_count]
  have orderedPrefix : WAL.OrdinalsFrom 1 covered := by
    obtain ⟨reference, replayed, _⟩ := represents
    exact replayed.ordinals
  obtain ⟨table, applied, count⟩ := replay_ordinals_complete base suffix numbered
  obtain ⟨abstract, replayed, refined⟩ := replay_refines refines applied
  have fullHistory := represents.append replayed
  have orderedHistory : WAL.OrdinalsFrom 1 (covered ++ suffix) := by
    obtain ⟨reference, replayed, _⟩ := fullHistory
    exact replayed.ordinals
  have recoveredFull : recoverSelected base (WAL.encode (covered ++ suffix)) = .ok table :=
    (recoverSelected_encoded base covered suffix orderedHistory watermark).trans applied
  have same := recoverRetainedSuffix_eq_recoverSelected base retained
    (WAL.decodeOrdinals_encode covered orderedPrefix) (by simp) watermark
  have recovered : recoverRetainedSuffix base retained = .ok table := by
    rw [same, exactRetained, ← WAL.encode_append]
    exact recoveredFull
  exact ⟨table, abstract, recovered, recoveredFull, refined, fullHistory, by rwa [watermark]⟩

end Alvoki.Storage
