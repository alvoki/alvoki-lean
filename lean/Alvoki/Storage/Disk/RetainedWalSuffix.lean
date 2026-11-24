import Alvoki.Storage.Disk.CheckpointHistory

namespace Alvoki.Storage

open Sequential (SnapshotTable)
open WAL (Write frameSize)

/-- Recover after physically removing `removedThrough` frames. Validate the
retained frames at their original positions before dropping frames already
represented by the checkpoint. The caller supplies a selected byte range
and a cutoff at or below the loaded checkpoint's watermark. -/
def recoverRetainedFrom (base : PackedTable) (removedThrough : Nat) (retained : ByteArray) :
    Except String PackedTable := do
  let events ← WAL.decodeOrdinalsFrom (removedThrough + 1) retained
  let table ← replay base (events.drop (base.committed.toNat - removedThrough))
  if table.committed.toNat == removedThrough + retained.size / frameSize then .ok table
  else .error "selected WAL frame count disagrees with the recovered sequence"

/-- Recover when every frame in the retained bytes is above the checkpoint
watermark. -/
def recoverRetainedSuffix (base : PackedTable) (retained : ByteArray) : Except String PackedTable :=
  recoverRetainedFrom base base.committed.toNat retained

/-- The physical and logical replay offsets can differ. With validated,
frame-aligned removed bytes, the original and retained workers return the
same table or error. This includes malformed retained frames at or below
the checkpoint sequence and preserves the existing short-tail behavior. -/
theorem recoverRetainedFrom_eq_recoverSelected (base : PackedTable)
    {removed : List Write} {prefixBytes : ByteArray} (retained : ByteArray)
    (validated : WAL.decodeOrdinals prefixBytes = .ok removed)
    (aligned : prefixBytes.size % frameSize = 0) (covered : removed.length ≤ base.committed.toNat) :
    recoverRetainedFrom base removed.length retained = recoverSelected base (prefixBytes ++ retained) := by
  have whole : prefixBytes.size / frameSize * frameSize = prefixBytes.size := by
    have splitBytes := Nat.mod_add_div prefixBytes.size frameSize
    simpa [aligned, Nat.mul_comm] using splitBytes
  have prefixExact := WAL.decodeOrdinals_reencode validated
  rw [whole, ByteArray.extract_zero_size] at prefixExact
  have count : (WAL.encode removed ++ retained).size / frameSize =
      removed.length + retained.size / frameSize := by
    rw [ByteArray.size_append, WAL.encode_size, Nat.mul_add_div (by decide : 0 < frameSize)]
  rw [← prefixExact, recoverSelected, WAL.decodeOrdinals_append_encoded removed retained
    (WAL.decodeOrdinals_sound validated), count, recoverRetainedFrom]
  cases decoded : WAL.decodeOrdinalsFrom (removed.length + 1) retained with
  | error => rfl
  | ok events =>
    have dropCovered : (removed ++ events).drop base.committed.toNat =
        events.drop (base.committed.toNat - removed.length) := by
      rw [List.drop_append, List.drop_eq_nil_iff.mpr covered, List.nil_append]
    change (do
      let table ← replay base (events.drop (base.committed.toNat - removed.length))
      if table.committed.toNat == removed.length + retained.size / frameSize then
        Except.ok table else Except.error _) =
      (do
        let table ← replay base ((removed ++ events).drop base.committed.toNat)
        if table.committed.toNat == removed.length + retained.size / frameSize then
          Except.ok table else Except.error _)
    rw [dropCovered]

/-- At the checkpoint's exact watermark, the retained worker simply
decodes and replays all retained frames. -/
theorem recoverRetainedSuffix_eq_recoverSelected (base : PackedTable)
    {covered : List Write} {prefixBytes : ByteArray} (retained : ByteArray)
    (validated : WAL.decodeOrdinals prefixBytes = .ok covered)
    (aligned : prefixBytes.size % frameSize = 0) (watermark : covered.length = base.committed.toNat) :
    recoverRetainedSuffix base retained = recoverSelected base (prefixBytes ++ retained) := by
  simpa only [recoverRetainedSuffix, watermark] using
    recoverRetainedFrom_eq_recoverSelected base retained validated aligned (Nat.le_of_eq watermark)

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

/-- The checkpoint can cover both removed frames and complete frames
still physically retained. Recovery validates both the retained covered
frames and the suffix, and the resulting table represents the full
original history. -/
theorem recoverRetainedFrom_refines {base : PackedTable} {model : SnapshotTable UInt64}
    {removed stillCovered suffix : List Write} {retained : ByteArray}
    (refines : base.Refines model) (represents : RepresentsWalHistory (removed ++ stillCovered) model)
    (numbered : WAL.OrdinalsFrom (base.committed.toNat + 1) suffix)
    (exactRetained : retained = WAL.encode (stillCovered ++ suffix)) :
    ∃ table abstract,
      recoverRetainedFrom base removed.length retained = .ok table ∧
      recoverSelected base (WAL.encode ((removed ++ stillCovered) ++ suffix)) = .ok table ∧
      table.Refines abstract ∧ RepresentsWalHistory ((removed ++ stillCovered) ++ suffix) abstract ∧
      table.committed.toNat = (removed ++ stillCovered).length + suffix.length := by
  have cutoff : removed.length ≤ base.committed.toNat := by
    rw [refines.committed, represents.committed_count, List.length_append]
    exact Nat.le_add_right _ _
  have numberedRemoved : WAL.OrdinalsFrom 1 removed := by
    obtain ⟨_, history, _⟩ := represents
    obtain ⟨_, played, _⟩ := history.split
    exact played.ordinals
  obtain ⟨table, abstract, _, recoveredFull, refined, fullHistory, count⟩ :=
    recoverRetainedSuffix_refines refines represents numbered (retained := WAL.encode suffix) rfl
  have same := recoverRetainedFrom_eq_recoverSelected base retained
    (WAL.decodeOrdinals_encode removed numberedRemoved) (by simp) cutoff
  have recovered : recoverRetainedFrom base removed.length retained = .ok table := by
    rw [same, exactRetained, ← WAL.encode_append, ← List.append_assoc]
    exact recoveredFull
  exact ⟨table, abstract, recovered, recoveredFull, refined, fullHistory, count⟩

end Alvoki.Storage
