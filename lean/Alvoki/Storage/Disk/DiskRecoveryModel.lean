import Alvoki.Storage.Disk.DiskTable
import Alvoki.Storage.Disk.WalBoundaryModel

namespace Alvoki.Storage
open Alvoki.Compaction (CheckedRun)

/-- A selected manifest and its exact ordered run bytes describe a flushed
checkpoint. An absent manifest uses the same empty base as the Linux adapter. -/
inductive CheckpointForRecovery : Option ByteArray → List ByteArray → PackedTable → Prop where
  | absent : CheckpointForRecovery none [] .empty
  | written (header : Manifest.Checkpoint) (checkpoint : PackedTable)
      (flushed : checkpoint.memory = Alvoki.Sequential.History.empty)
      (count : checkpoint.runs.length = header.runCount.toNat)
      (watermark : header.committed = checkpoint.committed)
      (floor : header.floor = checkpoint.pins.floor)
      (validFloor : header.floor ≤ header.committed)
      (bounded : ∀ run ∈ checkpoint.runs, ∀ row ∈ run.history.rows, row.sequence ≤ header.committed) :
      CheckpointForRecovery (some (Manifest.encode header))
        (checkpoint.runs.map (·.run.bytes)) checkpoint

theorem CheckpointForRecovery.loads {manifest : Option ByteArray} {files : List ByteArray}
    {checkpoint : PackedTable} (written : CheckpointForRecovery manifest files checkpoint) :
    ∃ base, (match manifest with
      | none => Except.ok PackedTable.empty
      | some bytes => do
        let header ← Manifest.decode bytes
        loadRunSet header files) = .ok base ∧ base.SameData checkpoint := by
  cases written with
  | absent => exact ⟨.empty, rfl, ⟨rfl, rfl, rfl, rfl⟩⟩
  | written header checkpoint flushed count watermark floor validFloor bounded =>
    obtain ⟨base, loaded, restored⟩ := loadRunSet_written header checkpoint.runs count validFloor bounded
    rw [watermark, floor] at restored
    refine ⟨base, ?_, PackedTable.restore_sameData flushed restored⟩
    change (do
      let decoded ← Manifest.decode (Manifest.encode header)
      loadRunSet decoded (checkpoint.runs.map fun run : CheckedRun => run.run.bytes)) = .ok base
    rw [Manifest.decode_encode header validFloor]
    exact loaded

private theorem ordinals_prefix {first : Nat} {initial suffix : List WAL.Write}
    (ordered : WAL.OrdinalsFrom first (initial ++ suffix)) : WAL.OrdinalsFrom first initial := by
  induction initial generalizing first with
  | nil => trivial
  | cons event rest ih => exact ⟨ordered.1, ih ordered.2⟩

/-- For a supplied manifest and marker pair, the production loader, selector
and replay recover the old or extended history. The reference replays from
the original checkpoint and may have a different pin registry. A trace
invariant must establish that the checkpoint represents the covered prefix. -/
theorem recoverWriteCutSelectedPair {manifest marker : Option ByteArray} {files : List ByteArray}
    {checkpoint : PackedTable} {covered pending : List WAL.Write}
    {event : WAL.Write} {wal : ByteArray} {image : Publication.Image}
    (written : CheckpointForRecovery manifest files checkpoint)
    (cut : WAL.Boundary.WriteCut (covered ++ pending) event wal image)
    (chosen : marker = image.active ∨ marker ∈ image.crashImages)
    (oldFits : (WAL.encode (covered ++ pending)).size < UInt64.size)
    (newFits : (WAL.encode ((covered ++ pending) ++ [event])).size < UInt64.size)
    (ordered : WAL.OrdinalsFrom 1 ((covered ++ pending) ++ [event]))
    (watermark : covered.length = checkpoint.committed.toNat) :
    ∃ markerBytes events base reopened reference, marker = some markerBytes ∧
      (match manifest with
      | none => Except.ok PackedTable.empty
      | some bytes => do
        let header ← Manifest.decode bytes
        loadRunSet header files) = .ok base ∧
      (do
        let count ← WAL.Boundary.decode markerBytes
        WAL.Boundary.select count wal) = .ok (WAL.encode events) ∧
      recoverSelected base (WAL.encode events) = .ok reopened ∧
      (events = covered ++ pending ∨ events = (covered ++ pending) ++ [event]) ∧
      reopened.committed.toNat = events.length ∧
      replay checkpoint (events.drop covered.length) = .ok reference ∧
      reference.SameData reopened := by
  obtain ⟨base, loaded, same⟩ := written.loads
  obtain ⟨markerBytes, events, bound, history, selected⟩ :=
    WAL.Boundary.write_cut_selects_old_or_new cut oldFits newFits chosen
  have recoverSuffix (suffix : List WAL.Write) (ordinals : WAL.OrdinalsFrom 1 (covered ++ suffix)) :
      ∃ reopened reference, recoverSelected base (WAL.encode (covered ++ suffix)) = .ok reopened ∧
        reopened.committed.toNat = (covered ++ suffix).length ∧
        replay checkpoint suffix = .ok reference ∧ reference.SameData reopened := by
    have count : covered.length = base.committed.toNat := by simpa only [same.committed] using watermark
    obtain ⟨reopened, recovered, sequence⟩ := recoverSelected_encoded_complete base covered suffix ordinals count
    have replayed := (recoverSelected_encoded base covered suffix ordinals count).symm.trans recovered
    have sameBase : checkpoint.SameData base :=
      ⟨same.runs.symm, same.memory.symm, same.committed.symm, same.floor.symm⟩
    obtain ⟨reference, expected, agrees⟩ := replay_sameData sameBase suffix replayed
    exact ⟨reopened, reference, recovered, by simpa only [List.length_append] using sequence,
      expected, agrees⟩
  rcases history with rfl | rfl
  · obtain ⟨reopened, reference, recovered, sequence, expected, agrees⟩ :=
      recoverSuffix pending (ordinals_prefix ordered)
    exact ⟨markerBytes, covered ++ pending, base, reopened, reference, bound, loaded, selected,
      recovered, Or.inl rfl, sequence, by simpa only [List.drop_left] using expected, agrees⟩
  · have ordinals : WAL.OrdinalsFrom 1 (covered ++ (pending ++ [event])) := by
      simpa only [List.append_assoc] using ordered
    obtain ⟨reopened, reference, recovered, sequence, expected, agrees⟩ :=
      recoverSuffix (pending ++ [event]) ordinals
    refine ⟨markerBytes, (covered ++ pending) ++ [event], base, reopened, reference, bound,
      loaded, selected, ?_, Or.inr rfl, ?_, ?_, agrees⟩
    · simpa only [List.append_assoc] using recovered
    · simpa only [List.append_assoc] using sequence
    · simpa only [List.append_assoc, List.drop_left] using expected

end Alvoki.Storage
