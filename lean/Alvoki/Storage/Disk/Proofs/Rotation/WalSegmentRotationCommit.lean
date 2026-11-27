import Alvoki.Storage.Disk.WalSegmentCommitEffects
import Alvoki.Storage.Disk.Proofs.Rotation.WalSegmentRotation

namespace Alvoki.Storage.WalSegmentRotation

open WAL.Boundary

/-- After a successful reported rotation at the current marker, the first
append starts in the durable empty segment at the absolute history end.
Every selected marker and segment survivor supplies the unchanged sealed
suffix followed by either zero bytes or the one submitted frame. -/
theorem Trace.firstCommitSelection {initial : WalSegmentImage} {history : List WAL.Write} {before after : State}
    (trace : Trace initial before) (plan : CanRotate initial history) (valid : initial.Valid history)
    {reports : Step → OperationResult} (rotated : before.run reports = .ok () after)
    (atMarker : ∃ range, before.metadata.active.walRange = some range ∧ range.through = history.length)
    (event : WAL.Write) (fits : (WAL.encode (history ++ [event])).size < UInt64.size)
    (effects : WriteEffects) :
    let visible := after.visible initial
    let scratch := after.metadata.staged .walBoundary
    let committed := (writeFilesAfter (runWriteEffects history event effects scratch)).reopenSegment
      visible.active.first history after.metadata.active.manifest
    ∃ range first,
      after.successor = .durable ∧
      after.metadata.crashImages = [after.metadata.active] ∧
      after.metadata.active.walRange = some range ∧ range.through = history.length ∧
      after.metadata.active.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64) ∧
      visible.active = ⟨history.length, history.length, ByteArray.empty⟩ ∧ first ≤ range.watermark ∧
      let sealed := WalSegment.concatenate (visible.sealed.filter fun segment => decide (range.watermark < segment.last))
      sealed = WAL.encode (history.drop first) ∧
      ∀ pair bytes, pair ∈ committed.directory.active :: committed.directory.crashImages →
        some bytes ∈ committed.wal.active :: committed.wal.crashImages →
        ∃ selected suffix,
          pair.manifest = after.metadata.active.manifest ∧
          pair.walBoundary = some (WAL.Boundary.encode (WAL.encode selected).size.toUInt64) ∧
          ((selected = history ∧ suffix = ByteArray.empty) ∨
            (selected = history ++ [event] ∧ suffix = WAL.encodeFrame event)) ∧
          selectRetained visible.active.first (WAL.encode selected).size.toUInt64 bytes = .ok suffix ∧
          sealed ++ suffix = WAL.encode (selected.drop first) := by
  intro visible scratch committed
  have ready := trace.readyForAppend plan valid rotated atMarker
  obtain ⟨range, current, through⟩ := ready.exactMarker
  obtain ⟨_, covered, marker, count, markerRead, decoded, absolute⟩ :=
    DirectoryPublication.Bindings.walRange_accounting current
  have oldMarker : after.metadata.active.walBoundary =
      some (WAL.Boundary.encode (WAL.encode history).size.toUInt64) := by
    have countExact : count.toNat = (WAL.encode history).size := by
      rw [absolute, through, WAL.encode_size, Nat.mul_comm]
    have markerExact := WAL.Boundary.decode_reencode decoded
    rw [markerRead, ← markerExact, ← countExact]
    change some (WAL.Boundary.encode count) = some (WAL.Boundary.encode (UInt64.ofNat count.toNat))
    rw [UInt64.ofNat_toNat]
  have metadata : visible.directory = after.metadata := by
    unfold visible State.visible
    split <;> rfl
  have selected : visible.Selects after.metadata.active := by
    simp [WalSegmentImage.Selects, metadata]
  obtain ⟨witness, first, same, starts, _, chain⟩ := ready.recoverable _ selected
  have sameRange := Option.some.inj (same.symm.trans current)
  subst witness
  let kept := visible.sealed.filter fun segment => decide (range.watermark < segment.last)
  have keptExact : WalSegment.concatenate kept = WAL.encode (history.drop first) := by
    have bytes := chain.concatenate_eq
    change WalSegment.concatenate (visible.afterWatermark range.watermark) = _ at bytes
    rw [WalSegmentImage.afterWatermark, List.filter_append, ready.emptyAtEnd] at bytes
    by_cases includesEnd : range.watermark < history.length <;>
      simpa [kept, includesEnd, WalSegment.concatenate_append_empty] using bytes
  refine ⟨range, first, ready.successorDurable, ready.directorySettled, current, through, oldMarker,
    ready.emptyAtEnd, starts, keptExact, ?_⟩
  intro pair bytes pairChosen bytesChosen
  have start : visible.active.first = history.length := congrArg WalSegment.first ready.emptyAtEnd
  dsimp only [committed] at pairChosen bytesChosen
  rw [start] at pairChosen bytesChosen ⊢
  obtain ⟨chosen, oldOrNew, manifest, boundary, selected⟩ :=
    WalSegmentCommit.selectSegment_atReportedCut (first := history.length) (Nat.le_refl _)
      event fits effects after.metadata.active.manifest scratch pair bytes pairChosen bytesChosen
  rcases oldOrNew with old | new
  · subst chosen
    refine ⟨history, ByteArray.empty, manifest, boundary, .inl ⟨rfl, rfl⟩, ?_, ?_⟩
    · simpa only [List.drop_length, WAL.encode] using selected
    · simpa only [ByteArray.append_empty] using keptExact
  · subst chosen
    refine ⟨history ++ [event], WAL.encodeFrame event, manifest, boundary, .inr ⟨rfl, rfl⟩, ?_, ?_⟩
    · simpa [List.drop_append_length, WAL.encode] using selected
    · have within : first ≤ history.length := Nat.le_trans starts (through ▸ covered)
      change WalSegment.concatenate kept ++ WAL.encodeFrame event = WAL.encode ((history ++ [event]).drop first)
      rw [List.drop_append_of_le_length within, WAL.encode_append, ← keptExact]
      simp [WAL.encode]

end Alvoki.Storage.WalSegmentRotation
