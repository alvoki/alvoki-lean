import Alvoki.Storage.Disk.Proofs.WAL.RetainedWalBoundary
import Alvoki.Storage.Disk.WAL.WalSegmentReplay

namespace Alvoki.Storage

open WAL (frameSize)

private def chargeReplayWrite (table : PackedTable) (event : WAL.Write) : EStateM String Nat PackedTable :=
  fun attempts => match replayWrite table event with
    | .ok next => .ok next (attempts + 1)
    | .error cause => .error cause (attempts + 1)

/-- Use the replay fold with one charge for each reached `replayWrite`,
including the attempt that returns an error. -/
def replayWithWork (base : PackedTable) (events : List WAL.Write) (before : Nat := 0) :
    Except String PackedTable × Nat :=
  match events.foldlM chargeReplayWrite base before with
  | .ok table attempts => (.ok table, attempts)
  | .error cause attempts => (.error cause, attempts)

theorem replayWithWork_spec (base : PackedTable) (events : List WAL.Write) (before : Nat) :
    let result := replayWithWork base events before
    result.1 = replay base events ∧ result.2 ≤ before + events.length ∧
      (∀ table, result.1 = .ok table → result.2 = before + events.length) := by
  induction events generalizing before base with
  | nil => simp [replayWithWork, replay, Pure.pure, EStateM.pure, Except.pure]
  | cons event rest ih =>
    dsimp only at ih ⊢
    cases applied : replayWrite base event with
    | error cause =>
      simp [replayWithWork, replay, chargeReplayWrite, applied, Bind.bind, Except.bind, EStateM.bind]
    | ok next =>
      simpa [replayWithWork, replay, chargeReplayWrite, applied, Bind.bind, Except.bind, EStateM.bind,
        Nat.add_assoc, Nat.add_comm 1 rest.length] using ih next (before + 1)

/-- A failure after an applied prefix charges its failing write and stops
before visiting the remaining events. -/
theorem replayWithWork_errorAfterPrefix {base current : PackedTable} {applied : List WAL.Write}
    (used : replay base applied = .ok current) {event : WAL.Write} {cause : String}
    (failed : replayWrite current event = .error cause) (remaining : List WAL.Write) (before : Nat) :
    replayWithWork base (applied ++ event :: remaining) before = (.error cause, before + applied.length + 1) := by
  obtain ⟨result, _, exactCount⟩ := replayWithWork_spec base applied before
  have success := result.trans used
  have reached := exactCount current success
  have appliedCount : applied.foldlM chargeReplayWrite base before = .ok current (before + applied.length) := by
    cases folded : applied.foldlM chargeReplayWrite base before with
    | error => simp [replayWithWork, folded] at success
    | ok next count =>
      simpa [replayWithWork, folded, Except.ok.injEq] using And.intro success reached
  simp [replayWithWork, List.foldlM_append, Bind.bind, EStateM.bind, appliedCount, chargeReplayWrite, failed]

/-- Interpret retained-WAL recovery with a replay counter. Decoder failure
stops before the first attempt. The final clock check keeps the reached count. -/
def recoverRetainedFromWithReplayWork (base : PackedTable) (first : Nat) (bytes : ByteArray) :
    Except String PackedTable × Nat :=
  match WAL.decodeOrdinalsFrom (first + 1) bytes with
  | .error cause => (.error cause, 0)
  | .ok events =>
    let (result, attempts) := replayWithWork base (events.drop (base.committed.toNat - first))
    let checked := result.bind fun table =>
      if table.committed.toNat == first + bytes.size / frameSize then .ok table
      else .error "selected WAL frame count disagrees with the recovered sequence"
    (checked, attempts)

/-- The count includes only replay attempts above the checkpoint watermark.
The decoder still validates the whole selected retained span. -/
theorem recoverRetainedFromWithReplayWork_spec (base : PackedTable) (first : Nat) (bytes : ByteArray) :
    let result := recoverRetainedFromWithReplayWork base first bytes
    let pending := first + bytes.size / frameSize - base.committed.toNat
    result.1 = recoverRetainedFrom base first bytes ∧ result.2 ≤ pending ∧
      (∀ table, result.1 = .ok table → result.2 = pending) := by
  dsimp only
  cases decoded : WAL.decodeOrdinalsFrom (first + 1) bytes with
  | error cause =>
    simp [recoverRetainedFromWithReplayWork, recoverRetainedFrom, decoded, Bind.bind, Except.bind]
  | ok events =>
    let pending := events.drop (base.committed.toNat - first)
    have length : pending.length ≤ first + bytes.size / frameSize - base.committed.toNat := by
      rw [List.length_drop, WAL.decodeOrdinalsFrom_length decoded]
      omega
    have bounded := replayWithWork_spec base pending 0
    cases replayed : replayWithWork base pending with
    | mk result attempts =>
      rw [replayed] at bounded
      obtain ⟨same, limit, exactCount⟩ := bounded
      dsimp only at same limit exactCount
      simp only [recoverRetainedFromWithReplayWork, recoverRetainedFrom, decoded,
        Bind.bind, Except.bind, ← show pending = events.drop (base.committed.toNat - first) from rfl,
        replayed, ← same, Nat.zero_add] at limit exactCount ⊢
      refine ⟨trivial, Nat.le_trans limit length, ?_⟩
      intro table accepted
      cases result with
      | error => contradiction
      | ok applied =>
        have clock : applied.committed.toNat = first + bytes.size / frameSize := by
          dsimp only at accepted
          split at accepted
          · rename_i matched
            exact beq_iff_eq.mp matched
          · contradiction
        have advanced := replay_committed_count pending same.symm
        rw [exactCount applied rfl]
        omega

/-- Count replay attempts after the shared marked worker's span and byte
selection. Both rejection stages stop before any replay. -/
def recoverMarkedWalSegmentsWithReplayWork (base : PackedTable) (length : UInt64)
    (files : List (Nat × ByteArray)) : Except String (ByteArray × PackedTable) × Nat :=
  match files with
  | [] => (recoverMarkedWalSegments base length files, 0)
  | (first, _) :: _ =>
    if checkSelectedWalSegmentSpans (length.toNat / frameSize) files then
      let clipped := (walSegmentPayloadBytes files).extract 0 (length.toNat - first * frameSize)
      match WAL.Boundary.selectRetained first length clipped with
      | .error cause => (.error cause, 0)
      | .ok selected =>
        let (result, attempts) := recoverRetainedFromWithReplayWork base first selected
        (result.map fun table => (selected, table), attempts)
    else (recoverMarkedWalSegments base length files, 0)

/-- The counted marked recovery returns the same selected bytes and table
or the same error. A healthy result replays exactly the writes above the
checkpoint watermark up to the marker. -/
theorem recoverMarkedWalSegmentsWithReplayWork_spec (base : PackedTable) (length : UInt64)
    (files : List (Nat × ByteArray)) :
    let result := recoverMarkedWalSegmentsWithReplayWork base length files
    let pending := length.toNat / frameSize - base.committed.toNat
    result.1 = recoverMarkedWalSegments base length files ∧ result.2 ≤ pending ∧
      (∀ output, result.1 = .ok output → result.2 = pending) := by
  dsimp only
  cases files with
  | nil => simp [recoverMarkedWalSegmentsWithReplayWork, recoverMarkedWalSegments]
  | cons file rest =>
    obtain ⟨first, bytes⟩ := file
    by_cases spans : checkSelectedWalSegmentSpans (length.toNat / frameSize) ((first, bytes) :: rest) = true
    · rw [recoverMarkedWalSegments_eq_extract base length first bytes rest spans]
      let clipped := (walSegmentPayloadBytes ((first, bytes) :: rest)).extract 0 (length.toNat - first * frameSize)
      cases selected : WAL.Boundary.selectRetained first length clipped with
      | error cause =>
        dsimp only [clipped] at selected
        simp [recoverMarkedWalSegmentsWithReplayWork, spans,
          WAL.Boundary.recoverRetainedMarked, selected, Bind.bind, Except.bind]
      | ok selectedBytes =>
        dsimp only [clipped] at selected
        have through : length.toNat / frameSize = first + selectedBytes.size / frameSize := by
          rw [← WAL.Boundary.selectRetained_absoluteSize selected, Nat.add_comm,
            Nat.add_mul_div_right _ _ (by decide), Nat.add_comm]
        have work := recoverRetainedFromWithReplayWork_spec base first selectedBytes
        cases replayed : recoverRetainedFromWithReplayWork base first selectedBytes with
        | mk result attempts =>
          rw [replayed] at work
          obtain ⟨same, limit, exactCount⟩ := work
          dsimp only at same limit exactCount
          simp only [recoverMarkedWalSegmentsWithReplayWork, spans, ↓reduceIte, selected,
            WAL.Boundary.recoverRetainedMarked, Bind.bind, Except.bind, replayed, ← same]
          rw [through]
          cases result with
          | error cause => simp [Except.map, limit]
          | ok table => simp [Except.map, Pure.pure, Except.pure, exactCount table rfl]
    · simp [recoverMarkedWalSegmentsWithReplayWork, recoverMarkedWalSegments, spans]

/-- Account for decoding after the marked worker's span and marker
selection. A rejection during either selection stage reaches no frame. -/
noncomputable def markedWalDecodeWork (length : UInt64) (files : List (Nat × ByteArray)) : WAL.OrdinalDecodeWork :=
  match files with
  | [] => ⟨0, 0⟩
  | (first, _) :: _ =>
    if checkSelectedWalSegmentSpans (length.toNat / frameSize) files then
      let clipped := (walSegmentPayloadBytes files).extract 0 (length.toNat - first * frameSize)
      match WAL.Boundary.selectRetained first length clipped with
      | .error _ => ⟨0, 0⟩
      | .ok selected => (WAL.decodeOrdinalsFromWithWork (first + 1) selected).2
    else ⟨0, 0⟩

/-- Marked recovery validates the same selected bytes at the same absolute
ordinals. In particular, decoder rejection reaches the caller unchanged. -/
theorem markedWalDecodeWork_of_selection (base : PackedTable) (length : UInt64)
    (first : Nat) (bytes : ByteArray) (rest : List (Nat × ByteArray))
    (spans : checkSelectedWalSegmentSpans (length.toNat / frameSize) ((first, bytes) :: rest) = true)
    {selected : ByteArray}
    (selection : WAL.Boundary.selectRetained first length
      ((walSegmentPayloadBytes ((first, bytes) :: rest)).extract 0 (length.toNat - first * frameSize)) = .ok selected) :
    markedWalDecodeWork length ((first, bytes) :: rest) = (WAL.decodeOrdinalsFromWithWork (first + 1) selected).2 ∧
      ∀ cause, WAL.decodeOrdinalsFrom (first + 1) selected = .error cause →
        recoverMarkedWalSegments base length ((first, bytes) :: rest) = .error cause := by
  refine ⟨by simp [markedWalDecodeWork, spans, selection], ?_⟩
  intro cause stopped
  rw [recoverMarkedWalSegments_eq_extract base length first bytes rest spans]
  simp [WAL.Boundary.recoverRetainedMarked, recoverRetainedFrom, selection, stopped, Bind.bind, Except.bind]

/-- Bound the decoded span by the absolute marker measured from the first
retained frame. Success reaches every format and ordinal check in the span. -/
theorem markedWalDecodeWork_spec (base : PackedTable) (length : UInt64) (files : List (Nat × ByteArray)) :
    let work := markedWalDecodeWork length files
    let through := length.toNat / frameSize
    let complete := through - (files.head?.map Prod.fst).getD through
    work.ordinals ≤ work.frames ∧ work.frames ≤ complete ∧
      (∀ output, recoverMarkedWalSegments base length files = .ok output → work = ⟨complete, complete⟩) := by
  dsimp only
  cases files with
  | nil => simp [markedWalDecodeWork, recoverMarkedWalSegments]
  | cons file rest =>
    obtain ⟨first, bytes⟩ := file
    by_cases spans : checkSelectedWalSegmentSpans (length.toNat / frameSize) ((first, bytes) :: rest) = true
    · let clipped := (walSegmentPayloadBytes ((first, bytes) :: rest)).extract 0 (length.toNat - first * frameSize)
      cases chosen : WAL.Boundary.selectRetained first length clipped with
      | error cause =>
        dsimp only [clipped] at chosen
        rw [recoverMarkedWalSegments_eq_extract base length first bytes rest spans]
        simp [markedWalDecodeWork, spans, chosen, WAL.Boundary.recoverRetainedMarked, Bind.bind, Except.bind]
      | ok selected =>
        obtain ⟨work, decoderError⟩ := markedWalDecodeWork_of_selection base length first bytes rest spans chosen
        have complete : length.toNat / frameSize - first = selected.size / frameSize := by
          rw [← WAL.Boundary.selectRetained_absoluteSize chosen, Nat.add_comm,
            Nat.add_mul_div_right _ _ (by decide), Nat.add_sub_cancel]
        obtain ⟨same, ordinals, frames, exact⟩ := WAL.decodeOrdinalsFromWithWork_spec (first + 1) selected
        simp only [work, List.head?_cons, Option.map_some, Option.getD_some, complete]
        refine ⟨ordinals, frames, ?_⟩
        intro output recovered
        cases decoded : WAL.decodeOrdinalsFrom (first + 1) selected with
        | error cause => rw [decoderError cause decoded] at recovered; contradiction
        | ok events => exact exact events (same.trans decoded)
    · simp [markedWalDecodeWork, recoverMarkedWalSegments, spans]

end Alvoki.Storage
