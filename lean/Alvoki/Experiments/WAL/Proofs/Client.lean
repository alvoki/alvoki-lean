import Alvoki.Experiments.WAL.Proofs.Persistence

namespace WalRecoverySlice.Persistence

/-- Fresh durable files after initialization of the caller-owned directory. -/
def freshImage : Image :=
  let empty := encodeMarker 0 0
  ⟨⟨[], []⟩, ⟨empty, empty⟩, ⟨[], []⟩⟩

/-- Format rejection happens before the first filesystem primitive. -/
theorem append_rejected (policy : Policy) (effects : Effects) (cursor : Cursor) (payload : Bytes)
    (before : Image) (invalid : 32 < payload.length ∨ 255 < cursor.nextSeq) :
    (appendBatch (ops effects) policy cursor payload).run before = .ok (.error "batch out of bounds") before := by
  have guard : (payload.length > 32 || cursor.nextSeq == 0 || cursor.nextSeq > 255) = true := by
    rcases invalid with size | seq <;> simp [*]
  unfold appendBatch
  change ((if (payload.length > 32 || cursor.nextSeq == 0 || cursor.nextSeq > 255) = true then _ else _) :
    M Cursor).run before = _
  simp only [guard, ↓reduceIte]
  rfl

theorem fresh_ready (policy : Policy) : Ready policy freshImage [] := by
  refine ⟨⟨rfl, rfl⟩, fun _ => ⟨rfl, none, rfl, ?_⟩⟩
  intro old h
  contradiction

theorem ready_after_ack {policy prior before next after} (entry : Ready policy before prior)
    (payload : Bytes) (effects : Effects)
    (returned : (appendBatch (ops effects) policy (historyCursor prior) payload).run before = .ok (.ok next) after)
    (oldBound : ∀ b ∈ prior, b.length ≤ 32) (priorFits : prior.length < 255)
    (payloadBound : payload.length ≤ 32) :
    next = historyCursor (prior ++ [payload]) ∧ Ready policy after (prior ++ [payload]) := by
  obtain ⟨settled, authority⟩ := entry
  have size := encoded_history_size prior 1 oldBound
  have positive : (historyCursor prior).nextSeq ≠ 0 := by simp [historyCursor]
  have observed := appendBatch_effects effects policy (historyCursor prior) payload before _
    settled payloadBound positive (by simp [historyCursor]; omega)
    (by intro; simp only [historyCursor, frame_length]; omega)
  rw [returned] at observed
  have ack := observed.ack next rfl
  obtain ⟨rfl, full, published⟩ := ack
  simp only [reached] at full published
  have snoc := encodeFrames_snoc 1 prior payload
  have cursorEq : (⟨(historyCursor prior).endPos + (frame (historyCursor prior).nextSeq payload).length,
      (historyCursor prior).nextSeq + 1⟩ : Cursor) = historyCursor (prior ++ [payload]) := by
    simp [historyCursor, snoc, Nat.add_assoc]
  refine ⟨cursorEq, ?_⟩
  unfold Ready
  rw [← cursorEq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa [historyCursor, snoc] using full
  · simp [historyCursor, snoc]
  intro boundary
  have prev := authority boundary
  have seqpar : 1 - (1 + prior.length) % 2 = prior.length % 2 := by omega
  have nextpar : ((1 + prior.length) + 1) % 2 = prior.length % 2 := by omega
  have kept := observed.otherMarkerUnchanged
  simp only [reached, historyCursor, seqpar] at kept
  have oldSlot := prev.selected
  simp [historyCursor] at oldSlot
  constructor
  · simpa [historyCursor] using congrArg FileImage.durable (published boundary)
  · refine ⟨some ⟨(encodeFrames 1 prior).length, prior.length⟩, ?_, ?_⟩
    · simp only [historyCursor, nextpar, kept, oldSlot]
      apply decodeMarker_encode _ _ (by omega) (by omega)
      cases prior <;> simp [encodeFrames, frame_length]
    · intro old h
      cases h
      simp [historyCursor]

end WalRecoverySlice.Persistence
