import Alvoki.Experiments.WAL.Proofs.Persistence

namespace WalRecoverySlice.Persistence

/-- Fresh durable files after initialization of the caller-owned directory. -/
def freshImage : Image :=
  let empty := encodeMarker 0 0
  let spare := List.replicate markerSize 0
  ⟨⟨[], []⟩, ⟨empty, empty⟩, ⟨spare, spare⟩⟩

/-- A client's uninterrupted sequence of successful calls. Each step uses the
cursor and image returned by the preceding call. -/
inductive Confirmed (policy : Policy) : List Bytes → Cursor → Image → Prop where
  | fresh : Confirmed policy [] {} freshImage
  | append {prior cursor before next after} (earlier : Confirmed policy prior cursor before)
      (payload : Bytes) (effects : Effects)
      (returned : (appendBatch (ops effects) policy cursor payload).run before = .ok (.ok next) after) :
      Confirmed policy (prior ++ [payload]) next after

private theorem encoded_bound (batches : List Bytes) (first : Nat)
    (bounded : ∀ b ∈ batches, b.length ≤ 32) :
    (encodeFrames first batches).length ≤ 38 * batches.length := by
  induction batches generalizing first with
  | nil => simp [encodeFrames]
  | cons head rest ih =>
    have headFits := bounded head (by simp)
    have tailFits := ih (first + 1) (by intro b hb; exact bounded b (by simp [hb]))
    simp only [encodeFrames, List.length_append, frame_length, List.length_cons]
    omega

/-- The file and marker premises required for recovery follow from the client's
actual ACK history starting at the fresh files. -/
theorem Confirmed.settled {policy batches cursor image} (run : Confirmed policy batches cursor image)
    (bounded : ∀ b ∈ batches, b.length ≤ 32) (fits : batches.length ≤ 255) :
    cursor = historyCursor batches ∧ AtEnd image cursor (encodeFrames 1 batches) ∧
      (policy = .boundary → BoundaryEntry image cursor) := by
  induction run with
  | fresh =>
    refine ⟨rfl, ⟨rfl, rfl⟩, fun _ => ⟨rfl, none, rfl, ?_⟩⟩
    intro old h
    contradiction
  | @append prior cursor before next after earlier payload effects returned ih =>
    have priorFits : prior.length < 255 := by simp at fits; omega
    have oldBound : ∀ b ∈ prior, b.length ≤ 32 := fun b hb => bounded b (by simp [hb])
    have payloadBound := bounded payload (by simp)
    obtain ⟨rfl, settled, authority⟩ := ih oldBound (by omega)
    have size := encoded_bound prior 1 oldBound
    have positive : (historyCursor prior).nextSeq ≠ 0 := by simp [historyCursor]
    have effects := appendBatch_effects effects policy (historyCursor prior) payload before _
      settled payloadBound positive (by simp [historyCursor]; omega)
      (by intro; simp only [historyCursor, frame_length]; omega)
    rw [returned] at effects
    have ack := effects.ack next rfl
    obtain ⟨rfl, full, published⟩ := ack
    simp only [reached] at full published
    have snoc := encodeFrames_snoc 1 prior payload
    refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
    · simp [historyCursor, snoc, Nat.add_assoc]
    · simpa [historyCursor, snoc] using full
    · simp [historyCursor, snoc]
    intro boundary
    have prev := authority boundary
    have seqpar : 1 - (1 + prior.length) % 2 = prior.length % 2 := by omega
    have nextpar : ((1 + prior.length) + 1) % 2 = prior.length % 2 := by omega
    have kept := effects.otherMarkerUnchanged
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

/-- From fresh files, any bounded ACK history survives power loss after the
next append attempt. Healthy reopen can also retain that whole last batch;
it must retain it if the last call returned success. -/
theorem Confirmed.recover {policy batches cursor image} (run : Confirmed policy batches cursor image)
    (payload : Bytes) (effects : Effects) (bounded : ∀ b ∈ batches, b.length ≤ 32)
    (fits : batches.length < 255) (wellSized : payload.length ≤ 32) :
    RecoversAppend policy ((appendBatch (ops effects) policy cursor payload).run image) batches payload := by
  obtain ⟨rfl, entry, authority⟩ := run.settled bounded (by omega)
  cases policy with
  | logOnly => exact appendBatch_reopens_logOnly effects image batches payload entry bounded fits wellSized
  | boundary =>
    apply appendBatch_reopens_boundary effects image batches payload entry (authority rfl) bounded fits wellSized
    have size := encoded_bound batches 1 bounded
    rw [frame_length]
    omega

end WalRecoverySlice.Persistence
