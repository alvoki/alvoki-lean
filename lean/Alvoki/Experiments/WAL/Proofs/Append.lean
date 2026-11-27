import Alvoki.Experiments.WAL.CrashModel
import Alvoki.Experiments.WAL.Proofs.Marker

namespace WalRecoverySlice.Persistence

private theorem markerFragment_complete (residue : Option DamagedMarker) (old : Bytes) (endPos seq : Nat) :
    markerFragment residue old (encodeMarker endPos seq) = encodeMarker endPos seq := by
  simp [markerFragment, encodeMarker, markerSize]

private theorem Written.append_prefix (written : Written) (old bytes : Bytes) :
    ∃ count, written.bytes List.append old bytes = old ++ bytes.take count := by
  cases written
  · exact ⟨0, by simp [Written.bytes]⟩
  · exact ⟨_, rfl⟩
  · exact ⟨bytes.length, by simp [Written.bytes]⟩

def SlotOutcome (slot : Nat) (old new observed : Bytes) : Prop :=
  observed = old ∨ (∃ count, observed = new.take count) ∨ decodeMarker slot observed = .ok none

private theorem Written.slotOutcome (written : Written) (old : Bytes) (endPos seq : Nat)
    (residue : Option DamagedMarker) :
    let new := encodeMarker endPos seq
    SlotOutcome (seq % 2) old new (written.bytes (markerFragment residue) old new) := by
  dsimp only
  cases written with
  | old => exact .inl rfl
  | complete =>
    rw [Written.bytes, markerFragment_complete]
    exact .inr (.inl ⟨_, (List.take_length).symm⟩)
  | short count =>
    simp only [Written.bytes, markerFragment]
    split
    · exact .inr (.inl ⟨count, rfl⟩)
    · cases residue with
      | none => exact .inr (.inl ⟨count, rfl⟩)
      | some m => exact .inr (.inr (decodeMarker_bad_check _ _ _ _ _ _ _ _ m.checkLength m.damaged))

private theorem Image.marker_updated (image : Image) (slot : Nat) (file : FileImage) :
    (image.withMarker slot file).marker slot = file := by
  by_cases zero : slot = 0 <;> simp [Image.marker, Image.withMarker, zero]

private theorem Image.otherMarker_updated (image : Image) (slot : Nat) (file : FileImage) :
    (image.withMarker slot file).marker (1 - slot) = image.marker (1 - slot) := by
  by_cases zero : slot = 0
  · simp [Image.marker, Image.withMarker, zero]
  · have other : 1 - slot = 0 := by omega
    simp [Image.marker, Image.withMarker, zero, other]

theorem Image.data_updatedMarker (image : Image) (slot : Nat) (file : FileImage) :
    (image.withMarker slot file).data = image.data := by
  by_cases zero : slot = 0 <;> simp [Image.withMarker, zero]

/-- The observed append preserves the settled data prefix and the other slot.
Any physical change to the destination slot follows complete data settlement. -/
structure AppendEffects (policy : Policy) (cursor : Cursor) (payload prior : Bytes)
    (before : Image) (result : Result Cursor) : Prop where
  livePrefix : ∃ count, (reached result).data.live = prior ++ (frame cursor.nextSeq payload).take count
  durablePrefix : ∃ count, (reached result).data.durable = prior ++ (frame cursor.nextSeq payload).take count
  otherMarkerUnchanged : (reached result).marker (1 - cursor.nextSeq % 2) =
    before.marker (1 - cursor.nextSeq % 2)
  markerRequiresSync : (reached result).marker (cursor.nextSeq % 2) ≠ before.marker (cursor.nextSeq % 2) →
    policy = .boundary ∧ (reached result).data = ⟨prior ++ frame cursor.nextSeq payload, prior ++ frame cursor.nextSeq payload⟩
  markerOutcome : let slot := cursor.nextSeq % 2
    SlotOutcome slot (before.marker slot).durable
      (encodeMarker (cursor.endPos + (frame cursor.nextSeq payload).length) cursor.nextSeq)
      ((reached result).marker slot).durable
  ack : ∀ next, acknowledged result = some next →
    next = ⟨cursor.endPos + (frame cursor.nextSeq payload).length, cursor.nextSeq + 1⟩ ∧
    (reached result).data = ⟨prior ++ frame cursor.nextSeq payload, prior ++ frame cursor.nextSeq payload⟩ ∧
    (policy = .boundary → (reached result).marker (cursor.nextSeq % 2) =
      ⟨encodeMarker next.endPos cursor.nextSeq, encodeMarker next.endPos cursor.nextSeq⟩)

private theorem noMarker {policy : Policy} {cursor : Cursor} {payload prior : Bytes}
    {before : Image} {result : Result Cursor} {data : FileImage}
    (atData : reached result = { before with data })
    (live : ∃ count, data.live = prior ++ (frame cursor.nextSeq payload).take count)
    (durable : ∃ count, data.durable = prior ++ (frame cursor.nextSeq payload).take count)
    (ack : ∀ next, acknowledged result = some next →
      policy = .logOnly ∧ next = ⟨cursor.endPos + (frame cursor.nextSeq payload).length, cursor.nextSeq + 1⟩ ∧
      data = ⟨prior ++ frame cursor.nextSeq payload, prior ++ frame cursor.nextSeq payload⟩) :
    AppendEffects policy cursor payload prior before result := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [atData] using live
  · simpa only [atData] using durable
  · rw [atData]
    rfl
  · rw [atData]
    intro bad
    exact (bad rfl).elim
  · rw [atData]
    exact .inl rfl
  · intro next got
    obtain ⟨logOnly, nextEq, exactData⟩ := ack next got
    exact ⟨nextEq, atData ▸ exactData, fun boundary => by cases logOnly.symm.trans boundary⟩

private theorem dataEnds (prior bytes : Bytes) :
    ∃ count, prior ++ bytes = prior ++ bytes.take count :=
  ⟨bytes.length, by simp⟩

private theorem afterMarker {cursor : Cursor} {payload prior : Bytes} {before : Image} {result : Result Cursor}
    {marker : FileImage}
    (exactImage : reached result =
      ({before with data := ⟨prior ++ frame cursor.nextSeq payload, prior ++ frame cursor.nextSeq payload⟩}).withMarker
        (cursor.nextSeq % 2) marker)
    (published : SlotOutcome (cursor.nextSeq % 2) (before.marker (cursor.nextSeq % 2)).durable
      (encodeMarker (cursor.endPos + (frame cursor.nextSeq payload).length) cursor.nextSeq) marker.durable)
    (ack : ∀ next, acknowledged result = some next →
      next = ⟨cursor.endPos + (frame cursor.nextSeq payload).length, cursor.nextSeq + 1⟩ ∧
      marker = ⟨encodeMarker next.endPos cursor.nextSeq, encodeMarker next.endPos cursor.nextSeq⟩) :
    AppendEffects .boundary cursor payload prior before result := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [exactImage, Image.data_updatedMarker]
    exact dataEnds _ _
  · rw [exactImage, Image.data_updatedMarker]
    exact dataEnds _ _
  · rw [exactImage, Image.otherMarker_updated]
    rfl
  · rw [exactImage, Image.data_updatedMarker]
    exact fun _ => ⟨rfl, rfl⟩
  · dsimp only
    rw [exactImage, Image.marker_updated]
    exact published
  · intro next got
    obtain ⟨nextEq, markerEq⟩ := ack next got
    exact ⟨nextEq, by rw [exactImage, Image.data_updatedMarker],
      fun _ => by rw [exactImage, Image.marker_updated, markerEq]⟩

private theorem AppendEffects.unchanged {policy : Policy} {cursor : Cursor} {payload prior : Bytes}
    {before : Image} {result : Result Cursor} (stable : before.data = ⟨prior, prior⟩)
    (atStart : reached result = before) (failed : acknowledged result = none) :
    AppendEffects policy cursor payload prior before result := by
  have atData : reached result = {before with data := ⟨prior, prior⟩} := by
    cases before
    cases stable
    exact atStart
  exact noMarker atData ⟨0, by simp⟩ ⟨0, by simp⟩ (by simp [failed])

/-- The actual append schedule after its size, sequence and marker extent guards. -/
theorem appendBatch_of_valid {callbacks : Ops M} {policy : Policy} {cursor : Cursor} {payload : Bytes}
    (wellSized : payload.length ≤ 32) (positive : cursor.nextSeq ≠ 0) (fits : cursor.nextSeq ≤ 255)
    (inBounds : policy = .boundary → cursor.endPos + (frame cursor.nextSeq payload).length ≤ 65535) :
    appendBatch callbacks policy cursor payload = (do
      let bytes := frame cursor.nextSeq payload
      let next := cursor.endPos + bytes.length
      callbacks.append bytes
      callbacks.syncData
      if policy == .boundary then
        let slot := cursor.nextSeq % 2
        callbacks.writeMarker slot (encodeMarker next cursor.nextSeq)
        callbacks.syncMarker slot
      return ⟨next, cursor.nextSeq + 1⟩) := by
  have guard : (payload.length > 32 || cursor.nextSeq == 0 || cursor.nextSeq > 255) = false := by
    simp [Nat.not_lt_of_ge wellSized, positive, Nat.not_lt_of_ge fits]
  have extent : ((policy == .boundary) && (cursor.endPos + (frame cursor.nextSeq payload).length > 65535)) = false := by
    cases policy
    · rfl
    · simp [BEq.beq, Nat.not_lt_of_ge (inBounds rfl)]
  simp only [appendBatch, extent, Bool.false_eq_true, ↓reduceIte]
  change (if (payload.length > 32 || cursor.nextSeq == 0 || cursor.nextSeq > 255) = true then _ else _) = _
  simp only [guard, Bool.false_eq_true, ↓reduceIte]

private theorem Image.withMarker_twice (image : Image) (slot : Nat) (a b : FileImage) :
    (image.withMarker slot a).withMarker slot b = image.withMarker slot b := by
  by_cases zero : slot = 0 <;> simp [Image.withMarker, zero]

private def destination (cursor : Cursor) := cursor.nextSeq % 2
private def markerBytes (cursor : Cursor) (payload : Bytes) :=
  encodeMarker (cursor.endPos + (frame cursor.nextSeq payload).length) cursor.nextSeq
private def advanced (cursor : Cursor) (payload : Bytes) : Cursor :=
  ⟨cursor.endPos + (frame cursor.nextSeq payload).length, cursor.nextSeq + 1⟩

local macro "run_effects" " [" facts:Lean.Parser.Tactic.simpArg,* "]" : tactic => do
  let facts : Lean.Syntax.TSepArray
      [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma] "," :=
    ⟨facts.elemsAndSeps⟩
  `(tactic| simp only [ops, Bind.bind, ExceptT.run, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
      EStateM.bind, Write.result, Primitive.syncResult, Abort.result, Pure.pure, ExceptT.pure, EStateM.pure,
      Image.marker_updated, Image.withMarker_twice, $facts,*])

private theorem afterDataSync {effects : Effects} {cursor : Cursor} {payload prior : Bytes} {before : Image} :
    let synced := { before with data := ⟨prior ++ frame cursor.nextSeq payload, prior ++ frame cursor.nextSeq payload⟩ }
    AppendEffects .boundary cursor payload prior before (((do
      (ops effects).writeMarker (destination cursor) (markerBytes cursor payload)
      (ops effects).syncMarker (destination cursor)
      pure (advanced cursor payload)) : M Cursor).run synced) := by
  intro synced
  have fullTail := dataEnds prior (frame cursor.nextSeq payload)
  cases written : effects.writeMarker with
  | before abort =>
    cases abort <;> run_effects [written] <;> exact noMarker rfl fullTail fullTail (by simp [acknowledged])
  | torn count persisted abort =>
    cases abort <;> run_effects [written] <;>
      exact afterMarker rfl (persisted.slotOutcome _ _ _ _) (by simp [acknowledged])
  | full persisted abort =>
    cases abort with
    | some abort =>
      cases abort <;> run_effects [written] <;>
        exact afterMarker rfl (persisted.slotOutcome _ _ _ _) (by simp [acknowledged])
    | none =>
      cases syncedMarker : effects.markerSync (destination cursor) with
      | before abort =>
        cases abort <;> run_effects [written, syncedMarker, markerBytes, markerFragment_complete] <;>
          exact afterMarker rfl (persisted.slotOutcome _ _ _ _) (by simp [acknowledged])
      | after abort =>
        have published : ∃ count, markerBytes cursor payload = (markerBytes cursor payload).take count :=
          ⟨(markerBytes cursor payload).length, by simp⟩
        cases abort with
        | some abort =>
          cases abort <;> run_effects [written, syncedMarker, markerBytes, markerFragment_complete] <;>
            exact afterMarker rfl (.inr (.inl published)) (by simp [acknowledged])
        | none =>
          run_effects [written, syncedMarker, markerBytes, markerFragment_complete]
          apply afterMarker rfl (.inr (.inl published))
          intro next equals
          have equal : advanced cursor payload = next := Option.some.inj equals
          subst next
          exact ⟨rfl, rfl⟩

/-- Classifies all reached images of the real append schedule for a bounded
request. The only inputs are the settled entry and primitive filesystem choices. -/
theorem appendBatch_effects (effects : Effects) (policy : Policy) (cursor : Cursor) (payload : Bytes)
    (before : Image) (prior : Bytes) (settled : AtEnd before cursor prior)
    (wellSized : payload.length ≤ 32) (positive : cursor.nextSeq ≠ 0) (fits : cursor.nextSeq ≤ 255)
    (inBounds : policy = .boundary → cursor.endPos + (frame cursor.nextSeq payload).length ≤ 65535) :
    AppendEffects policy cursor payload prior before ((appendBatch (ops effects) policy cursor payload).run before) := by
  rw [appendBatch_of_valid wellSized positive fits inBounds]
  have initial := settled.1
  let bytes := frame cursor.nextSeq payload
  have fullTail := dataEnds prior bytes
  cases written : effects.appendData with
  | before abort =>
    cases abort <;> run_effects [written] <;> exact AppendEffects.unchanged initial rfl rfl
  | torn count persisted abort =>
    cases abort <;> run_effects [written, initial] <;>
      exact noMarker rfl ⟨count, rfl⟩ (persisted.append_prefix _ _) (by simp [acknowledged])
  | full persisted abort =>
    cases abort with
    | some abort =>
      cases abort <;> run_effects [written, initial] <;>
        exact noMarker rfl fullTail (persisted.append_prefix _ _) (by simp [acknowledged])
    | none =>
      cases syncedData : effects.dataSync with
      | before abort =>
        cases abort <;> run_effects [written, initial, syncedData] <;>
          exact noMarker rfl fullTail (persisted.append_prefix _ _) (by simp [acknowledged])
      | after abort =>
        cases abort with
        | some abort =>
          cases abort <;> run_effects [written, initial, syncedData] <;>
            exact noMarker rfl fullTail fullTail (by simp [acknowledged])
        | none =>
          cases policy
          · run_effects [written, initial, syncedData, BEq.beq, instBEqPolicy, Bool.false_eq_true, ↓reduceIte]
            refine noMarker (before := before) rfl fullTail fullTail ?_
            intro next returned
            exact ⟨rfl, Option.some.inj returned |>.symm, rfl⟩
          · have valid := @afterDataSync effects cursor payload prior before
            run_effects [written, initial, syncedData, BEq.beq, instBEqPolicy, ↓reduceIte]
            exact valid

end WalRecoverySlice.Persistence
