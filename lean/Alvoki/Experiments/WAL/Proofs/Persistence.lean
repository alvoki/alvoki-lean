import Alvoki.Experiments.WAL.Proofs.Append
import Alvoki.Experiments.WAL.Proofs.Scan

namespace WalRecoverySlice.Persistence

/-- Truthful reads and successful repair primitives. The append callbacks are unused. -/
def healthyReopen : Effects where
  appendData := .before .error
  writeMarker := .before .error
  dataSync := .after none
  markerSync := fun _ => .after none

@[simp] private theorem Image.marker_zero (image : Image) : image.marker 0 = image.slot0 := rfl
@[simp] private theorem Image.marker_one (image : Image) : image.marker 1 = image.slot1 := rfl

private theorem reopen_logOnly {before : Image} {decoded : Decoded}
    (scanned : scan before.data.live before.data.live.length .logOnly = .ok decoded) :
    let bytes := before.data.live.take decoded.cursor.endPos
    (reopen (ops healthyReopen) .logOnly).run before = .ok (.ok decoded)
      { before with data := ⟨bytes, bytes⟩ } := by
  have branch : (Policy.logOnly == .boundary) = false := rfl
  dsimp only
  by_cases trim : decoded.cursor.endPos < before.data.live.length
  · simp [reopen, ops, healthyReopen, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
      ExceptT.run, EStateM.bind, Pure.pure, ExceptT.pure, EStateM.pure, branch,
      scanned, Primitive.syncResult, trim]
  · have bytes : before.data.live.take decoded.cursor.endPos = before.data.live :=
      List.take_of_length_le (Nat.le_of_not_gt trim)
    rw [bytes]
    simp [reopen, ops, healthyReopen, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
      ExceptT.run, EStateM.bind, Pure.pure, ExceptT.pure, EStateM.pure, branch,
      scanned, Primitive.syncResult, trim]

private theorem reopen_boundary {before : Image} {selected : Marker} {decoded : Decoded}
    (picked : selectMarker before.slot0.live before.slot1.live = .ok selected)
    (scanned : scan before.data.live selected.endPos .boundary = .ok decoded)
    (ordinal : decoded.cursor.nextSeq = selected.lastSeq + 1) :
    let bytes := before.data.live.take decoded.cursor.endPos
    let slot := selected.lastSeq % 2
    let sibling := 1 - slot
    let synced := before.withMarker slot ⟨(before.marker slot).live, (before.marker slot).live⟩
    (reopen (ops healthyReopen) .boundary).run before = .ok (.ok decoded)
      { (synced.withMarker sibling ⟨(synced.marker sibling).live, (synced.marker sibling).live⟩) with
        data := ⟨bytes, bytes⟩ } := by
  have branch : (Policy.boundary == .boundary) = true := rfl
  dsimp only
  by_cases trim : decoded.cursor.endPos < before.data.live.length
  · simp [reopen, ops, healthyReopen, Image.data_updatedMarker, Bind.bind, ExceptT.bind,
      ExceptT.bindCont, ExceptT.mk, ExceptT.run, EStateM.bind, Pure.pure, ExceptT.pure, EStateM.pure,
      branch, picked, scanned, ordinal, Primitive.syncResult, trim]
  · have bytes : before.data.live.take decoded.cursor.endPos = before.data.live :=
      List.take_of_length_le (Nat.le_of_not_gt trim)
    rw [bytes]
    simp [reopen, ops, healthyReopen, Image.data_updatedMarker, Bind.bind, ExceptT.bind,
      ExceptT.bindCont, ExceptT.mk, ExceptT.run, EStateM.bind, Pure.pure, ExceptT.pure, EStateM.pure,
      branch, picked, scanned, ordinal, Primitive.syncResult, trim]

def historyCursor (batches : List Bytes) : Cursor :=
  ⟨(encodeFrames 1 batches).length, 1 + batches.length⟩

/-- The durable active slot records the settled cursor. The other slot
is either detectably incomplete or encodes an older cursor. -/
structure BoundaryEntry (before : Image) (cursor : Cursor) : Prop where
  selected : (before.marker ((cursor.nextSeq - 1) % 2)).durable = encodeMarker cursor.endPos (cursor.nextSeq - 1)
  other : ∃ marker : Option Marker,
    decodeMarker (cursor.nextSeq % 2) (before.marker (cursor.nextSeq % 2)).durable = .ok marker ∧
    ∀ old, marker = some old → old.lastSeq < cursor.nextSeq - 1

/-- A settled history and, in boundary mode, the two durable marker
slots needed to attempt the next bounded append. -/
def Ready (policy : Policy) (image : Image) (batches : List Bytes) : Prop :=
  AtEnd image (historyCursor batches) (encodeFrames 1 batches) ∧
    (policy = .boundary → BoundaryEntry image (historyCursor batches))

theorem encoded_history_size (batches : List Bytes) (first : Nat)
    (bounded : ∀ b ∈ batches, b.length ≤ 32) :
    (encodeFrames first batches).length ≤ 52 * batches.length := by
  induction batches generalizing first with
  | nil => simp [encodeFrames]
  | cons head rest ih =>
    have headFits := bounded head (by simp)
    have tailFits := ih (first + 1) (by intro b hb; exact bounded b (by simp [hb]))
    simp only [encodeFrames, List.length_append, frame_length, List.length_cons]
    omega

/-- Exact public reopen result after one modeled power loss. The returned
cursor, data, and marker slots agree with the recovered history, ready for the
next bounded append. An acknowledged submission is retained. Another power
loss and healthy reopen return the same history and image. -/
def RecoversAppend (policy : Policy) (outcome : Result Cursor) (batches : List Bytes) (payload : Bytes) : Prop :=
  ∃ decoded after,
    (reopen (ops healthyReopen) policy).run (reached outcome).powerLoss = .ok (.ok decoded) after ∧
    decoded.cursor = historyCursor decoded.batches ∧
    Ready policy after decoded.batches ∧
    (decoded.batches = batches ∨ decoded.batches = batches ++ [payload]) ∧
    (∀ cursor, acknowledged outcome = some cursor → decoded.batches = batches ++ [payload]) ∧
    after.powerLoss = after ∧
    (reopen (ops healthyReopen) policy).run after.powerLoss = .ok (.ok decoded) after

private theorem takePrior (prior suffix : Bytes) :
    (prior ++ suffix).take prior.length = prior := by
  simp

private theorem reopen_logOnly_again (reached : Image) (batches : List Bytes)
    (bounded : ∀ b ∈ batches, b.length ≤ 32) (fits : batches.length ≤ 255) :
    let bytes := encodeFrames 1 batches
    let after := { reached.powerLoss with data := ⟨bytes, bytes⟩ }
    (reopen (ops healthyReopen) .logOnly).run after.powerLoss = .ok (.ok ⟨batches, historyCursor batches⟩) after := by
  intro bytes after
  have stable : after.powerLoss = after := rfl
  rw [stable]
  have scanned : scan after.data.live after.data.live.length .logOnly = .ok ⟨batches, historyCursor batches⟩ :=
    scan_encodeFrames _ bounded fits
  have opened := reopen_logOnly scanned
  change (reopen (ops healthyReopen) .logOnly).run after = .ok (.ok ⟨batches, historyCursor batches⟩)
    {after with data := ⟨bytes.take bytes.length, bytes.take bytes.length⟩} at opened
  simpa only [List.take_length] using opened

/-- After a settled history and one actual append attempt, healthy log-only
reopen adopts the full appended frame or discards its strict byte prefix. -/
theorem appendBatch_reopens_logOnly (effects : Effects) (before : Image)
    (batches : List Bytes) (payload : Bytes)
    (entry : AtEnd before (historyCursor batches) (encodeFrames 1 batches))
    (bounded : ∀ b ∈ batches, b.length ≤ 32) (fits : batches.length < 255) (wellSized : payload.length ≤ 32) :
    RecoversAppend .logOnly ((appendBatch (ops effects) .logOnly (historyCursor batches) payload).run before)
      batches payload := by
  let cursor := historyCursor batches
  let outcome := (appendBatch (ops effects) .logOnly cursor payload).run before
  let boot := (reached outcome).powerLoss
  let prior := encodeFrames 1 batches
  let bytes := frame (1 + batches.length) payload
  have effect : AppendEffects .logOnly cursor payload prior before outcome :=
    appendBatch_effects effects .logOnly cursor payload before prior entry wellSized (by simp [cursor, historyCursor])
      (by simp [cursor, historyCursor]; omega) (by intro impossible; cases impossible)
  obtain ⟨cut, durable⟩ := effect.durablePrefix
  change boot.data.live = prior ++ bytes.take cut at durable
  have snoc : encodeFrames 1 (batches ++ [payload]) = prior ++ bytes := encodeFrames_snoc _ _ _
  change ∃ decoded after, (reopen (ops healthyReopen) .logOnly).run boot = .ok (.ok decoded) after ∧ _
  by_cases short : cut < bytes.length
  · have scanned : scan boot.data.live boot.data.live.length .logOnly = .ok ⟨batches, cursor⟩ := by
      rw [durable]
      exact scan_torn_encodeFrames payload cut bounded fits wellSized short
    have kept : boot.data.live.take cursor.endPos = prior := by
      rw [durable]
      exact takePrior _ _
    have opened := reopen_logOnly scanned
    change (reopen (ops healthyReopen) .logOnly).run boot =
      .ok (.ok ⟨batches, cursor⟩) {boot with data := ⟨boot.data.live.take cursor.endPos, _⟩} at opened
    rw [kept] at opened
    refine ⟨⟨batches, cursor⟩, {boot with data := ⟨prior, prior⟩}, opened, rfl,
      ⟨⟨rfl, rfl⟩, fun branch => by cases branch⟩, .inl rfl, ?_, rfl,
      reopen_logOnly_again (reached outcome) batches bounded (by omega)⟩
    intro next ack
    have stored : boot.data.live = prior ++ bytes :=
      congrArg FileImage.durable (effect.ack next ack).2.1
    have sizes := congrArg List.length (durable.symm.trans stored)
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt short)] at sizes
    omega
  · have whole : boot.data.live = prior ++ bytes :=
      durable.trans (congrArg (prior ++ ·) (List.take_of_length_le (Nat.le_of_not_gt short)))
    let retained := batches ++ [payload]
    let selected := historyCursor retained
    have retainedBounded : ∀ b ∈ retained, b.length ≤ 32 := by
      intro b member
      rcases List.mem_append.mp member with old | fresh
      · exact bounded b old
      · simpa using (List.mem_singleton.mp fresh ▸ wellSized)
    have retainedFits : retained.length ≤ 255 := by simp [retained]; omega
    have scanned : scan boot.data.live boot.data.live.length .logOnly = .ok ⟨retained, selected⟩ := by
      rw [whole, ← snoc]
      exact scan_encodeFrames .logOnly retainedBounded retainedFits
    have kept : boot.data.live.take selected.endPos = encodeFrames 1 retained := by
      rw [whole, ← snoc]
      exact List.take_length
    have opened := reopen_logOnly scanned
    change (reopen (ops healthyReopen) .logOnly).run boot =
      .ok (.ok ⟨retained, selected⟩) {boot with data := ⟨boot.data.live.take selected.endPos, _⟩} at opened
    rw [kept] at opened
    exact ⟨_, _, opened, rfl, ⟨⟨rfl, rfl⟩, fun branch => by cases branch⟩,
      .inr rfl, (fun _ _ => rfl), rfl, reopen_logOnly_again (reached outcome) retained retainedBounded retainedFits⟩

private theorem Image.marker_afterPowerLoss (image : Image) (slot : Nat) :
    (image.powerLoss.marker slot).live = (image.marker slot).durable := by
  by_cases zero : slot = 0 <;> simp [Image.marker, Image.powerLoss, FileImage.powerLoss, zero]

private theorem select_newest {image : Image} {slot : Nat} {selected : Marker} {other : Option Marker}
    (fits : slot < 2)
    (accepted : decodeMarker slot (image.marker slot).live = .ok (some selected))
    (alternate : decodeMarker (1 - slot) (image.marker (1 - slot)).live = .ok other)
    (newer : ∀ prior, other = some prior → prior.lastSeq < selected.lastSeq) :
    selectMarker image.slot0.live image.slot1.live = .ok selected := by
  have which : slot = 0 ∨ slot = 1 := by omega
  rcases which with rfl | rfl
  · cases other with
    | none => exact selectMarker_one (.inl ⟨accepted, alternate⟩)
    | some prior =>
      simpa [newer prior rfl] using selectMarker_both accepted alternate
  · cases other with
    | none => exact selectMarker_one (.inr ⟨alternate, accepted⟩)
    | some prior =>
      simpa [Nat.not_lt_of_ge (Nat.le_of_lt (newer prior rfl))] using selectMarker_both alternate accepted

private theorem decodeMarker_short (slot : Nat) {bytes : Bytes} (short : bytes.length < markerSize) :
    decodeMarker slot bytes = .ok none := by
  simp [decodeMarker, short, Nat.not_lt_of_ge (Nat.le_of_lt short)] <;> rfl

private theorem emptyFrames_iff (batches : List Bytes) :
    batches.length = 0 ↔ (encodeFrames 1 batches).length = 0 := by
  cases batches <;> simp [encodeFrames, frame_length]

private theorem Image.syncMarker_afterPowerLoss (image : Image) (slot : Nat) :
    image.powerLoss.withMarker slot ⟨(image.powerLoss.marker slot).live, (image.powerLoss.marker slot).live⟩ =
      image.powerLoss := by
  by_cases zero : slot = 0 <;> simp [Image.withMarker, Image.marker, Image.powerLoss, FileImage.powerLoss, zero]

private theorem Image.marker_setData (image : Image) (data : FileImage) (slot : Nat) :
    ({image with data}).marker slot = image.marker slot := by
  by_cases zero : slot = 0 <;> simp [Image.marker, zero]

private theorem Image.markerSettledByReboot (image : Image) (slot : Nat) :
    (image.powerLoss.marker slot).live = (image.powerLoss.marker slot).durable := by
  by_cases zero : slot = 0 <;> simp [Image.marker, Image.powerLoss, FileImage.powerLoss, zero]

private theorem BoundaryEntry.setData {image : Image} {cursor : Cursor}
    (entry : BoundaryEntry image cursor) (data : FileImage) :
    BoundaryEntry {image with data} cursor :=
  ⟨by simpa only [Image.marker_setData] using entry.selected,
    by simpa only [Image.marker_setData] using entry.other⟩

private theorem BoundaryEntry.powerLoss {image : Image} {cursor : Cursor}
    (entry : BoundaryEntry image cursor) : BoundaryEntry image.powerLoss cursor := by
  constructor
  · rw [← Image.markerSettledByReboot, Image.marker_afterPowerLoss]
    exact entry.selected
  · rw [← Image.markerSettledByReboot, Image.marker_afterPowerLoss]
    exact entry.other

private theorem BoundaryEntry.ofRebootedMarkers {image : Image} {batches : List Bytes} {alternate : Option Marker}
    (active : (image.powerLoss.marker (batches.length % 2)).live =
      encodeMarker (encodeFrames 1 batches).length batches.length)
    (other : decodeMarker ((1 + batches.length) % 2) (image.powerLoss.marker ((1 + batches.length) % 2)).live =
      .ok alternate)
    (older : ∀ record, alternate = some record → record.lastSeq < batches.length) :
    BoundaryEntry image.powerLoss (historyCursor batches) := by
  constructor
  · simpa only [historyCursor, Nat.add_sub_cancel_left, ← Image.markerSettledByReboot] using active
  · exact ⟨alternate, by simpa only [historyCursor, ← Image.markerSettledByReboot] using other,
      by simpa only [historyCursor, Nat.add_sub_cancel_left] using older⟩

private theorem reopen_selected {image : Image} {batches : List Bytes}
    (entry : BoundaryEntry image.powerLoss (historyCursor batches))
    {suffix : Bytes} (physical : image.powerLoss.data.live = encodeFrames 1 batches ++ suffix)
    (bounded : ∀ b ∈ batches, b.length ≤ 32) (fits : batches.length ≤ 255) :
    let decoded : Decoded := ⟨batches, historyCursor batches⟩
    let bytes := encodeFrames 1 batches
    let after := {image.powerLoss with data := ⟨bytes, bytes⟩}
    (reopen (ops healthyReopen) .boundary).run image.powerLoss = .ok (.ok decoded) after ∧
    Ready .boundary after batches ∧ after.powerLoss = after ∧
    (reopen (ops healthyReopen) .boundary).run after.powerLoss = .ok (.ok decoded) after := by
  intro decoded bytes after
  have picked : selectMarker image.powerLoss.slot0.live image.powerLoss.slot1.live =
      .ok ⟨bytes.length, batches.length⟩ := by
    have active := entry.selected
    simp only [historyCursor, Nat.add_sub_cancel_left, ← Image.markerSettledByReboot] at active
    have bound := encoded_history_size batches 1 bounded
    have activeRead : decodeMarker (batches.length % 2) (image.powerLoss.marker (batches.length % 2)).live =
        .ok (some ⟨bytes.length, batches.length⟩) := by
      rw [active]
      change decodeMarker _ (encodeMarker bytes.length batches.length) = _
      have extent : bytes.length < 65536 := by dsimp [bytes]; omega
      exact decodeMarker_encode _ _ (by omega) extent (emptyFrames_iff batches)
    obtain ⟨alternate, read, older⟩ := entry.other
    simp only [historyCursor, Nat.add_sub_cancel_left, ← Image.markerSettledByReboot] at read older
    have otherSlot : 1 - batches.length % 2 = (1 + batches.length) % 2 := by omega
    exact select_newest (Nat.mod_lt _ (by decide)) activeRead (otherSlot ▸ read) older
  have scanned : scan image.powerLoss.data.live bytes.length .boundary = .ok decoded := by
    rw [physical]
    exact scan_encodeFrames_append suffix .boundary bounded fits
  have ordinal : decoded.cursor.nextSeq = batches.length + 1 := by simp [decoded, historyCursor, Nat.add_comm]
  have opened := reopen_boundary picked scanned ordinal
  have kept : image.powerLoss.data.live.take decoded.cursor.endPos = bytes := by
    rw [physical]
    exact takePrior _ _
  simp only [Image.syncMarker_afterPowerLoss, kept] at opened
  refine ⟨opened, ⟨⟨rfl, rfl⟩, fun _ => entry.setData _⟩, rfl, ?_⟩
  have pickedAgain : selectMarker after.powerLoss.slot0.live after.powerLoss.slot1.live =
      .ok ⟨bytes.length, batches.length⟩ := picked
  have scannedAgain : scan after.powerLoss.data.live bytes.length .boundary = .ok decoded :=
    scan_encodeFrames .boundary bounded fits
  have reopened := reopen_boundary pickedAgain scannedAgain ordinal
  simp only [Image.syncMarker_afterPowerLoss] at reopened
  change (reopen (ops healthyReopen) .boundary).run after.powerLoss =
    .ok (.ok decoded) {after.powerLoss with data := ⟨bytes.take bytes.length, bytes.take bytes.length⟩} at reopened
  have stable : after.powerLoss = after := rfl
  simpa only [List.take_length, stable] using reopened

/-- After one append attempt in boundary mode, the durable slot selects the
old history or the whole submission. The actual healthy reopen settles that
selection. Selecting the new marker implies that its data barrier succeeded. -/
theorem appendBatch_reopens_boundary (effects : Effects) (before : Image)
    (batches : List Bytes) (payload : Bytes)
    (entry : AtEnd before (historyCursor batches) (encodeFrames 1 batches))
    (markerEntry : BoundaryEntry before (historyCursor batches))
    (bounded : ∀ b ∈ batches, b.length ≤ 32) (fits : batches.length < 255) (wellSized : payload.length ≤ 32)
    (inBounds : (encodeFrames 1 batches).length + (frame (1 + batches.length) payload).length ≤ 65535) :
    RecoversAppend .boundary ((appendBatch (ops effects) .boundary (historyCursor batches) payload).run before)
      batches payload := by
  let prior := encodeFrames 1 batches
  let cursor := historyCursor batches
  let bytes := frame cursor.nextSeq payload
  let slot := cursor.nextSeq % 2
  let oldSlot := 1 - slot
  let outcome := (appendBatch (ops effects) .boundary cursor payload).run before
  let boot := (reached outcome).powerLoss
  let oldRecord := encodeMarker cursor.endPos batches.length
  let newRecord := encodeMarker (cursor.endPos + bytes.length) cursor.nextSeq
  have parity : oldSlot = batches.length % 2 := by
    dsimp [oldSlot, slot, cursor, historyCursor]
    omega
  have next : cursor.nextSeq = 1 + batches.length := rfl
  have oldSeq : cursor.nextSeq - 1 = batches.length := by omega
  have oldPosition : cursor.endPos = prior.length := rfl
  have oldBound : prior.length < 65536 := by
    change (encodeFrames 1 batches).length < 65536
    omega
  have newBound : cursor.endPos + bytes.length < 65536 := Nat.lt_of_le_of_lt inBounds (by decide)
  have positiveSize : bytes.length > 0 := by
    simp [bytes, frame_length]
  have newFields : cursor.nextSeq = 0 ↔ cursor.endPos + bytes.length = 0 := by omega
  have advance := appendBatch_effects effects .boundary cursor payload before prior entry wellSized
    (by omega) (by omega) (fun _ => inBounds)
  change AppendEffects .boundary cursor payload prior before outcome at advance
  have old : (boot.marker oldSlot).live = oldRecord := by
    rw [Image.marker_afterPowerLoss, advance.otherMarkerUnchanged]
    have oldEvidence := markerEntry.selected
    change (before.marker ((cursor.nextSeq - 1) % 2)).durable =
      encodeMarker cursor.endPos (cursor.nextSeq - 1) at oldEvidence
    rw [oldSeq, ← parity] at oldEvidence
    exact oldEvidence
  have oldDecoded : decodeMarker oldSlot (boot.marker oldSlot).live = .ok (some ⟨prior.length, batches.length⟩) := by
    rw [old, parity]
    exact decodeMarker_encode _ _ (by omega) oldBound (emptyFrames_iff batches)
  obtain ⟨cut, tail⟩ := advance.durablePrefix
  change boot.data.live = prior ++ bytes.take cut at tail
  have openOld (sibling : Option Marker)
      (read : decodeMarker slot (boot.marker slot).live = .ok sibling)
      (earlier : ∀ m, sibling = some m → m.lastSeq < batches.length)
      (noAck : ∀ returned, acknowledged outcome ≠ some returned) :
      RecoversAppend .boundary outcome batches payload := by
    have selected := BoundaryEntry.ofRebootedMarkers (image := reached outcome) (batches := batches)
      (by rw [← parity]; exact old) read earlier
    obtain ⟨opened, state, stable, again⟩ := reopen_selected selected tail bounded (by omega)
    exact ⟨_, _, opened, rfl, state, .inl rfl, (fun returned ack => (noAck returned ack).elim), stable, again⟩
  have oldOther : ∃ sibling : Option Marker, decodeMarker slot (before.marker slot).durable = .ok sibling ∧
      ∀ m, sibling = some m → m.lastSeq < batches.length := by
    simpa only [← oldSeq] using markerEntry.other
  have newDifferent : (before.marker slot).durable ≠ newRecord := by
    obtain ⟨sibling, beforeDecoded, beforeOlder⟩ := oldOther
    intro same
    have nextDecode := decodeMarker_encode (cursor.endPos + bytes.length) cursor.nextSeq
      (by omega) newBound newFields
    change decodeMarker slot newRecord = .ok (some ⟨cursor.endPos + bytes.length, cursor.nextSeq⟩) at nextDecode
    rw [same, nextDecode] at beforeDecoded
    have sameRecord := Except.ok.inj beforeDecoded
    have contradiction := beforeOlder ⟨cursor.endPos + bytes.length, cursor.nextSeq⟩ sameRecord.symm
    simp only at contradiction
    omega
  have acknowledgedWrites {returned : Cursor} (ack : acknowledged outcome = some returned) :
      (boot.marker slot).live = newRecord := by
    obtain ⟨nextEq, _, synchronized⟩ := advance.ack returned ack
    rw [Image.marker_afterPowerLoss, synchronized rfl, nextEq]
  have changes := advance.markerOutcome
  change SlotOutcome slot (before.marker slot).durable newRecord ((reached outcome).marker slot).durable at changes
  rcases changes with unchanged | ⟨count, persisted⟩ | damaged
  · obtain ⟨sibling, observed, earlier⟩ := oldOther
    apply openOld sibling (by rwa [Image.marker_afterPowerLoss, unchanged]) earlier
    intro returned ack
    exact newDifferent (unchanged.symm.trans ((Image.marker_afterPowerLoss _ _).symm.trans (acknowledgedWrites ack)))
  · have live : (boot.marker slot).live = newRecord.take count := (Image.marker_afterPowerLoss _ _).trans persisted
    have recordSize : newRecord.length = markerSize := rfl
    by_cases short : count < newRecord.length
    · have shortRead : ((boot.marker slot).live).length < markerSize := by
        rw [live, List.length_take, Nat.min_eq_left (Nat.le_of_lt short), ← recordSize]
        exact short
      apply openOld none (decodeMarker_short slot shortRead) (by simp)
      intro returned ack
      rw [acknowledgedWrites ack, ← recordSize] at shortRead
      omega
    · have complete : (boot.marker slot).live = newRecord :=
        live.trans (List.take_of_length_le (Nat.le_of_not_gt short))
      have changed : (reached outcome).marker slot ≠ before.marker slot := by
        intro same
        exact newDifferent ((congrArg FileImage.durable same).symm.trans ((Image.marker_afterPowerLoss _ _).symm.trans complete))
      have synced : boot.data.live = prior ++ bytes :=
        congrArg FileImage.durable (advance.markerRequiresSync changed).2
      let retained := batches ++ [payload]
      have snoc : encodeFrames 1 retained = prior ++ bytes := encodeFrames_snoc _ _ _
      have retainedLength : (encodeFrames 1 retained).length = cursor.endPos + bytes.length := by
        rw [snoc, List.length_append, oldPosition]
      have retainedSequence : retained.length = cursor.nextSeq := by simp [retained, next, Nat.add_comm]
      have rotate : (1 + retained.length) % 2 = oldSlot := by
        rw [retainedSequence, parity]
        omega
      have selected := BoundaryEntry.ofRebootedMarkers (image := reached outcome) (batches := retained)
        (by rw [retainedLength, retainedSequence]; exact complete)
        (by rw [rotate]; exact oldDecoded)
        (by intro m h
            cases Option.some.inj h
            change batches.length < retained.length
            rw [retainedSequence]
            omega)
      obtain ⟨opened, state, stable, again⟩ := reopen_selected (suffix := []) selected
        (by rw [List.append_nil, snoc]; exact synced)
        (by intro b member
            rcases List.mem_append.mp member with prior | fresh
            · exact bounded b prior
            · simpa using (List.mem_singleton.mp fresh ▸ wellSized))
        (by omega)
      exact ⟨_, _, opened, rfl, state, .inr rfl, (fun _ _ => rfl), stable, again⟩
  · have invalid : decodeMarker slot (boot.marker slot).live = .ok none := by
      rwa [Image.marker_afterPowerLoss]
    apply openOld none invalid (by simp)
    intro returned ack
    rw [acknowledgedWrites ack] at invalid
    have valid := decodeMarker_encode (cursor.endPos + bytes.length) cursor.nextSeq (by omega) newBound newFields
    change decodeMarker slot newRecord = .ok (some _) at valid
    rw [valid] at invalid
    cases invalid

/-- A crash between calls starts from settled data and the last durable
selection. Healthy reopen returns that canonical history and the exact
reboot image, with the same invariant for subsequent operations. -/
theorem ready_powerLoss_reopen {policy : Policy} {image : Image} {batches : List Bytes}
    (ready : Ready policy image batches) (bounded : ∀ b ∈ batches, b.length ≤ 32)
    (fits : batches.length ≤ 255) :
    let rebooted := image.powerLoss
    let decoded : Decoded := ⟨batches, historyCursor batches⟩
    (reopen (ops healthyReopen) policy).run rebooted = .ok (.ok decoded) rebooted ∧
    Ready policy rebooted batches ∧ rebooted.powerLoss = rebooted ∧
    (reopen (ops healthyReopen) policy).run rebooted.powerLoss = .ok (.ok decoded) rebooted := by
  intro rebooted decoded
  have data : rebooted.data = ⟨encodeFrames 1 batches, encodeFrames 1 batches⟩ := by
    change image.data.powerLoss = _
    rw [ready.1.1]
    rfl
  have same : ({rebooted with data := ⟨encodeFrames 1 batches, encodeFrames 1 batches⟩} : Image) =
      rebooted := by
    exact congrArg (fun data => {rebooted with data}) data.symm
  cases policy with
  | logOnly =>
    have opened := reopen_logOnly_again image batches bounded fits
    simp only at opened
    rw [same] at opened
    have exactOpen : (reopen (ops healthyReopen) .logOnly).run rebooted = .ok (.ok decoded) rebooted := opened
    exact ⟨exactOpen, ⟨⟨data, rfl⟩, fun branch => by cases branch⟩, rfl, exactOpen⟩
  | boundary =>
    have physical : rebooted.data.live = encodeFrames 1 batches ++ [] := by
      rw [data, List.append_nil]
    have opened := reopen_selected (ready.2 rfl).powerLoss physical bounded fits
    simp only at opened
    rwa [same] at opened

/-- Every finite sequence of further power losses and healthy opens
preserves the decoded result and the exact file image. -/
theorem repeats_healthyReopen {policy : Policy} {decoded : Decoded} {after : Image}
    (stable : (reopen (ops healthyReopen) policy).run after.powerLoss = .ok (.ok decoded) after) (count : Nat) :
    (List.replicate count ()).foldl
      (fun previous _ => (reopen (ops healthyReopen) policy).run (reached previous).powerLoss)
      (.ok (.ok decoded) after) = .ok (.ok decoded) after := by
  induction count with
  | zero => rfl
  | succ count prior => simpa only [List.replicate_succ, List.foldl_cons, reached, stable] using prior

end WalRecoverySlice.Persistence
