import Alvoki.Experiments.WAL.Proofs.Retry

/-! Policy distinctions on the same observed segment bytes. -/

namespace WalRecoverySlice.Persistence

private theorem Image.markerSync_keepsData (before : Image) (slot : Nat) (file : FileImage) :
    (before.withMarker slot file).data = before.data := by
  by_cases zero : slot = 0 <;> simp [Image.withMarker, zero]

private theorem Image.bothSynced_keepsData (before : Image) (marker : Option Marker) :
    (before.bothSynced marker).data = before.data := by
  cases marker with
  | none => rfl
  | some selected =>
    change ((before.withMarker (selected.lastSeq % 2) _).withMarker (1 - selected.lastSeq % 2) _).data = _
    rw [Image.markerSync_keepsData, Image.markerSync_keepsData]

private theorem reopen_canonical {policy : Policy} {before : Image} {marker : Option Marker}
    {batches : List Bytes}
    (selection : ReopenSelection policy before marker ⟨batches, historyCursor batches⟩)
    (bytes : before.data.live.take (historyCursor batches).endPos = encodeFrames 1 batches) :
    ∃ after, (reopen (ops healthyReopen) policy).run before =
      .ok (.ok ⟨batches, historyCursor batches⟩) after ∧
      AtEnd after (historyCursor batches) (encodeFrames 1 batches) := by
  refine ⟨_, reopen_selected_healthy selection, ⟨?_, rfl⟩⟩
  change FileImage.mk
    ((before.bothSynced marker).data.live.take (historyCursor batches).endPos)
    ((before.bothSynced marker).data.live.take (historyCursor batches).endPos) = _
  rw [Image.bothSynced_keepsData, bytes]

private theorem reopen_logOfEncoded {before : Image} {batches : List Bytes}
    (physical : before.data.live = encodeFrames 1 batches)
    (bounded : ∀ b ∈ batches, b.length ≤ 32) (fits : batches.length ≤ 255) :
    ∃ after, (reopen (ops healthyReopen) .logOnly).run before =
      .ok (.ok ⟨batches, historyCursor batches⟩) after ∧
      AtEnd after (historyCursor batches) (encodeFrames 1 batches) := by
  apply reopen_canonical (marker := none)
  · change scan before.data.live before.data.live.length .logOnly = _
    rw [physical]
    exact scan_encodeFrames .logOnly bounded fits
  · rw [physical]
    exact List.take_length

/-- With a complete extra frame on disk, log-only recovery adopts it.
The boundary policy returns the marker's history and settles the
truncated segment. Both calls start with the same physical image. -/
theorem reopen_unpublished_batch (before : Image) (history : List Bytes) (batch : Bytes)
    (physical : before.data.live = encodeFrames 1 (history ++ [batch]))
    (published : selectMarker before.slot0.live before.slot1.live =
      .ok ⟨(encodeFrames 1 history).length, history.length⟩)
    (bounded : ∀ b ∈ history ++ [batch], b.length ≤ 32) (fits : history.length < 255) :
    (∃ after, (reopen (ops healthyReopen) .logOnly).run before =
      .ok (.ok ⟨history ++ [batch], historyCursor (history ++ [batch])⟩) after ∧
      AtEnd after (historyCursor (history ++ [batch])) (encodeFrames 1 (history ++ [batch]))) ∧
    (∃ after, (reopen (ops healthyReopen) .boundary).run before =
      .ok (.ok ⟨history, historyCursor history⟩) after ∧
      AtEnd after (historyCursor history) (encodeFrames 1 history)) := by
  have extendedFits : (history ++ [batch]).length ≤ 255 := by simp; omega
  refine ⟨reopen_logOfEncoded physical bounded extendedFits, ?_⟩
  let suffix := frame (1 + history.length) batch
  have observed : before.data.live = encodeFrames 1 history ++ suffix :=
    physical.trans (encodeFrames_snoc 1 history batch)
  apply reopen_canonical (marker := some ⟨(encodeFrames 1 history).length, history.length⟩)
  · refine ⟨published, ?_, by simp [historyCursor, Nat.add_comm]⟩
    change scan before.data.live (encodeFrames 1 history).length .boundary = _
    rw [observed]
    exact scan_encodeFrames_append suffix .boundary
      (fun b member => bounded b (List.mem_append_left _ member)) (Nat.le_of_lt fits)
  · simp [observed, historyCursor]

/-- An intact selected marker whose byte limit exceeds the observed
segment makes boundary recovery report the missing data without repairing
the image. No condition on the observed prefix's contents is needed. -/
theorem reopen_missing_published_bytes {before : Image} {marker : Marker}
    (published : selectMarker before.slot0.live before.slot1.live = .ok marker)
    (short : before.data.live.length < marker.endPos) :
    (reopen (ops healthyReopen) .boundary).run before = .ok (.error "missing bytes") before := by
  have missing : scan before.data.live marker.endPos .boundary = .error "missing bytes" := by
    simp [scan, Nat.min_eq_right (Nat.le_of_lt short), Nat.ne_of_lt short,
      Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  have branch : (Policy.boundary == .boundary) = true := rfl
  simp [reopen, ops, healthyReopen, branch, published, missing, Bind.bind,
    ExceptT.run, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, EStateM.bind, ExceptT.pure,
    Pure.pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw]

/-- When the whole final published frame is absent, the same intact
shorter history can pass log-only recovery while boundary recovery
reports the missing bytes named by its marker. -/
theorem reopen_missing_published_batch (before : Image) (history : List Bytes) (batch : Bytes)
    (physical : before.data.live = encodeFrames 1 history)
    (published : selectMarker before.slot0.live before.slot1.live =
      .ok ⟨(encodeFrames 1 (history ++ [batch])).length, (history ++ [batch]).length⟩)
    (bounded : ∀ b ∈ history ++ [batch], b.length ≤ 32) (fits : history.length < 255) :
    (∃ after, (reopen (ops healthyReopen) .logOnly).run before =
      .ok (.ok ⟨history, historyCursor history⟩) after ∧
      AtEnd after (historyCursor history) (encodeFrames 1 history)) ∧
    (reopen (ops healthyReopen) .boundary).run before = .ok (.error "missing bytes") before := by
  refine ⟨reopen_logOfEncoded physical (fun b member => bounded b (List.mem_append_left _ member)) (Nat.le_of_lt fits),
    reopen_missing_published_bytes published ?_⟩
  change before.data.live.length < (encodeFrames 1 (history ++ [batch])).length
  rw [physical, encodeFrames_snoc, List.length_append, frame_length]
  omega

end WalRecoverySlice.Persistence
