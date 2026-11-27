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

/-- The selected marker delimits the entire published history. Any bytes after
it, of any length or provenance, are absent from both live and durable data
when healthy boundary recovery returns. -/
theorem reopen_unpublished_suffix (before : Image) (history : List Bytes) (suffix : Bytes)
    (physical : before.data.live = encodeFrames 1 history ++ suffix)
    (published : selectMarker before.slot0.live before.slot1.live =
      .ok ⟨(encodeFrames 1 history).length, history.length⟩)
    (bounded : ∀ b ∈ history, b.length ≤ 32) (fits : history.length ≤ 255) :
    ∃ after, (reopen (ops healthyReopen) .boundary).run before =
      .ok (.ok ⟨history, historyCursor history⟩) after ∧
      AtEnd after (historyCursor history) (encodeFrames 1 history) := by
  apply reopen_canonical (marker := some ⟨(encodeFrames 1 history).length, history.length⟩)
  · refine ⟨published, ?_, by simp [historyCursor, Nat.add_comm]⟩
    change scan before.data.live (encodeFrames 1 history).length .boundary = _
    rw [physical]
    exact scan_encodeFrames_append suffix .boundary bounded fits
  · simp [physical, historyCursor]

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
  exact reopen_unpublished_suffix before history _ (physical.trans (encodeFrames_snoc 1 history batch))
    published (fun b member => bounded b (List.mem_append_left _ member)) (Nat.le_of_lt fits)

/-- A decode error inside the published extent returns before the first
recovery write. Both marker slots and the segment retain their entry images. -/
theorem reopen_published_scan_error {before : Image} {marker : Marker} {err : String}
    (published : selectMarker before.slot0.live before.slot1.live = .ok marker)
    (failed : scan before.data.live marker.endPos .boundary = .error err) :
    (reopen (ops healthyReopen) .boundary).run before = .ok (.error err) before := by
  have branch : (Policy.boundary == .boundary) = true := rfl
  simp [reopen, ops, healthyReopen, branch, published, failed, Bind.bind,
    ExceptT.run, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, EStateM.bind, ExceptT.pure,
    Pure.pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw]

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
  exact reopen_published_scan_error published missing

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

/-- A boundary records length and sequence. Even with the original marker intact,
replacing the last batch by a different valid frame of equal payload length lets
both policies return the replacement. This is a storage fault outside Run. -/
theorem reopen_substituted_batch (before : Image) (history : List Bytes)
    (submitted replacement : Bytes) (different : submitted ≠ replacement)
    (sameSize : submitted.length = replacement.length)
    (physical : before.data.live = encodeFrames 1 (history ++ [replacement]))
    (published : selectMarker before.slot0.live before.slot1.live =
      .ok ⟨(encodeFrames 1 (history ++ [submitted])).length, history.length + 1⟩)
    (bounded : ∀ b ∈ history ++ [replacement], b.length ≤ 32)
    (fits : history.length < 255) :
    history ++ [replacement] ≠ history ++ [submitted] ∧
    ∀ policy, ∃ after, (reopen (ops healthyReopen) policy).run before =
      .ok (.ok ⟨history ++ [replacement], historyCursor (history ++ [replacement])⟩) after := by
  have size : (encodeFrames 1 (history ++ [submitted])).length =
      (encodeFrames 1 (history ++ [replacement])).length := by
    simp only [encodeFrames_snoc, List.length_append, frame_length, sameSize]
  rw [size] at published
  have count : (history ++ [replacement]).length ≤ 255 := by simp; omega
  refine ⟨by simpa using Ne.symm different, ?_⟩
  intro policy
  cases policy with
  | logOnly =>
    obtain ⟨after, result, _⟩ := reopen_logOfEncoded physical bounded count
    exact ⟨after, result⟩
  | boundary =>
    let cursor := historyCursor (history ++ [replacement])
    let marker : Marker := ⟨cursor.endPos, history.length + 1⟩
    have selected : ReopenSelection .boundary before (some marker)
        ⟨history ++ [replacement], cursor⟩ := by
      refine ⟨published, ?_, by simp [marker, cursor, historyCursor, Nat.add_comm]⟩
      change scan before.data.live (encodeFrames 1 (history ++ [replacement])).length .boundary = _
      rw [physical]
      exact scan_encodeFrames .boundary bounded count
    obtain ⟨after, result, _⟩ := reopen_canonical selected (by
      rw [physical]
      exact List.take_length)
    exact ⟨after, result⟩

end WalRecoverySlice.Persistence
