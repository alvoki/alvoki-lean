import Alvoki.Experiments.WAL.Proofs.DirtyAppend

namespace WalRecoverySlice.Persistence

/-- Even if a complete frame is visible, the first append primitive returned
an error or interrupted. Neither data sync nor marker publication has run. -/
theorem tornAppend_stops (p : Policy) (cut : TornAppend) (s : Image) (cursor : Cursor) (submitted : Bytes)
    (sized : submitted.length ≤ 32) (positive : cursor.nextSeq ≠ 0) (fits : cursor.nextSeq ≤ 255)
    (extent : p = .boundary → cursor.endPos + (frame cursor.nextSeq submitted).length ≤ 65535) :
    (appendBatch cut.ops p cursor submitted).run s =
      cut.abort.result (cut.after s (frame cursor.nextSeq submitted)) := by
  rw [appendBatch_of_valid sized positive fits extent]
  obtain ⟨live, durable, abort⟩ := cut
  cases abort <;> rfl

private theorem first_twelve (seq : Nat) (payload : Bytes) :
    (frame seq payload).take 12 =
      [42, 1, seq.toUInt8, payload.length.toUInt8] ++
        checksumBytes [42, 1, seq.toUInt8, payload.length.toUInt8] := by
  rfl

private theorem DataResidue.logTail {known : List Bytes} {submitted : Bytes} (residue : DataResidue)
    (extent : residue.SameExtent submitted) (bad : residue.Detected (1 + known.length)) :
    LogTail known (some submitted) (residue.bytes (frame (1 + known.length) submitted)) := by
  cases residue with
  | «prefix» n => exact .cut n
  | torn observed trailer =>
    obtain ⟨len, width⟩ := extent
    simpa [DataResidue.bytes, first_twelve, frameWithTrailer, len] using
      (show LogTail known (some submitted) (frameWithTrailer (1 + known.length) observed trailer) from
        .damaged rfl len width bad)

/-- Marker files are untouched before the data barrier. Log-only recovery
classifies the tail, while boundary recovery uses the previously selected extent. -/
private theorem DataResidue.replayView {p : Policy} {s view : Image} {known : List Bytes} {submitted : Bytes}
    (residue : DataResidue) (entry : Ready p s known) (sameExtent : residue.SameExtent submitted)
    (detected : p = .logOnly → residue.Detected (historyCursor known).nextSeq)
    (data : view.data.live = encodeFrames 1 known ++ residue.bytes (frame (historyCursor known).nextSeq submitted))
    (markers : ∀ slot, (view.marker slot).durable = (s.marker slot).durable) :
    ReplayView p known (some submitted) view := by
  cases p with
  | logOnly => exact ⟨_, residue.logTail sameExtent (detected rfl), data⟩
  | boundary => exact ⟨known, .inl rfl, (entry.2 rfl).sameSlots markers, _, data⟩

theorem tornAppend_dirty (p : Policy) (cut : TornAppend) (s : Image) (known : List Bytes)
    (submitted : Bytes) (entry : Ready p s known) (clean : s.powerLoss = s)
    (bounded : ∀ b ∈ known, b.length ≤ 32) (fits : known.length < 255) (wellSized : submitted.length ≤ 32)
    (sameExtent : cut.SameExtent submitted) (detected : p = .logOnly → cut.Detected (historyCursor known).nextSeq) :
    let result := (appendBatch cut.ops p (historyCursor known) submitted).run s
    Dirty p known (some submitted) (reached result) ∧ (reached result).MarkersSettled := by
  have size := encoded_history_size known 1 bounded
  rw [tornAppend_stops p cut s _ submitted wellSized (by simp [historyCursor])
    (by simp [historyCursor]; omega) (by simp only [historyCursor, frame_length]; omega)]
  have stopped {α} (after : Image) : reached (cut.abort.result (α := α) after) = after := by
    cases cut.abort <;> rfl
  dsimp only
  rw [stopped]
  let requested := frame (historyCursor known).nextSeq submitted
  let after := cut.after s requested
  have markers : after.MarkersSettled := by
    change s.MarkersSettled
    rw [← clean]
    exact ⟨rfl, rfl⟩
  refine ⟨⟨?_, by simp; omega, ?_, ?_, fun _ => .inl markers⟩, markers⟩
  · intro b hb
    rcases List.mem_append.mp hb with old | new
    · exact bounded b old
    · simpa using (List.mem_singleton.mp new ▸ wellSized)
  · apply cut.live.replayView entry sameExtent.1 (fun log => (detected log).1)
    · change s.data.live ++ _ = _
      rw [entry.1.1]
    · intro slot
      by_cases zero : slot = 0 <;>
        simp [Image.marker, Image.liveSnapshot, FileImage.liveSnapshot, TornAppend.after, zero] <;>
        first | exact (congrArg (fun i => i.slot0.live) clean).symm
              | exact (congrArg (fun i => i.slot1.live) clean).symm
  · apply cut.durable.replayView entry sameExtent.2 (fun log => (detected log).2)
    · change s.data.durable ++ _ = _
      rw [entry.1.1]
    · intro slot
      by_cases zero : slot = 0 <;> simp [Image.marker, Image.powerLoss, FileImage.powerLoss,
        TornAppend.after, zero]

end WalRecoverySlice.Persistence
