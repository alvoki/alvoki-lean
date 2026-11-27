import Alvoki.Experiments.WAL.Proofs.DirtyRetry

namespace WalRecoverySlice.Persistence

private theorem liveSnapshot_eq_of_clean {s : Image} (clean : s.powerLoss = s) :
    s.liveSnapshot = s := by
  obtain ⟨⟨dl, dd⟩, ⟨al, ad⟩, ⟨bl, bd⟩⟩ := s
  simp [Image.powerLoss, FileImage.powerLoss] at clean
  obtain ⟨rfl, rfl, rfl⟩ := clean
  rfl

private theorem clean_slots {s : Image} (clean : s.powerLoss = s) (slot : Nat) :
    (s.marker slot).live = (s.marker slot).durable := by
  have slot0 := congrArg (fun i => i.slot0.live) clean
  have slot1 := congrArg (fun i => i.slot1.live) clean
  by_cases h : slot = 0
  · simpa [Image.marker, h] using (show s.slot0.live = s.slot0.durable from slot0.symm)
  · simpa [Image.marker, h] using (show s.slot1.live = s.slot1.durable from slot1.symm)

private theorem settled_slots {s : Image} {slot : Nat}
    (here : (s.marker (slot % 2)).live = (s.marker (slot % 2)).durable)
    (other : (s.marker (1 - slot % 2)).live = (s.marker (1 - slot % 2)).durable) :
    s.MarkersSettled := by
  have parity : slot % 2 = 0 ∨ slot % 2 = 1 := by omega
  rcases parity with h | h <;> simp [h, Image.marker] at here other <;> first
    | exact ⟨here, other⟩
    | exact ⟨other, here⟩

private theorem effectOfReady {p} (e : Effects) {s : Image} {known : List Bytes} (payload : Bytes)
    (entry : Ready p s known) (bounded : ∀ b ∈ known, b.length ≤ 32) (fits : known.length < 255)
    (wellSized : payload.length ≤ 32) :
    AppendEffects p (historyCursor known) payload (encodeFrames 1 known) s
      ((appendBatch (ops e) p (historyCursor known) payload).run s) := by
  have size := encoded_history_size known 1 bounded
  apply appendBatch_effects _ _ _ _ _ _ entry.1 wellSized
  · simp [historyCursor]
  · simp [historyCursor]; omega
  · simp only [historyCursor, frame_length]; omega

private theorem otherClean {p c b prior s r} (effect : AppendEffects p c b prior s r)
    (clean : s.powerLoss = s) :
    ((reached r).marker (1 - c.nextSeq % 2)).live =
      ((reached r).marker (1 - c.nextSeq % 2)).durable := by
  rw [effect.otherMarkerUnchanged]
  apply clean_slots clean

theorem appendBatch_logOnly_markers (e : Effects) (s : Image) (known : List Bytes) (payload : Bytes)
    (entry : Ready .logOnly s known) (clean : s.powerLoss = s)
    (bounded : ∀ b ∈ known, b.length ≤ 32) (fits : known.length < 255) (wellSized : payload.length ≤ 32) :
    (reached ((appendBatch (ops e) .logOnly (historyCursor known) payload).run s)).MarkersSettled := by
  have effect := effectOfReady e payload entry bounded fits wellSized
  apply settled_slots _ (otherClean effect clean)
  by_cases eqn : (reached ((appendBatch (ops e) .logOnly (historyCursor known) payload).run s)).marker ((historyCursor known).nextSeq % 2) = s.marker ((historyCursor known).nextSeq % 2)
  · rw [eqn]; exact clean_slots clean _
  · cases (effect.markerRequiresSync eqn).1

theorem appendBatch_ack_clean (p : Policy) (e : Effects) (s : Image) (known : List Bytes) (payload : Bytes)
    (entry : Ready p s known) (clean : s.powerLoss = s) (bounded : ∀ b ∈ known, b.length ≤ 32)
    (fits : known.length < 255) (wellSized : payload.length ≤ 32) {returned : Cursor}
    (ack : acknowledged ((appendBatch (ops e) p (historyCursor known) payload).run s) = some returned) :
    (reached ((appendBatch (ops e) p (historyCursor known) payload).run s)).powerLoss =
      reached ((appendBatch (ops e) p (historyCursor known) payload).run s) := by
  have effect := effectOfReady e payload entry bounded fits wellSized
  obtain ⟨_, data, dest⟩ := effect.ack returned ack
  apply Image.stableDataAndMarkers (by rw [data])
  cases p with
  | logOnly => exact appendBatch_logOnly_markers e s known payload entry clean bounded fits wellSized
  | boundary => exact settled_slots (by rw [dest rfl]) (otherClean effect clean)

private theorem boundary_input_of_open {s : Image} {d : Decoded} {after : Image}
    (clean : s.powerLoss = s)
    (opened : (reopen (ops healthyReopen) .boundary).run s = .ok (.ok d) after)
    (ready : Ready .boundary after d.batches) :
    BoundaryEntry s (historyCursor d.batches) ∧ ∃ suffix, s.data.live = encodeFrames 1 d.batches ++ suffix := by
  obtain ⟨marker, _, rfl⟩ := healthy_reopen_selection opened
  have unchanged : s.bothSynced marker = s := by
    simpa only [clean] using both_boot s marker
  rw [unchanged] at ready
  have auth := ready.2 rfl
  have data : s.data.live.take d.cursor.endPos = encodeFrames 1 d.batches :=
    congrArg FileImage.live ready.1.1
  constructor
  · exact auth.sameSlots (by intro slot; simp [Image.marker, Image.trimmed, Image.dataSettled])
  · exact ⟨s.data.live.drop d.cursor.endPos, by rw [← data, List.take_append_drop]⟩

private theorem append_durable_view (p : Policy) (e : Effects) (s : Image) (known : List Bytes)
    (payload : Bytes) (ready : Ready p s known) (bounded : ∀ b ∈ known, b.length ≤ 32)
    (fits : known.length < 255) (wellSized : payload.length ≤ 32) :
    ReplayView p known (some payload)
      (reached ((appendBatch (ops e) p (historyCursor known) payload).run s)).powerLoss := by
  cases p with
  | logOnly => exact (effectOfReady e payload ready bounded fits wellSized).durablePrefix
  | boundary =>
    have ext : (encodeFrames 1 known).length + (frame (1 + known.length) payload).length ≤ 65535 := by
      have size := encoded_history_size known 1 bounded
      rw [frame_length]; omega
    obtain ⟨d, after, opened, _, installed, choices, _, _, _⟩ :=
      appendBatch_reopens_boundary e s known payload ready.1 (ready.2 rfl) bounded fits wellSized ext
    exact ⟨d.batches, choices, boundary_input_of_open rfl opened installed⟩

private theorem powerLoss_snapshot_result {α} (r : Result α) :
    (reached (Result.liveSnapshot r)).powerLoss = (reached r).liveSnapshot := by
  cases r <;> rfl

/-- Every attempted append leaves enough authority for either kind of
restart. Only the candidate slot can become dirty, after complete data sync. -/
theorem appendBatch_dirty (p : Policy) (e : Effects) (s : Image) (known : List Bytes)
    (payload : Bytes) (entry : Ready p s known) (clean : s.powerLoss = s)
    (bounded : ∀ b ∈ known, b.length ≤ 32) (fits : known.length < 255) (wellSized : payload.length ≤ 32) :
    Dirty p known (some payload) (reached ((appendBatch (ops e) p (historyCursor known) payload).run s)) := by
  constructor
  · intro b hb; rcases List.mem_append.mp hb with old | fresh
    · exact bounded b old
    · simpa using (List.mem_singleton.mp fresh ▸ wellSized)
  · simp; omega
  · have ready : Ready p s.liveSnapshot known := liveSnapshot_eq_of_clean clean ▸ entry
    have view := append_durable_view p e.mirrorLive s.liveSnapshot known payload ready bounded fits wellSized
    rwa [appendBatch_liveSnapshot, powerLoss_snapshot_result] at view
  · exact append_durable_view p e s known payload entry bounded fits wellSized
  · intro _
    let c := historyCursor known
    let r := (appendBatch (ops e) p c payload).run s
    have effect := effectOfReady e payload entry bounded fits wellSized
    have other := otherClean effect clean
    by_cases eqn : (reached r).marker (c.nextSeq % 2) = s.marker (c.nextSeq % 2)
    · exact .inl (settled_slots (by rw [eqn]; exact clean_slots clean _) other)
    · have data := (effect.markerRequiresSync eqn).2
      refine .inr ⟨by rw [data], ?_⟩
      have parity : c.nextSeq % 2 = 0 ∨ c.nextSeq % 2 = 1 := by omega
      change ((reached r).marker (1 - c.nextSeq % 2)).live = ((reached r).marker (1 - c.nextSeq % 2)).durable at other
      rcases parity with h | h
      · right; simpa [h, Image.marker] using other
      · left; simpa [h, Image.marker] using other

/-- A process may exit between calls. With no submission in flight either
restart view describes the one settled history. -/
theorem ready_dirty (p : Policy) (s : Image) (known : List Bytes)
    (entry : Ready p s known) (clean : s.powerLoss = s)
    (bounded : ∀ b ∈ known, b.length ≤ 32) (fits : known.length ≤ 255) :
    Dirty p known none s := by
  have view : ReplayView p known none s := by
    have data := congrArg FileImage.live entry.1.1
    cases p with
    | logOnly => exact ⟨0, by simpa using data⟩
    | boundary => exact ⟨known, .inl rfl, entry.2 rfl, [], by simpa using data⟩
  refine ⟨by simpa using bounded, by simpa using fits, ?_, ?_, fun _ => .inl ?_⟩
  · rwa [liveSnapshot_eq_of_clean clean]
  · rwa [clean]
  · exact ⟨clean_slots clean 0, clean_slots clean 1⟩

end WalRecoverySlice.Persistence
