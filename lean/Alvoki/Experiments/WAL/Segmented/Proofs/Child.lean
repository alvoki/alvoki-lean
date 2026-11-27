import Alvoki.Experiments.WAL.Segmented.Proofs.Model
import Alvoki.Experiments.WAL.Segmented.Proofs.SegmentRecovery
import Alvoki.Experiments.WAL.Segmented.Proofs.ScheduledAppend

namespace WalRecoverySlice.Segmented.Model
variable {id j : Nat} {state : State}

/-- The nested call installs its exact reached bytes even when it fails. Only
    a returned child value replaces that segment's cursor. -/
theorem child_reached (named : id ∈ state.disk.liveNames) (run : Persistence.M α)
    (next : α → Cursor) (result : α → β) :
    let inner := run.run (state.disk.segment id)
    let cursor := ((Persistence.acknowledged inner).map next).getD (state.disk.cursor id)
    reached (child state id run next result) =
      {state.tick with disk := state.disk.setSegment id (Persistence.reached inner) cursor} := by
  simp only [child, named, ↓reduceIte]
  cases h : run.run (state.disk.segment id) with
  | error => rfl
  | ok value s => cases value <;> rfl

theorem child_returned (named : id ∈ state.disk.liveNames) (run : Persistence.M α)
    (next : α → Cursor) (result : α → β) :
    returned (child state id run next result) =
      (Persistence.acknowledged (run.run (state.disk.segment id))).map result := by
  simp only [child, named, ↓reduceIte]
  cases h : run.run (state.disk.segment id) with
  | error => rfl
  | ok value s => cases value <;> rfl

@[simp] theorem Disk.setSegment_here (disk : Disk) (id : Nat) (image : DataImage) (cursor : Cursor) :
    (disk.setSegment id image cursor).segment id = image := by simp [Disk.setSegment]

@[simp] theorem Disk.setCursor_here (disk : Disk) (id : Nat) (image : DataImage) (cursor : Cursor) :
    (disk.setSegment id image cursor).cursor id = cursor := by simp [Disk.setSegment]

@[simp] theorem Disk.setSegment_other (disk : Disk) (image : DataImage) (cursor : Cursor) (other : j ≠ id) :
    (disk.setSegment id image cursor).segment j = disk.segment j := by simp [Disk.setSegment, other]

@[simp] theorem Disk.setCursor_other (disk : Disk) (image : DataImage) (cursor : Cursor) (other : j ≠ id) :
    (disk.setSegment id image cursor).cursor j = disk.cursor j := by simp [Disk.setSegment, other]

/-- Each sealed open preserves its already-settled bytes at every cut. A
    successful callback returns the canonical segment and installs its cursor. -/
theorem openSegment_settled (effects : Effects) (named : id ∈ state.disk.liveNames)
    (ready : Persistence.Ready policy (state.disk.segment id) history)
    (clean : (state.disk.segment id).powerLoss = state.disk.segment id)
    (bounded : ∀ b ∈ history, b.length ≤ 32) (fits : history.length ≤ 255) :
    let r := ((ops effects).openSegment policy id).run state
    (reached r).disk.segment id = state.disk.segment id ∧
    ∀ batches, returned r = some batches →
      batches = history ∧ (reached r).disk.cursor id = Persistence.historyCursor history := by
  let run := openChild effects state.step id policy
  have frame := child_reached named run Decoded.cursor Decoded.batches
  have ret := child_returned named run Decoded.cursor Decoded.batches
  have ⟨same, canonical⟩ := reopensSettledSegmentScheduled ready clean bounded fits (effects.openSegment state.step id) (effects.reopenWritebacks state.step id)
  change _ ∧ ∀ batches, returned (child state id run Decoded.cursor Decoded.batches) = some batches → _
  refine ⟨?_, ?_⟩
  · change (reached (child state id run Decoded.cursor Decoded.batches)).disk.segment id = _
    rw [frame, Disk.setSegment_here]; exact same
  · intro batches success
    rw [ret] at success
    obtain ⟨decoded, got, rfl⟩ := Option.map_eq_some_iff.mp success
    obtain rfl := canonical decoded got
    change _ ∧ (reached (child state id run Decoded.cursor Decoded.batches)).disk.cursor id = _
    rw [frame, Disk.setCursor_here, got]
    exact ⟨rfl, rfl⟩

/-- Failed recovery is retryable from this exact reached child. Returned
    batches determine both the installed cursor and the next append authority. -/
theorem openSegment_dirty (effects : Effects) (named : id ∈ state.disk.liveNames)
    (entry : Persistence.Dirty policy known pending (state.disk.segment id)) :
    let r := ((ops effects).openSegment policy id).run state
    let image := (reached r).disk.segment id
    Persistence.Dirty policy known pending image ∧
    ((state.disk.segment id).MarkersSettled → image.MarkersSettled) ∧
    ∀ batches, returned r = some batches →
      WalRecoverySlice.Contract.Permitted known pending batches ∧ (reached r).disk.cursor id = Persistence.historyCursor batches ∧
      Persistence.Ready policy image batches ∧ (∀ b ∈ batches, b.length ≤ 32) ∧ batches.length ≤ 255 ∧
      (policy = .boundary ∨ (state.disk.segment id).MarkersSettled → image.powerLoss = image) := by
  let run := openChild effects state.step id policy
  have frame := child_reached named run Decoded.cursor Decoded.batches
  have ret := child_returned named run Decoded.cursor Decoded.batches
  obtain ⟨retry, markers, success⟩ := reopensDirtySegmentScheduled entry (effects.openSegment state.step id) (effects.reopenWritebacks state.step id)
  dsimp only
  change _ ∧ _ ∧ ∀ batches, returned (child state id run Decoded.cursor Decoded.batches) = some batches → _
  simp only [ops, ExceptT.run] at *
  rw [frame, Disk.setSegment_here]
  refine ⟨retry, markers, ?_⟩
  intro batches h
  rw [ret] at h
  obtain ⟨d, got, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨allowed, cursor, ready, size, fits, clean⟩ := success d got
  refine ⟨allowed, ?_, ready, size, fits, clean⟩
  rw [Disk.setCursor_here, got]
  exact cursor

theorem openSegment_healthy (named : id ∈ state.disk.liveNames)
    (entry : Persistence.Dirty policy known pending (state.disk.segment id)) :
    ∃ batches, returned (((ops healthy).openSegment policy id).run state) = some batches := by
  obtain ⟨d, after, h⟩ := entry.healthy_reopen
  refine ⟨d.batches, ?_⟩
  change returned (child state id _ Decoded.cursor Decoded.batches) = _
  rw [child_returned named]
  change (Persistence.acknowledged ((WalRecoverySlice.reopen (Persistence.ops Persistence.healthyReopen) policy).run
    (state.disk.segment id))).map Decoded.batches = _
  rw [h]; rfl

/-- An attempted append leaves the one issued batch pending at every cut.
    A successful callback instead installs the extended canonical cursor and
    leaves a settled file ready for the next call. -/
theorem appendSegment_dirty (effects : Effects) (named : id ∈ state.disk.liveNames)
    (entry : Persistence.Ready policy (state.disk.segment id) known)
    (clean : (state.disk.segment id).powerLoss = state.disk.segment id)
    (cursor : state.disk.cursor id = Persistence.historyCursor known)
    (bounded : ∀ b ∈ known, b.length ≤ 32) (fits : known.length < 255)
    (size : payload.length ≤ 32) :
    let r := ((ops effects).appendSegment policy id payload).run state
    let image := (reached r).disk.segment id
    Persistence.Dirty policy known (some payload) image ∧
    (policy = .logOnly → image.MarkersSettled) ∧
    (returned r = some () →
      (reached r).disk.cursor id = Persistence.historyCursor (known ++ [payload]) ∧
      Persistence.Ready policy image (known ++ [payload]) ∧ image.powerLoss = image) := by
  let run := effects.appendRun state.step id policy (Persistence.historyCursor known) payload
  let next := fun c : Cursor => c
  let done_ := fun _ : Cursor => ()
  have frame := child_reached named run next done_
  have ret := child_returned named run next done_
  obtain ⟨dirty, markers, installed⟩ :=
    effects.appendRun_refines state.step id policy _ known payload entry clean bounded fits size
  simp only [ops, ExceptT.run, cursor]
  change Persistence.Dirty policy known (some payload) ((reached (child state id run next done_)).disk.segment id) ∧ _
  rw [frame, Disk.setSegment_here]
  refine ⟨dirty, markers, ?_⟩
  intro ok
  rw [ret] at ok
  obtain ⟨c, got, _⟩ := Option.map_eq_some_iff.mp ok
  rw [Disk.setCursor_here, got]
  exact installed c got

end WalRecoverySlice.Segmented.Model
