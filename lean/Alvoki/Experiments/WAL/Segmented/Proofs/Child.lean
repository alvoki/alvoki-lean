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

/-- A nested file call can replace only its own bytes and cursor. This
frame applies equally to success, a reported I/O error, and interruption. -/
theorem child_frame (named : id ∈ state.disk.liveNames) (run : Persistence.M α)
    (next : α → Cursor) (result : α → β) :
    ∃ image cursor, (reached (child state id run next result)).disk = state.disk.setSegment id image cursor := by
  rw [child_reached named]; exact ⟨_, _, rfl⟩

theorem openSegment_frame (e : Effects) (policy : Policy) (named : id ∈ state.disk.liveNames) :
    ∃ image cursor, (reached (((ops e).openSegment policy id).run state)).disk = state.disk.setSegment id image cursor :=
  child_frame named _ _ _

theorem appendSegment_frame (e : Effects) (policy : Policy) (payload : Bytes) (named : id ∈ state.disk.liveNames) :
    ∃ image cursor, (reached (((ops e).appendSegment policy id payload).run state)).disk = state.disk.setSegment id image cursor :=
  child_frame named _ _ _

theorem openSegment_selected (e : Effects) (named : id ∈ state.disk.liveNames)
    (sel : Child.Selects policy (state.disk.segment id) batches)
    (ok : returned (((ops e).openSegment policy id).run state) = some result) : result = batches := by
  obtain ⟨marker, decoded, selected, rfl⟩ := sel
  change returned (child state id _ Decoded.cursor Decoded.batches) = some result at ok
  rw [child_returned named] at ok
  obtain ⟨d, got, rfl⟩ := Option.map_eq_some_iff.mp ok
  exact congrArg Decoded.batches (scheduledReopen_selected selected _ _ d got)

/-- Each sealed open preserves its already-settled bytes at every cut. A
    successful callback returns the canonical segment and installs its cursor. -/
theorem openSegment_settled (effects : Effects) (named : id ∈ state.disk.liveNames)
    (entry : Child.Settled policy (state.disk.segment id) history)
    (bounded : ∀ b ∈ history, b.length ≤ 32) (fits : history.length ≤ 255) :
    let r := ((ops effects).openSegment policy id).run state
    (reached r).disk.segment id = state.disk.segment id ∧
    ∀ batches, returned r = some batches →
      batches = history ∧ Child.Installed policy ((reached r).disk.segment id) ((reached r).disk.cursor id) history := by
  let run := openChild effects state.step id policy
  have frame := child_reached named run Decoded.cursor Decoded.batches
  have ret := child_returned named run Decoded.cursor Decoded.batches
  have ⟨same, canonical⟩ := reopensSettledSegmentScheduled entry.ready entry.clean bounded fits (effects.openSegment state.step id) (effects.reopenWritebacks state.step id)
  change Persistence.reached (run.run (state.disk.segment id)) = _ at same
  change _ ∧ ∀ batches, returned (child state id run Decoded.cursor Decoded.batches) = some batches → _
  refine ⟨?_, ?_⟩
  · change (reached (child state id run Decoded.cursor Decoded.batches)).disk.segment id = _
    rw [frame, Disk.setSegment_here]; exact same
  · intro batches success
    rw [ret] at success
    obtain ⟨decoded, got, rfl⟩ := Option.map_eq_some_iff.mp success
    obtain rfl := canonical decoded got
    change _ ∧ Child.Installed policy ((reached (child state id run Decoded.cursor Decoded.batches)).disk.segment id)
      ((reached (child state id run Decoded.cursor Decoded.batches)).disk.cursor id) history
    rw [frame, Disk.setSegment_here, Disk.setCursor_here, got, same]
    exact ⟨rfl, entry, rfl⟩

/-- Failed recovery is retryable from this exact reached child. Returned
    batches determine both the installed cursor and the next append authority. -/
theorem openSegment_dirty (effects : Effects) (named : id ∈ state.disk.liveNames)
    (entry : Child.Recoverable policy known pending (state.disk.segment id)) :
    let r := ((ops effects).openSegment policy id).run state
    let image := (reached r).disk.segment id
    Child.Recoverable policy known pending image ∧
    ∀ batches, returned r = some batches →
      WalRecoverySlice.Contract.Permitted known pending batches ∧ Child.Installed policy image ((reached r).disk.cursor id) batches := by
  let run := openChild effects state.step id policy
  have frame := child_reached named run Decoded.cursor Decoded.batches
  have ret := child_returned named run Decoded.cursor Decoded.batches
  obtain ⟨retry, markers, success⟩ := reopensDirtySegmentScheduled entry.dirty (effects.openSegment state.step id) (effects.reopenWritebacks state.step id)
  dsimp only
  change _ ∧ ∀ batches, returned (child state id run Decoded.cursor Decoded.batches) = some batches → _
  simp only [ops, ExceptT.run] at *
  rw [frame, Disk.setSegment_here]
  refine ⟨⟨retry, fun log => markers (entry.markers log)⟩, ?_⟩
  intro batches h
  rw [ret] at h
  obtain ⟨d, got, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨allowed, cursor, ready, size, fits, clean⟩ := success d got
  refine ⟨allowed, ⟨ready, clean ?_⟩, ?_⟩
  · cases hp : policy with
    | logOnly => exact .inr (entry.markers hp)
    | boundary => exact .inl rfl
  · rw [Disk.setCursor_here, got]; exact cursor

theorem openSegment_healthy (named : id ∈ state.disk.liveNames)
    (entry : Child.Recoverable policy known pending (state.disk.segment id)) :
    ∃ batches, returned (((ops healthy).openSegment policy id).run state) = some batches := by
  obtain ⟨d, after, h⟩ := entry.dirty.healthy_reopen
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
    (entry : Child.Installed policy (state.disk.segment id) (state.disk.cursor id) known)
    (bounded : ∀ b ∈ known, b.length ≤ 32) (fits : known.length < 255)
    (size : payload.length ≤ 32) :
    let r := ((ops effects).appendSegment policy id payload).run state
    let image := (reached r).disk.segment id
    Child.Recoverable policy known (some payload) image ∧
    (returned r = some () →
      Child.Installed policy image ((reached r).disk.cursor id) (known ++ [payload])) := by
  let run := effects.appendRun state.step id policy (Persistence.historyCursor known) payload
  let next := fun c : Cursor => c
  let done_ := fun _ : Cursor => ()
  have frame := child_reached named run next done_
  have ret := child_returned named run next done_
  obtain ⟨dirty, markers, installed⟩ :=
    effects.appendRun_refines state.step id policy _ known payload entry.ready entry.clean bounded fits size
  simp only [ops, ExceptT.run, entry.position]
  change Child.Recoverable policy known (some payload) ((reached (child state id run next done_)).disk.segment id) ∧ _
  rw [frame, Disk.setSegment_here]
  refine ⟨⟨dirty, markers⟩, ?_⟩
  intro ok
  rw [ret] at ok
  obtain ⟨c, got, _⟩ := Option.map_eq_some_iff.mp ok
  rw [Disk.setCursor_here, got]
  obtain ⟨position, ready, clean⟩ := installed c got
  exact ⟨⟨ready, clean⟩, position⟩

end WalRecoverySlice.Segmented.Model
