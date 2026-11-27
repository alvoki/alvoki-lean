import Alvoki.Experiments.WAL.Proofs.DirtyAppend
import Alvoki.Experiments.WAL.Proofs.NativeAppend
import Alvoki.Experiments.WAL.Proofs.Client
import Alvoki.Experiments.WAL.Proofs.ReopenWriteback

/-! Recovery of segments already sealed by the directory protocol. -/

namespace WalRecoverySlice.Segmented

open Persistence

namespace Child

/-- A child whose canonical batch sequence survives a reboot byte-for-byte. -/
structure Settled (policy : Policy) (image : Image) (history : List Bytes) : Prop where
  ready : Ready policy image history
  clean : image.powerLoss = image

/-- The live child handle is positioned exactly after the settled batches. -/
structure Installed (policy : Policy) (image : Image) (cursor : Cursor) (history : List Bytes) : Prop
    extends Settled policy image history where
  position : cursor = historyCursor history

/-- Every retry may recover the old sequence or the single pending batch.
In log-only mode the unused marker files remain settled across repairs. -/
structure Recoverable (policy : Policy) (history : List Bytes) (pending : Option Bytes) (image : Image) : Prop where
  dirty : Dirty policy history pending image
  markers : policy = .logOnly → image.MarkersSettled

theorem Installed.fresh (policy : Policy) : Installed policy freshImage {} [] :=
  ⟨⟨fresh_ready policy, rfl⟩, rfl⟩

theorem Settled.recoverable {policy image history} (s : Settled policy image history)
    (bounded : ∀ b ∈ history, b.length ≤ 32) (fits : history.length ≤ 255) :
    Recoverable policy history none image := by
  refine ⟨ready_dirty policy _ _ s.ready s.clean bounded fits, fun _ => ?_⟩
  rw [← s.clean]; exact ⟨rfl, rfl⟩

theorem Recoverable.powerLoss {policy history pending image} (r : Recoverable policy history pending image) :
    Recoverable policy history pending image.powerLoss := ⟨r.dirty.powerLoss, fun _ => ⟨rfl, rfl⟩⟩

theorem Recoverable.settle {policy history pending image} (r : Recoverable policy history pending image) (file : WalFile) :
    Recoverable policy history pending (file.settle image) :=
  ⟨r.dirty.writeback (file.writeback image), fun log => (file.writeback image).keepsMarkersSettled (r.markers log)⟩

theorem Settled.writeback {policy image history} (s : Settled policy image history) (file : WalFile) :
    file.settle image = image := file.settle_clean image s.clean

/-- The descriptor-level single-file worker produces the state needed by
the segmented child contract at its actual return or failure. -/
theorem Recoverable.nativeRecovery (prior : Recoverable policy known pending image) (effects : Effects) :
    let result := (SingleFile.recover effects policy).run image
    Recoverable policy known pending (reached result) ∧
      ∀ decoded, acknowledged result = some decoded →
        WalRecoverySlice.Contract.Permitted known pending decoded.batches ∧
        Installed policy (reached result) decoded.cursor decoded.batches := by
  intro result
  obtain ⟨retry, markers, returned⟩ := SingleFile.recover_refines effects prior.dirty
  refine ⟨⟨retry, fun log => markers (prior.markers log)⟩, ?_⟩
  intro decoded success
  obtain ⟨allowed, cursor, ready, _, _, clean⟩ := returned decoded success
  have physical : policy = .boundary ∨ image.MarkersSettled := by
    cases policy with
    | boundary => exact Or.inl rfl
    | logOnly => exact Or.inr (prior.markers rfl)
  exact ⟨allowed, ⟨⟨ready, clean physical⟩, cursor⟩⟩

/-- The public single-file acquisition, recovery and scan supply the child
contract without assuming a successful native open callback. -/
theorem Recoverable.nativeOpen (dir : System.FilePath) (reports : SingleFile.OpenReports)
    (start : SingleFile.OpenImage) (free : start.held = false)
    (prior : Recoverable policy known pending start.image) :
    let result := SingleFile.openExistingModel dir policy reports start
    Recoverable policy known pending (SingleFile.postState result).image ∧
    match result with
    | .ok (.ok ready) after =>
      after.held = true ∧ after.policyDurable = true ∧ after.namesDurable = true ∧
      WalRecoverySlice.Contract.Permitted known pending ready.recovered.batches ∧
      Installed policy after.image ready.recovered.cursor ready.recovered.batches ∧
      (SingleFile.scanWith (SingleFile.storedPhase ready) : SingleFile.OpenM _).run after =
        .ok (.ok ready.recovered.batches) after
    | .ok (.error _) after | .error _ after => after.held = false := by
  have facts := SingleFile.openExisting_refines dir policy reports start free prior.dirty prior.markers
  refine ⟨⟨facts.1, facts.2.1⟩, ?_⟩
  have result := facts.2.2
  cases ran : SingleFile.openExistingModel dir policy reports start with
  | error => rw [ran] at result; exact result
  | ok value after =>
    rw [ran] at result
    cases value with
    | error => exact result
    | ok ready =>
      obtain ⟨_, _, _, _, _, held, stamp, names, chosen, cursor, valid, settled, installed⟩ := result
      exact ⟨held, stamp, names, chosen, ⟨⟨valid, settled⟩, cursor⟩, SingleFile.scan_opened ready after installed⟩

/-- Compose the public open producer with append on its exact stored
writer and marker bindings. The single-file contract lifts directly to
the child recovery or installation required by the segmented schedule. -/
theorem Recoverable.nativeAppendAfterOpen (dir : System.FilePath)
    (openReports : SingleFile.OpenReports) (start : SingleFile.OpenImage)
    (free : start.held = false) (prior : Recoverable policy known pending start.image)
    (returned : SingleFile.openExistingModel dir policy openReports start = .ok (.ok ready) after)
    (reports : ∀ cursor, SingleFile.AppendReports policy cursor batch)
    (room : ready.recovered.batches.length < 255) (size : batch.length ≤ 32) :
    let old := ready.recovered.batches
    let result := SingleFile.appendModel reports ⟨after.image, SingleFile.storedPhase ready⟩
    Recoverable policy old (some batch) (SingleFile.appendReached result).image ∧
    SingleFile.AppendGuarantee policy old batch result ∧
    match result with
    | .ok (.ok ()) next =>
      Installed policy next.image (historyCursor (old ++ [batch])) (old ++ [batch])
    | .ok (.error _) _ | .error _ _ => True := by
  have opened := SingleFile.openExisting_refines dir policy openReports start free prior.dirty prior.markers
  rw [returned] at opened
  have bindings := SingleFile.openedAppendPhase opened
  obtain ⟨_, _, _, _, _, _, _, _, permitted, _, entry, clean, _⟩ := opened.2.2
  have bounded : ∀ b ∈ ready.recovered.batches, b.length ≤ 32 := by
    intro b member
    apply prior.dirty.bounded b
    rcases permitted with same | same
    · exact List.mem_append_left _ (same ▸ member)
    · exact same ▸ member
  have appended := SingleFile.append_refines reports entry clean bounded room size
  simp only [bindings]
  refine ⟨⟨appended.1, appended.2.1⟩, appended, ?_⟩
  have outcome := appended.2.2
  cases run : SingleFile.appendModel reports
      ⟨after.image, .active .lock (SingleFile.appendBindings policy)
        (historyCursor ready.recovered.batches) ready.recovered.batches⟩ with
  | error => trivial
  | ok response _ =>
    cases response with
    | error => trivial
    | ok ack =>
      cases ack
      rw [run] at outcome
      obtain ⟨_, _, valid, settled⟩ := outcome
      exact ⟨⟨valid, settled⟩, rfl⟩

/-- A retry after close selects only an admitted history. Closing that
recovered handle pins the same history for the next successful open. -/
theorem Recoverable.nativeReopenTwice (dir : System.FilePath)
    (first cleanup second : SingleFile.OpenReports)
    (start : SingleFile.OpenImage) (free : start.held = false)
    (entry : Recoverable policy known pending start.image)
    (opened : SingleFile.openExistingModel dir policy first start = .ok (.ok ready) after)
    (reopened : SingleFile.openExistingModel dir policy second
      (SingleFile.postState (SingleFile.closeModel policy cleanup (SingleFile.storedPhase ready) after)) =
      .ok (.ok again) final) :
    WalRecoverySlice.Contract.Permitted known pending ready.recovered.batches ∧
      again.recovered.batches = ready.recovered.batches := by
  have found := SingleFile.openExisting_refines dir policy first start free entry.dirty entry.markers
  rw [opened] at found
  obtain ⟨lock, _, _, _, _, _, _, _, permitted, cursor, valid, settled, phase⟩ := found.2.2
  have release := SingleFile.close_opened policy cleanup ready lock after phase
  have bounds : ∀ b ∈ ready.recovered.batches, b.length ≤ 32 := by
    intro b member
    apply entry.dirty.bounded b
    rcases permitted with same | same
    · exact List.mem_append_left _ (same ▸ member)
    · exact same ▸ member
  have fits : ready.recovered.batches.length ≤ 255 := by
    rcases permitted with same | same
    · rw [same]
      have bound := entry.dirty.fits
      simp only [List.length_append] at bound
      omega
    · exact same ▸ entry.dirty.fits
  have stable : Settled policy after.image ready.recovered.batches := ⟨valid, settled⟩
  have closed := stable.recoverable bounds fits
  have againFact := Recoverable.nativeOpen dir second _ release.2.1 (release.2.2.1.symm ▸ closed)
  rw [reopened] at againFact
  have allowed := againFact.2.2.2.2.1
  exact ⟨permitted, by simpa [WalRecoverySlice.Contract.Permitted] using allowed⟩

/-- Ordinary errors close the original poisoned phase on the reached image.
A process exit or power loss instead drops the lock on termination, using
the standard restart image. The subsequent open consumes the same invariant. -/
theorem nativeRetryAfterAppend (dir : System.FilePath) (cleanup first second : SingleFile.OpenReports)
    (result : SingleFile.AppendResult)
    (outcome : SingleFile.AppendGuarantee policy known batch result)
    (stop : Option Persistence.Restart)
    (namespaceState : SingleFile.OpenImage)
    (opened : SingleFile.openExistingModel dir policy first
      (match stop with
      | none => SingleFile.postState (SingleFile.closeModel policy cleanup
          (SingleFile.appendReached result).phase
          {namespaceState with image := (SingleFile.appendReached result).image, held := true})
      | some mode => {namespaceState with
          image := mode.image (SingleFile.appendReached result).image
          held := false}) = .ok (.ok ready) after)
    (reopened : SingleFile.openExistingModel dir policy second
      (SingleFile.postState (SingleFile.closeModel policy cleanup (SingleFile.storedPhase ready) after)) =
      .ok (.ok again) final) :
    WalRecoverySlice.Contract.Permitted known (some batch) ready.recovered.batches ∧
      again.recovered.batches = ready.recovered.batches := by
  have entry : Recoverable policy known (some batch) (SingleFile.appendReached result).image :=
    ⟨outcome.1, outcome.2.1⟩
  cases stop with
  | none =>
    have closeSame (state : SingleFile.OpenImage) :
        SingleFile.closeModel policy cleanup (SingleFile.appendReached result).phase state =
          SingleFile.closeModel policy cleanup (.poisoned .lock) state := by
      have phase := outcome.2.2
      cases result with
      | error => simp only [SingleFile.appendReached, phase.2]
      | ok response _ =>
        cases response with
        | error => simp only [SingleFile.appendReached, phase.2]
        | ok ack =>
          cases ack
          simp only [SingleFile.appendReached, phase.2.1]
          rfl
    simp only [closeSame] at opened
    have released := SingleFile.close_poisoned policy cleanup
      {namespaceState with image := (SingleFile.appendReached result).image, held := true}
    have retry : Recoverable policy known (some batch)
        (SingleFile.postState (SingleFile.closeModel policy cleanup (.poisoned .lock)
          {namespaceState with image := (SingleFile.appendReached result).image, held := true})).image := by
      rw [released.2.2]
      exact entry
    exact retry.nativeReopenTwice dir first cleanup second _ released.2.1 opened reopened
  | some mode =>
    cases mode with
    | processExit => exact Recoverable.nativeReopenTwice dir first cleanup second _ rfl entry opened reopened
    | powerLoss => exact Recoverable.nativeReopenTwice dir first cleanup second _ rfl entry.powerLoss opened reopened

/-- A rejected append leaves no physical pending batch, even when the caller
conservatively treats an error as uncertain. -/
theorem Installed.nativeRetryAfterRejected (entry : Installed policy image cursor known)
    (bounded : ∀ b ∈ known, b.length ≤ 32) (fits : known.length ≤ 255)
    (dir : System.FilePath) (cleanup first second : SingleFile.OpenReports)
    (reports : ∀ cursor, SingleFile.AppendReports policy cursor batch)
    (invalid : batch.length > 32 ∨ known.length ≥ 255) (namespaceState : SingleFile.OpenImage)
    (opened : SingleFile.openExistingModel dir policy first
      (let issued := SingleFile.appendReached (SingleFile.appendModel reports
        ⟨image, .active .lock (SingleFile.appendBindings policy) cursor known⟩)
       SingleFile.postState (SingleFile.closeModel policy cleanup issued.phase
        {namespaceState with image := issued.image, held := true})) = .ok (.ok ready) after)
    (reopened : SingleFile.openExistingModel dir policy second
      (SingleFile.postState (SingleFile.closeModel policy cleanup (SingleFile.storedPhase ready) after)) =
      .ok (.ok again) final) :
    ready.recovered.batches = known ∧ again.recovered.batches = known := by
  rw [entry.position, SingleFile.append_rejected reports invalid] at opened
  have released := SingleFile.close_poisoned policy cleanup {namespaceState with image, held := true}
  have original := entry.toSettled.recoverable bounded fits
  have retry : Recoverable policy known none
      (SingleFile.postState (SingleFile.closeModel policy cleanup (.poisoned .lock)
        {namespaceState with image, held := true})).image := by
    rw [released.2.2]
    exact original
  obtain ⟨unchanged, same⟩ := retry.nativeReopenTwice dir first cleanup second _ released.2.1 opened reopened
  have old : ready.recovered.batches = known := by simpa [WalRecoverySlice.Contract.Permitted] using unchanged
  exact ⟨old, same.trans old⟩

end Child

private theorem selectedUnchanged {image : Image}
    (clean : image.powerLoss = image) (marker : Option Marker) :
    image.selectedSync marker = image := by
  rw [← clean]
  cases marker with
  | none => rfl
  | some selected =>
    let slot := selected.lastSeq % 2
    let bytes := (image.powerLoss.marker slot).live
    change image.powerLoss.withMarker slot ⟨bytes, bytes⟩ = image.powerLoss
    by_cases zero : slot = 0 <;>
      simp [bytes, Image.withMarker, Image.marker, Image.powerLoss, FileImage.powerLoss, zero]

/-- The bounded single-file reader leaves a settled segment unchanged at
every reached cut, even if a primitive returns an error after its effect.
A successful return is the exact canonical segment history. -/
theorem reopensSettledSegment {policy : Policy} {image : Image} {history : List Bytes}
    (ready : Ready policy image history) (clean : image.powerLoss = image)
    (bounded : ∀ batch ∈ history, batch.length ≤ 32) (fits : history.length ≤ 255) (effects : Effects) :
    let result := (reopen (ops effects) policy).run image
    reached result = image ∧
      (∀ returned, acknowledged result = some returned → returned = ⟨history, historyCursor history⟩) := by
  have healthy := (ready_powerLoss_reopen ready bounded fits).1
  rw [clean] at healthy
  obtain ⟨marker, selected, repaired⟩ := healthy_reopen_selection healthy
  obtain ⟨cuts, returned⟩ := reopen_cuts effects selected
  have first := selectedUnchanged clean marker
  have both := both_boot image marker
  rw [clean] at both
  have exactEnd : image.data.live.take (historyCursor history).endPos = image.data.live := by
    rw [ready.1.1]
    exact List.take_length
  have trimmed : image.trimmed ⟨history, historyCursor history⟩ = image := by
    simp [Image.trimmed, exactEnd]
  have dataSettled : image.dataSettled = image := by
    simpa only [both, trimmed] using repaired.symm
  refine ⟨?_, fun d got => (returned d got).1⟩
  simpa only [first, both, trimmed, dataSettled, or_self] using cuts

/-- Writebacks change only durable bytes. Every successful scheduling of the
same reopen therefore returns the result selected from the initial live bytes. -/
theorem scheduledReopen_selected {policy image marker decoded} (sel : ReopenSelection policy image marker decoded)
    (effects : Effects) (schedule : WritebackSchedule) :
    ∀ ret, acknowledged ((reopen (scheduledOps (ops effects) schedule) policy).run image) = some ret →
      ret = decoded := by
  obtain ⟨first, last, h⟩ := reopen_writeback_normalizes effects schedule policy image
  have same : ReopenSelection policy (settleFiles first image) marker decoded := by
    apply writebacks_keep (P := fun i => ReopenSelection policy i marker decoded) _ first sel
    intro i file prior
    cases policy <;> cases marker <;> cases file <;> exact prior
  rw [h, (writeback_result ..).2]
  exact fun ret ok => ((reopen_cuts effects same).2 ret ok).1

/-- The batch sequence identified by the live bytes of one child. -/
def Child.Selects (policy : Policy) (image : Image) (batches : List Bytes) : Prop :=
  ∃ marker decoded, ReopenSelection policy image marker decoded ∧ decoded.batches = batches

/-- Reopen selects the same batches from this child's live bytes for every
successful fault/writeback schedule. A healthy execution supplies the witness. -/
theorem Child.Recoverable.selectedBatches {policy history pending image} (r : Child.Recoverable policy history pending image) :
    ∃ batches, WalRecoverySlice.Contract.Permitted history pending batches ∧ (∀ b ∈ batches, b.length ≤ 32) ∧
      Child.Selects policy image batches := by
  obtain ⟨d, after, good⟩ := r.dirty.healthy_reopen
  have ack : acknowledged ((reopen (ops healthyReopen) policy).run image) = some d := by rw [good]; rfl
  obtain ⟨choice, _, _, bounded, _⟩ := (r.dirty.reopen healthyReopen).2.2 d ack
  obtain ⟨marker, sel, _⟩ := healthy_reopen_selection good
  exact ⟨_, choice, bounded, marker, d, sel, rfl⟩

theorem reopensSettledSegmentScheduled {policy image history}
    (ready : Ready policy image history) (clean : image.powerLoss = image)
    (bounded : ∀ b ∈ history, b.length ≤ 32) (fits : history.length ≤ 255)
    (effects : Effects) (schedule : WritebackSchedule) :
    let result := (reopen (scheduledOps (ops effects) schedule) policy).run image
    reached result = image ∧
      ∀ returned, acknowledged result = some returned → returned = ⟨history, historyCursor history⟩ := by
  dsimp only
  obtain ⟨first, last, h⟩ := reopen_writeback_normalizes effects schedule policy image
  rw [settleFiles_clean first image clean] at h
  obtain ⟨stable, response⟩ := reopensSettledSegment ready clean bounded fits effects
  rw [h, (writeback_result ..).1, (writeback_result ..).2, stable, settleFiles_clean last image clean]
  exact ⟨rfl, response⟩

abbrev reopensDirtySegmentScheduled := @Persistence.Dirty.reopenScheduled

end WalRecoverySlice.Segmented
