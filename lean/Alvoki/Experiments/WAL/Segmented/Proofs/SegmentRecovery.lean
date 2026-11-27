import Alvoki.Experiments.WAL.Proofs.DirtyAppend
import Alvoki.Experiments.WAL.Proofs.ReopenWriteback

/-! Recovery of segments already sealed by the directory protocol. -/

namespace WalRecoverySlice.Segmented

open Persistence

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

private theorem writebacks_keep {P : Image → Prop}
    (step : ∀ image file, P image → P (WalFile.settle file image)) (files : List WalFile)
    {before : Image} (entry : P before) : P (settleFiles files before) := by
  induction files generalizing before with
  | nil => exact entry
  | cons file rest ih => exact ih (step before file entry)

private theorem writeback_result (files : List WalFile) (r : Persistence.Result α) :
    reached (r.writeback files) = settleFiles files (reached r) ∧
    acknowledged (r.writeback files) = acknowledged r := by
  cases r with
  | error => exact ⟨rfl, rfl⟩
  | ok val _ => cases val <;> exact ⟨rfl, rfl⟩

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

theorem reopensDirtySegmentScheduled {policy known pending image}
    (dirty : Dirty policy known pending image) (effects : Effects) (schedule : WritebackSchedule) :
    let result := (reopen (scheduledOps (ops effects) schedule) policy).run image
    Dirty policy known pending (reached result) ∧ (image.MarkersSettled → (reached result).MarkersSettled) ∧
      ∀ decoded, acknowledged result = some decoded →
        WalRecoverySlice.Contract.Permitted known pending decoded.batches ∧ decoded.cursor = historyCursor decoded.batches ∧
        Ready policy (reached result) decoded.batches ∧ (∀ b ∈ decoded.batches, b.length ≤ 32) ∧ decoded.batches.length ≤ 255 ∧
        (policy = .boundary ∨ image.MarkersSettled → (reached result).powerLoss = reached result) := by
  dsimp only
  obtain ⟨first, last, h⟩ := reopen_writeback_normalizes effects schedule policy image
  have keepDirty (files : List WalFile) {i : Image} (p : Dirty policy known pending i) :=
    writebacks_keep (P := Dirty policy known pending) (fun i f p => p.writeback (f.writeback i)) files p
  have keepMarkers (files : List WalFile) {i : Image} (p : i.MarkersSettled) :=
    writebacks_keep (P := Image.MarkersSettled) (fun i f p => (f.writeback i).keepsMarkersSettled p) files p
  obtain ⟨retry, markers, success⟩ := (keepDirty first dirty).reopen effects
  rw [h, (writeback_result ..).1, (writeback_result ..).2]
  refine ⟨keepDirty last retry, fun m => keepMarkers last (markers (keepMarkers first m)), ?_⟩
  intro d ok
  obtain ⟨perm, cursor, ready, bounded, fits, clean⟩ := success d ok
  refine ⟨perm, cursor, ?_, bounded, fits, ?_⟩
  · by_cases boundary : policy = .boundary
    · rwa [settleFiles_clean _ _ (clean (.inl boundary))]
    · refine ⟨?_, fun b => (boundary b).elim⟩
      apply writebacks_keep (P := fun i => AtEnd i _ _) _ last ready.1
      intro i f atEnd
      rcases atEnd with ⟨data, endPos⟩
      cases f
      · exact ⟨by simp [WalFile.settle, data], endPos⟩
      · exact ⟨data, endPos⟩
      · exact ⟨data, endPos⟩
  · intro physical
    have same := clean (physical.imp_right (keepMarkers first))
    rwa [settleFiles_clean _ _ same]

end WalRecoverySlice.Segmented
