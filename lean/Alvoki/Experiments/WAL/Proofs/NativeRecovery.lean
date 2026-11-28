import Alvoki.Experiments.WAL.SingleFile
import Alvoki.Experiments.WAL.Proofs.DirtyRetry
import Alvoki.Experiments.WAL.Proofs.ReopenWriteback

namespace WalRecoverySlice.Persistence

theorem writebacks_keep {P : Image → Prop}
    (step : ∀ image file, P image → P (WalFile.settle file image)) (files : List WalFile)
    {before : Image} (entry : P before) : P (settleFiles files before) := by
  induction files generalizing before with
  | nil => exact entry
  | cons file rest ih => exact ih (step before file entry)

theorem writeback_result (files : List WalFile) (r : Persistence.Result α) :
    reached (r.writeback files) = settleFiles files (reached r) ∧
    acknowledged (r.writeback files) = acknowledged r := by
  cases r with
  | error => exact ⟨rfl, rfl⟩
  | ok val _ => cases val <;> exact ⟨rfl, rfl⟩

theorem Dirty.reopenScheduled {policy known pending image}
    (dirty : Dirty policy known pending image) (effects : Effects) (schedule : WritebackSchedule) :
    let result := (WalRecoverySlice.reopen (scheduledOps (ops effects) schedule) policy).run image
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

end WalRecoverySlice.Persistence

namespace WalRecoverySlice.SingleFile

open Persistence

/-- Roles of descriptions acquired for one recovery under the exclusive lock. -/
private inductive RecoveryHandle where
  | data
  | marker (slot : Nat)

private def recoveryEffects (effects : Effects) : RecoveryIO M RecoveryHandle where
  readData
    | .data => (ops effects).readData
    | .marker _ => throw "not a data descriptor"
  readMarker
    | .marker slot => (ops effects).readMarker slot
    | .data => throw "not a marker descriptor"
  truncateAt
    | .data => (ops effects).truncate
    | .marker _ => fun _ => throw "not a data descriptor"
  sync
    | .data => (ops effects).syncData
    | .marker slot => (ops effects).syncMarker slot

/-- Interpret the adapter at the descriptions reached by native acquisition. -/
def recoverScheduled (effects : Effects) (schedule : WritebackSchedule) (policy : Policy) : M Decoded :=
  let markers := if policy == .boundary then some (RecoveryHandle.marker 0, RecoveryHandle.marker 1)
    else none
  reopen (scheduledOps (recoveryOps (recoveryEffects effects) .data markers) schedule) policy

def recover (effects : Effects) (policy : Policy) : M Decoded :=
  recoverScheduled effects {} policy

private theorem marker_sync (effects : Effects) (slot : Nat) (bound : slot < 2) :
    (recoveryOps (recoveryEffects effects) .data
      (some (RecoveryHandle.marker 0, RecoveryHandle.marker 1))).syncMarker slot =
        (ops effects).syncMarker slot := by
  have slots : slot = 0 ∨ slot = 1 := by omega
  rcases slots with rfl | rfl <;> rfl

theorem recoverScheduled_eq (effects : Effects) (schedule : WritebackSchedule) (policy : Policy) :
    recoverScheduled effects schedule policy = reopen (scheduledOps (ops effects) schedule) policy := by
  cases policy with
  | logOnly => rfl
  | boundary =>
    let files := recoveryOps (recoveryEffects effects) .data
      (some (RecoveryHandle.marker 0, RecoveryHandle.marker 1))
    change reopen (scheduledOps files schedule) .boundary = reopen (scheduledOps (ops effects) schedule) .boundary
    have sync (slot : Nat) (bound : slot < 2) :
        files.syncMarker slot = (ops effects).syncMarker slot := marker_sync effects slot bound
    have syncSelected (marker : Marker) :
        files.syncMarker (marker.lastSeq % 2) = (ops effects).syncMarker (marker.lastSeq % 2) :=
      sync _ (by omega)
    have syncOther (marker : Marker) :
        files.syncMarker (1 - marker.lastSeq % 2) =
          (ops effects).syncMarker (1 - marker.lastSeq % 2) :=
      sync _ (by omega)
    have r0 : files.readMarker 0 = (ops effects).readMarker 0 := rfl
    have r1 : files.readMarker 1 = (ops effects).readMarker 1 := rfl
    have data : files.readData = (ops effects).readData := rfl
    have trim : files.truncate = (ops effects).truncate := rfl
    have syncData : files.syncData = (ops effects).syncData := rfl
    simp only [reopen, scheduledOps, r0, r1, data, trim, syncData, syncSelected, syncOther]

theorem recover_eq (effects : Effects) (policy : Policy) :
    recover effects policy = reopen (ops effects) policy := by
  rw [recover, recoverScheduled_eq]
  rfl

/-- The adapter's primitive interpretation preserves admission on failure and
establishes the selected physical entry and canonical cursor on success. -/
theorem recover_refines (effects : Effects) (dirty : Dirty policy known pending image) :
    let result := (recover effects policy).run image
    Dirty policy known pending (reached result) ∧
    (image.MarkersSettled → (reached result).MarkersSettled) ∧
    ∀ decoded, acknowledged result = some decoded →
      Contract.Permitted known pending decoded.batches ∧
      decoded.cursor = historyCursor decoded.batches ∧
      Ready policy (reached result) decoded.batches ∧
      (∀ b ∈ decoded.batches, b.length ≤ 32) ∧ decoded.batches.length ≤ 255 ∧
      (policy = .boundary ∨ image.MarkersSettled → (reached result).powerLoss = reached result) := by
  rw [recover_eq]
  exact dirty.reopen effects

end WalRecoverySlice.SingleFile
