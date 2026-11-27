import Alvoki.Experiments.WAL.SingleFile
import Alvoki.Experiments.WAL.Proofs.DirtyRetry

namespace WalRecoverySlice.SingleFile

open Persistence

/-- Roles of descriptions acquired for one recovery under the exclusive lock. -/
private inductive RecoveryHandle where
  | data
  | marker (slot : Nat)

private def recoveryEffects (effects : Effects) : RecoveryIO M RecoveryHandle where
  readFromStart
    | .data => (ops effects).readData
    | .marker slot => (ops effects).readMarker slot
  truncateAt
    | .data => (ops effects).truncate
    | .marker _ => fun _ => throw "not a data descriptor"
  sync
    | .data => (ops effects).syncData
    | .marker slot => (ops effects).syncMarker slot

/-- Interpret the adapter at the descriptions reached by native acquisition. -/
def recover (effects : Effects) (policy : Policy) : M Decoded :=
  let markers := if policy == .boundary then some (RecoveryHandle.marker 0, RecoveryHandle.marker 1)
    else none
  recoverWith (recoveryEffects effects) .data markers (ops effects) policy

private theorem marker_sync (effects : Effects) (slot : Nat) (bound : slot < 2) :
    (recoveryOps (recoveryEffects effects) .data
      (some (RecoveryHandle.marker 0, RecoveryHandle.marker 1)) (ops effects)).syncMarker slot =
        (ops effects).syncMarker slot := by
  have slots : slot = 0 ∨ slot = 1 := by omega
  rcases slots with rfl | rfl <;> rfl

theorem recover_eq (effects : Effects) (policy : Policy) :
    recover effects policy = reopen (ops effects) policy := by
  cases policy with
  | logOnly => rfl
  | boundary =>
    let files := recoveryOps (recoveryEffects effects) .data
      (some (RecoveryHandle.marker 0, RecoveryHandle.marker 1)) (ops effects)
    change reopen files .boundary = reopen (ops effects) .boundary
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
    simp only [reopen, r0, r1, data, trim, syncData, syncSelected, syncOther]

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
