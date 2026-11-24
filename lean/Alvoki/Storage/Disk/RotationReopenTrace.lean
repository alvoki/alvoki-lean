import Alvoki.Storage.Disk.RotationSessionHandoff
import Alvoki.Storage.Disk.SegmentedRetryTrace

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WalSegmentRotation

/-- The aligned plan follows the currently visible keeper, including an
empty successor whose name might still disappear. The first directory
barrier and the keeper sync have separate reports. -/
def BoundedReopenAttempt.RotationReports (attempt : BoundedReopenAttempt WalSegmentRotation.State)
    (directory : DiskDirectory) (image : WalSegmentImage) (state : WalSegmentRotation.State)
    (range : MarkedWalRange) : Prop :=
  attempt.acquired = .ok true →
    match attempt.prepare directory with
    | .error _ => True
    | .ok (plan, _, size) =>
      let active := (state.visible image).active
      plan = ⟨range.through, active.first, [], active.bytes⟩ ∧ size = active.bytes.size ∧
      (match attempt.sync #[directory.path] state with
        | .ok _ after => after = state.settleForReopen
        | .error _ after => after = state ∨ after = state.settleForReopen) ∧
      (match attempt.sync #[directory.file (.walSegment active.first)] state.settleForReopen with
        | .ok _ after | .error _ after => after = state.settleForReopen)

/-- An actual bounded read or sync failure carries its reported state
through lock cleanup. An effective directory barrier fixes the currently
observed successor even when recovery returns an error. -/
theorem BoundedReopenAttempt.rotationErrorFiles (attempt : BoundedReopenAttempt WalSegmentRotation.State)
    {directory : DiskDirectory} {before after : LockedFileState WalSegmentRotation.State} {cause : IO.Error}
    {image : WalSegmentImage} {history : List WAL.Write}
    (layout : (before.image.visible image).ReadLayout history) {range : MarkedWalRange}
    (decoded : before.image.metadata.active.walRange = some range) (atEnd : range.through = history.length)
    (reports : attempt.RotationReports directory image before.image range)
    (ran : attempt.run directory before = .error cause after) :
    after.image = before.image ∨ after.image = before.image.settleForReopen := by
  by_cases took : attempt.acquired = .ok true
  · have safe : match attempt.recover directory before.image with
        | .ok _ _ => True
        | .error _ final => final = before.image ∨ final = before.image.settleForReopen := by
      unfold BoundedReopenAttempt.recover reopenMarkedBoundedWith
      rw [prepareBoundedMarkedWith_liftReports]
      cases reading : attempt.prepare directory with
      | error error =>
        have rejected : prepareBoundedMarkedWith directory attempt.readOptional attempt.list attempt.lstat
          attempt.readBin attempt.readPrefix = .error error := reading
        rw [rejected]
        exact .inl rfl
      | ok result =>
        obtain ⟨plan, opened, physicalSize⟩ := result
        have accepted : prepareBoundedMarkedWith directory attempt.readOptional attempt.list attempt.lstat
          attempt.readBin attempt.readPrefix = .ok (plan, opened, physicalSize) := reading
        rw [accepted]
        have observed := reports took
        rw [reading] at observed
        obtain ⟨rfl, rfl, metadata, keeper⟩ := observed
        simp only [liftExcept, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
        obtain ⟨_, prepared, _, safeFinish⟩ := WalSegmentRotation.State.finishAfterRotation layout decoded atEnd directory
          attempt.removeFile attempt.write attempt.sync attempt.renameFile metadata keeper
        let active := (before.image.visible image).active
        let full : Plan := ⟨range.through, active.first, [], active.bytes⟩
        have size : full.keeperSize = active.bytes.size := by
          change (range.through - active.first) * WAL.frameSize = active.bytes.size
          rw [layout.activeBytes, WAL.encode_size, atEnd, List.length_drop, Nat.mul_comm]
        have kept : full.keeperBytes.extract 0 full.keeperSize = full.keeperBytes := by
          rw [size, ← show full.keeperBytes.size = active.bytes.size from rfl, ByteArray.extract_zero_size]
        have transport := finishBoundedMarkedOpen_eq_full directory full prepared.valid attempt.removeFile
          attempt.write attempt.sync attempt.renameFile
        rw [kept] at transport
        have applied : finishBoundedMarkedOpen directory
            ⟨range.through, (before.image.visible image).active.first, [], (before.image.visible image).active.bytes⟩
            (before.image.visible image).active.bytes.size attempt.removeFile attempt.write attempt.sync attempt.renameFile
            before.image = finishMarkedOpen directory full attempt.removeFile attempt.write attempt.sync attempt.renameFile
            before.image := congrArg (fun (step : EStateM IO.Error WalSegmentRotation.State Unit) => step before.image) transport
        rw [applied]
        change (match finishMarkedOpen directory full attempt.removeFile attempt.write attempt.sync attempt.renameFile
          before.image with
          | .ok _ final => final = before.image.settleForReopen ∧ _
          | .error _ final => final = before.image ∨ final = before.image.settleForReopen) at safeFinish
        cases finish : finishMarkedOpen directory full attempt.removeFile attempt.write attempt.sync attempt.renameFile
            before.image with
        | ok _ _ => trivial
        | error _ _ => simpa only [finish] using safeFinish
    rw [BoundedReopenAttempt.run, runOpenWithInstallation_outcome, took, runOpenWithImage_acquired] at ran
    cases worker : attempt.recover directory before.image with
    | ok _ _ => rw [worker] at ran; contradiction
    | error _ final =>
      rw [worker] at ran safe
      cases cleanup : attempt.unlock <;> simp only [cleanup] at ran <;>
        obtain ⟨_, same⟩ := EStateM.Result.error.inj ran <;>
        exact (congrArg (fun state => state.image) same) ▸ safe
  · obtain ⟨_, denied⟩ := runOpenWithImage_notAcquired directory attempt.descriptor attempt.acquired
      attempt.unlock (attempt.recover directory) before took
    rw [BoundedReopenAttempt.run, runOpenWithInstallation_outcome, denied] at ran
    exact Or.inl (congrArg LockedFileState.image (EStateM.Result.error.inj ran).2.symm)

/-- Repeated failed aligned opens retain the rotation state until the
name has settled. Power loss chooses the successor's presence here, before
projecting to a fixed keeper. Power loss clears the local owner. Process
death uses observed reference drops. -/
inductive RotationReopenFailures (directory : DiskDirectory) (image : WalSegmentImage) (history : List WAL.Write)
    (initial : LockedFileState WalSegmentRotation.State) : LockedFileState WalSegmentRotation.State → Prop where
  | empty : RotationReopenFailures directory image history initial initial
  | failed {before after cause range} (prior : RotationReopenFailures directory image history initial before)
      (attempt : BoundedReopenAttempt WalSegmentRotation.State)
      (acquisition : TryLockObserves before.owners directory attempt.acquired) (unlock : attempt.unlock.LocalFlock)
      (decoded : before.image.metadata.active.walRange = some range) (atEnd : range.through = history.length)
      (reports : attempt.RotationReports directory image before.image range)
      (ran : attempt.run directory before = .error cause after) :
      RotationReopenFailures directory image history initial after
  | referenceDrops {before description} (prior : RotationReopenFailures directory image history initial before)
      (references : HeldLockReferences description) (drops : List LockReferenceDrop) :
      RotationReopenFailures directory image history initial (references.afterFileDrops drops directory before)
  | powerLoss {before pair present} (prior : RotationReopenFailures directory image history initial before)
      (selected : pair ∈ before.image.metadata.crashImages) (survives : before.image.successor.MaySurvive present) :
      RotationReopenFailures directory image history initial
        ⟨⟨.settled pair, if present then .durable else .absent⟩, before.owners.set (directory.file .lock) none⟩

theorem RotationReopenFailures.rotationTrace {directory : DiskDirectory} {image : WalSegmentImage}
    {history : List WAL.Write} {initial after : LockedFileState WalSegmentRotation.State}
    (failures : RotationReopenFailures directory image history initial after)
    (rotation : CanRotate image history) (layout : image.ReadLayout history) (origin : Trace image initial.image) :
    Trace image after.image := by
  induction failures with
  | empty => exact origin
  | failed _ attempt _ _ decoded atEnd reports ran prior =>
    rcases attempt.rotationErrorFiles (WalSegmentRotation.State.visibleReadLayout _ rotation layout)
        decoded atEnd reports ran with unchanged | settled
    · exact unchanged.symm ▸ prior
    · exact settled.symm ▸ .reopenBarrier prior
  | referenceDrops _ _ _ prior => exact prior
  | powerLoss _ selected survives prior => exact .crash prior _ selected survives

end Alvoki.Storage.DiskSession
