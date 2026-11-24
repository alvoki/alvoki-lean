import Alvoki.Storage.Disk.LockedMarkedRead
import Alvoki.Storage.Disk.LockedVersionedCheckpointRead
import Alvoki.Storage.Disk.MarkedOpenControl

namespace Alvoki.Storage.DiskSession
open WAL.Boundary

structure LockedReopenState where
  image : ReopenImage
  owners : LockOwners

/-- Retain the recovery report's exact file image whenever the lock was
acquired. The outer lock schedule still decides the returned error and
ownership, including when an unlock error masks the recovery error. -/
def runLockedMarkedOpenRetainingImage (directory : DiskDirectory) (descriptor : Nat)
    (acquired : Except IO.Error Bool) (unlock : UnlockReport) (cause : String → IO.Error)
    (recovery : EStateM.Result String ReopenImage (PackedTable × UInt64 × Nat)) :
    EStateM IO.Error LockedReopenState ((PackedTable × UInt64 × Nat) × ReopenImage) := fun before =>
  let image := match acquired with
    | .ok true => match recovery with
      | .ok _ after | .error _ after => after
    | _ => before.image
  match runLockedMarkedOpen directory descriptor acquired unlock cause recovery before.owners with
  | .ok installed owners => .ok installed ⟨image, owners⟩
  | .error error owners => .error error ⟨image, owners⟩

theorem runLockedMarkedOpenRetainingImage_project (directory : DiskDirectory) (descriptor : Nat)
    (acquired : Except IO.Error Bool) (unlock : UnlockReport) (cause : String → IO.Error)
    (recovery : EStateM.Result String ReopenImage (PackedTable × UInt64 × Nat)) (before : LockedReopenState) :
    (match runLockedMarkedOpenRetainingImage directory descriptor acquired unlock cause recovery before with
    | .ok installed after => .ok installed after.owners
    | .error error after => .error error after.owners) =
      runLockedMarkedOpen directory descriptor acquired unlock cause recovery before.owners := by
  unfold runLockedMarkedOpenRetainingImage
  cases runLockedMarkedOpen directory descriptor acquired unlock cause recovery before.owners <;> rfl

theorem runLockedMarkedOpenRetainingImage_notAcquired (directory : DiskDirectory) (descriptor : Nat)
    (acquired : Except IO.Error Bool) (unlock : UnlockReport) (cause : String → IO.Error)
    (recovery : EStateM.Result String ReopenImage (PackedTable × UInt64 × Nat)) (before : LockedReopenState)
    (denied : acquired ≠ .ok true) :
    ∃ error, runLockedMarkedOpenRetainingImage directory descriptor acquired unlock cause recovery before =
      .error error before := by
  rcases acquired with error | (_ | _)
  · exact ⟨error, rfl⟩
  · exact ⟨_, rfl⟩
  · exact False.elim (denied rfl)

theorem runLockedMarkedOpenRetainingImage_recoveryError (directory : DiskDirectory) (descriptor : Nat)
    (unlock : UnlockReport) (cause : String → IO.Error) (message : String) (after : ReopenImage)
    (before : LockedReopenState) :
    runLockedMarkedOpenRetainingImage directory descriptor (.ok true) unlock cause (.error message after) before =
      match unlock with
      | .success => .error (cause message) ⟨after, before.owners.set (directory.file .lock) none⟩
      | .failure error released =>
        .error error ⟨after, before.owners.set (directory.file .lock) (if released then none else some descriptor)⟩ := by
  unfold runLockedMarkedOpenRetainingImage runLockedMarkedOpen
  rw [runOpen_recoveryError]
  cases unlock <;> rfl

private theorem MarkedReopenAttempts.ofStrictSharedOpenError
    {initial before after : ReopenImage} {durable : CheckpointPublication.RunFiles}
    (attempts : MarkedReopenAttempts initial before) (bound : MarkerBound initial.directory)
    (checkpoint : VersionedCheckpointFileReads durable before.directory.active.manifest)
    (reads : MarkedWalReads before) (repair : Publication.Step → RepairReport) (aligned : AlignedSyncReport)
    {message : String}
    (failed : runSharedMarkedOpen (readIntegrityCheckpoint checkpoint.readManifest checkpoint.readRun id)
      reads.marker reads.wal repair aligned before = .error message after) :
    MarkedReopenAttempts initial after := by
  let loaded := readIntegrityCheckpoint checkpoint.readManifest checkpoint.readRun id
  let observed := MarkedReopenReads.mk reads (loaded.map fun result => (result.getD (.empty, 0)).1)
  obtain ⟨marker, _, visible, _, _⟩ := (attempts.toRetry bound).markerBound bound
  have marked : reads.marker ≠ .ok none := by
    intro absent
    have impossible := (reads.markerVisible _ absent).symm.trans visible
    contradiction
  have shared := runSharedMarkedOpen_eq loaded reads.marker reads.wal marked repair aligned before
  change runSharedMarkedOpen loaded reads.marker reads.wal repair aligned before =
    (match runMarkedReopen observed.preflight repair false aligned before with
    | .error error image => .error error image
    | .ok table image => .ok (table, ((loaded.toOption.getD none).getD (.empty, 0)).2,
      (observed.preflight.toOption.map (·.selected.size)).getD 0) image) at shared
  change runSharedMarkedOpen loaded reads.marker reads.wal repair aligned before = .error message after at failed
  rw [shared] at failed
  cases examined : runMarkedReopen observed.preflight repair false aligned before with
  | ok _ _ => rw [examined] at failed; contradiction
  | error error image =>
    rw [examined] at failed
    have exactImage := (EStateM.Result.error.inj failed).2
    cases exactImage
    exact .failure attempts observed repair aligned examined

/-- A strict locked open error leaves an admitted retry image. Lock denial
keeps the old image, while an acquired attempt contributes its actual
reported read, repair or sync effects even if cleanup also reports failure. -/
theorem runLockedStrictMarkedOpenRetainingImage_retry
    {initial : ReopenImage} {before after : LockedReopenState} {durable : CheckpointPublication.RunFiles}
    (attempts : MarkedReopenAttempts initial before.image) (bound : MarkerBound initial.directory)
    (directory : DiskDirectory) (descriptor : Nat) (acquired : Except IO.Error Bool) (unlock : UnlockReport)
    (cause : String → IO.Error)
    (checkpoint : VersionedCheckpointFileReads durable before.image.directory.active.manifest)
    (reads : MarkedWalReads before.image) (repair : Publication.Step → RepairReport) (aligned : AlignedSyncReport)
    {error : IO.Error}
    (failed : runLockedMarkedOpenRetainingImage directory descriptor acquired unlock cause
      (runSharedMarkedOpen (readIntegrityCheckpoint checkpoint.readManifest checkpoint.readRun id)
        reads.marker reads.wal repair aligned before.image) before = .error error after) :
    MarkedReopenAttempts initial after.image := by
  let reopened := runSharedMarkedOpen (readIntegrityCheckpoint checkpoint.readManifest checkpoint.readRun id)
    reads.marker reads.wal repair aligned before.image
  change runLockedMarkedOpenRetainingImage directory descriptor acquired unlock cause reopened before =
    .error error after at failed
  by_cases acquiredLock : acquired = .ok true
  · subst acquired
    cases observed : reopened with
    | ok installed image =>
      rw [observed] at failed
      contradiction
    | error message image =>
      rw [observed, runLockedMarkedOpenRetainingImage_recoveryError] at failed
      have exactImage : after.image = image := by
        cases unlock <;> cases failed <;> rfl
      rw [exactImage]
      exact MarkedReopenAttempts.ofStrictSharedOpenError attempts bound checkpoint reads repair aligned observed
  · obtain ⟨_, unchanged⟩ :=
      runLockedMarkedOpenRetainingImage_notAcquired directory descriptor acquired unlock cause reopened before acquiredLock
    have same := (EStateM.Result.error.inj (failed.symm.trans unchanged)).2
    rwa [same]

end Alvoki.Storage.DiskSession
