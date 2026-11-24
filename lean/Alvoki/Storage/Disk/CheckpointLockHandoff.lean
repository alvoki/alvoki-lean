import Alvoki.Storage.Disk.LockDescriptionLifetime

namespace Alvoki.Storage.DiskSession

/-- Interpret the tail of `DiskTable.checkpoint_fileEffects` after the
ready guard and checkpoint preparation have succeeded. The shared
publication schedule runs while the writer is poisoned. Its file
callbacks leave lock ownership to the session scheduler. -/
def runPreparedCheckpoint {image : Type} (prepared : Installed)
    (perform : CheckpointPublication.Step → EStateM IO.Error image Unit) :
    EStateM IO.Error (Phase Installed × LockedFileState image) Unit := do
  modify fun before => (.poisoned, before.2)
  fun before => match CheckpointPublication.run prepared.table.runs.length perform before.2.image with
    | .ok _ after => .ok () (.ready prepared, { before.2 with image := after })
    | .error cause after => .error cause (before.1, { before.2 with image := after })

/-- The shared close procedure changes the phase and lock ownership.
It carries the file image unchanged in either result. -/
def runCloseWithFiles {α image : Type} (directory : DiskDirectory) (descriptor : Nat)
    (unlock : UnlockReport) : EStateM IO.Error (Phase α × LockedFileState image) Unit :=
  fun (phase, files) => match runClose directory descriptor unlock ⟨phase, files.owners⟩ with
    | .ok _ after => .ok () (after.phase, { files with owners := after.owners })
    | .error cause after => .error cause (after.phase, { files with owners := after.owners })

theorem runCloseWithFiles_poisoned {α image : Type} {directory : DiskDirectory}
    {descriptor : Nat} {before : LockedFileState image}
    (ownership : before.owners.Owns directory descriptor) {unlock : UnlockReport}
    (localUnlock : unlock.LocalFlock) :
    runCloseWithFiles directory descriptor unlock ((.poisoned : Phase α), before) =
      match unlock with
      | .success => .ok () (.closed, ⟨before.image, before.owners.set (directory.file .lock) none⟩)
      | .failure cause _ => .error cause (.poisoned, before) := by
  dsimp only [runCloseWithFiles]
  rw [runClose_open (by simp) unlock, LockOwners.release_owned ownership]
  cases unlock with
  | success => rfl
  | failure cause released =>
    change released = false at localUnlock
    subst released
    rfl

/-- An error from the admitted publication tail leaves its exact file
effects under the original lock. Successful explicit close and an
observed final reference drop both leave those files available for a
reported successful acquisition by the next cooperating open. -/
theorem runPreparedCheckpoint_failure_handoff {image : Type} {directory : DiskDirectory}
    {descriptor : Nat} {before : LockedFileState image} {checkpointImage : image}
    {cause : IO.Error} (previous prepared : Installed)
    (perform : CheckpointPublication.Step → EStateM IO.Error image Unit)
    (publication : CheckpointPublication.run prepared.table.runs.length perform before.image =
      .error cause checkpointImage)
    (ownership : before.owners.Owns directory descriptor) :
    let poisoned : Phase Installed × LockedFileState image := (.poisoned, ⟨checkpointImage, before.owners⟩)
    let released : LockedFileState image := ⟨checkpointImage, before.owners.set (directory.file .lock) none⟩
    runPreparedCheckpoint prepared perform (.ready previous, before) = .error cause poisoned ∧
      runCloseWithFiles directory descriptor .success poisoned = .ok () (.closed, released) ∧
      (∀ (references : HeldLockReferences descriptor) (drops : List LockReferenceDrop),
        references.remaining drops = [] → references.afterFileDrops drops directory poisoned.2 = released) ∧
      TryLockObserves released.owners directory (.ok true) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (match CheckpointPublication.run prepared.table.runs.length perform before.image with
      | .ok _ after => EStateM.Result.ok () (Phase.ready prepared, LockedFileState.mk after before.owners)
      | .error cause after => EStateM.Result.error cause
          ((.poisoned : Phase Installed), LockedFileState.mk after before.owners)) = _
    rw [publication]
  · exact runCloseWithFiles_poisoned (before := ⟨checkpointImage, before.owners⟩)
      (unlock := .success) ownership trivial
  · intro references drops last
    exact references.afterFileDrops_released ownership last
  · simp [TryLockObserves, LockOwners.set]

end Alvoki.Storage.DiskSession
