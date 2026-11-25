import Alvoki.Storage.Disk.LockDescriptionLifetime

namespace Alvoki.Storage.DiskSession

/-- Interpret the prepared checkpoint's publication operations under
the poisoned phase. An observed prefix uses `.poisoned` as its boundary
phase. The full schedule installs the prepared writer on success. -/
def runCheckpointActions {image : Type} (actions : EStateM IO.Error image Unit) (onSuccess : Phase Installed) :
    EStateM IO.Error (Phase Installed × LockedFileState image) Unit := do
  modify fun before => (.poisoned, before.2)
  fun before => match actions before.2.image with
    | .ok _ after => .ok () (onSuccess, { before.2 with image := after })
    | .error cause after => .error cause (before.1, { before.2 with image := after })

/-- Interpret the tail of `DiskTable.checkpoint_fileEffects` after
preparation, with the ready update after all publication operations. -/
def runPreparedCheckpoint {image : Type} (prepared : Installed)
    (perform : CheckpointPublication.Step → EStateM IO.Error image Unit) :
    EStateM IO.Error (Phase Installed × LockedFileState image) Unit :=
  runCheckpointActions (CheckpointPublication.run prepared.table.runs.length perform) (.ready prepared)

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
  refine ⟨?_, runCloseWithFiles_handoff (by simp) ownership⟩
  · change (match CheckpointPublication.run prepared.table.runs.length perform before.image with
      | .ok _ after => EStateM.Result.ok () (Phase.ready prepared, LockedFileState.mk after before.owners)
      | .error cause after => EStateM.Result.error cause
          ((.poisoned : Phase Installed), LockedFileState.mk after before.owners)) = _
    rw [publication]

end Alvoki.Storage.DiskSession
