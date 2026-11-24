import Alvoki.Storage.Disk.CheckpointLockHandoff
import Alvoki.Storage.Disk.WalSegmentRotation

namespace Alvoki.Storage.WalSegmentRotation

open System

/-- The successor lookup is read-only. An accepted lookup drives the actual
create and sync callbacks on the absolute segment path. -/
theorem Trace.afterRunAt {initial : WalSegmentImage} {before : State} (trace : Trace initial before)
    (directory : DiskDirectory)
    (read : FilePath → EStateM IO.Error State (Option ByteArray))
    (create sync : FilePath → EStateM IO.Error State Unit)
    (lookup : match read (directory.file (.walSegment initial.active.last)) before with
      | .ok bytes after => bytes = before.observeSuccessor ∧ after = before
      | .error _ after => after = before)
    (reports : EffectReports (performPaths directory initial.active.last create sync)) :
    match runAt directory initial.active.last read create sync before with
    | .ok _ after | .error _ after => Trace initial after := by
  unfold runAt observeSuccessorWith
  simp only [Bind.bind, EStateM.bind]
  cases report : read (directory.file (.walSegment initial.active.last)) before with
  | error _ after =>
    rw [report] at lookup
    exact lookup.symm ▸ trace
  | ok bytes after =>
    rw [report] at lookup
    obtain ⟨exactBytes, unchanged⟩ := lookup
    subst bytes
    subst after
    have observed := trace.afterObservedReport before.observeSuccessor.isSome
      (performPaths directory initial.active.last create sync) reports
    by_cases absent : before.successor = .absent
    · cases ran : run false (performPaths directory initial.active.last create sync) before <;>
        simpa [State.observeSuccessor, absent, Pure.pure, EStateM.pure, ran] using observed
    · cases ran : run true (performPaths directory initial.active.last create sync) before <;>
        simpa [State.observeSuccessor, absent, Pure.pure, EStateM.pure, ran] using observed

end Alvoki.Storage.WalSegmentRotation

namespace Alvoki.Storage.DiskSession

open System WalSegmentRotation

/-- Interpret the shared publication tail of `rotateWal` after the ready,
nonempty active segment and stable file identity guards. -/
def runPreparedRotation (next : Installed) (rotate : EStateM IO.Error State Unit) :
    EStateM IO.Error (Phase Installed × LockedFileState State) Unit :=
  let setPhase := fun phase => modify fun (state : Phase Installed × LockedFileState State) => (phase, state.2)
  publishPrepared setPhase
    (fun state => match rotate state.2.image with
      | .ok _ after => .ok () (state.1, { state.2 with image := after })
      | .error cause after => .error cause (state.1, { state.2 with image := after }))
    (setPhase (.ready next))

/-- Error reports from the reached native rotation retain the exact name
and directory state. The writer stays poisoned under its original owner.
Successful close or the observed last reference drop hands off that state. -/
theorem runPreparedRotation_failure_handoff {directory : DiskDirectory} {descriptor : Nat}
    {before : LockedFileState State} {after : State} {cause : IO.Error}
    {initial : WalSegmentImage} {history : List WAL.Write} (rotation : CanRotate initial history)
    (trace : Trace initial before.image) (previous : Installed)
    (installedBytes : previous.walBytes = history.length * WAL.frameSize)
    (installedStart : previous.activeFirst = initial.active.first)
    (ownership : before.owners.Owns directory descriptor)
    (read : FilePath → EStateM IO.Error State (Option ByteArray))
    (create sync : FilePath → EStateM IO.Error State Unit)
    (lookup : match read (directory.file (.walSegment initial.active.last)) before.image with
      | .ok bytes after => bytes = before.image.observeSuccessor ∧ after = before.image
      | .error _ after => after = before.image)
    (reports : EffectReports (performPaths directory initial.active.last create sync))
    (failed : runAt directory (previous.walBytes / WAL.frameSize) read create sync before.image = .error cause after) :
    let successor := previous.walBytes / WAL.frameSize
    let poisoned : Phase Installed × LockedFileState State := (.poisoned, ⟨after, before.owners⟩)
    let released : LockedFileState State := ⟨after, before.owners.set (directory.file .lock) none⟩
    successor = initial.active.last ∧ previous.activeFirst < successor ∧ Trace initial after ∧
    runPreparedRotation { previous with activeFirst := successor } (runAt directory successor read create sync)
      (.ready previous, before) = .error cause poisoned ∧
    runCloseWithFiles directory descriptor .success poisoned = .ok () (.closed, released) ∧
    (∀ (references : HeldLockReferences descriptor) (drops : List LockReferenceDrop),
      references.remaining drops = [] → references.afterFileDrops drops directory poisoned.2 = released) := by
  intro successor poisoned released
  have start : successor = initial.active.last := by
    dsimp only [successor]
    rw [installedBytes, Nat.mul_div_cancel _ (by decide : 0 < WAL.frameSize), rotation.atEnd]
  have observed := trace.afterRunAt directory read create sync lookup reports
  change runAt directory successor read create sync before.image = _ at failed
  rw [← start, failed] at observed
  refine ⟨start, installedStart.symm ▸ start.symm ▸ rotation.nonempty, observed, ?_, ?_, ?_⟩
  · simp only [runPreparedRotation, publishPrepared, Bind.bind, EStateM.bind,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, failed, poisoned]
  · exact runCloseWithFiles_poisoned (before := ⟨after, before.owners⟩) (unlock := .success) ownership trivial
  · intro references drops last
    exact references.afterFileDrops_released ownership last

end Alvoki.Storage.DiskSession
