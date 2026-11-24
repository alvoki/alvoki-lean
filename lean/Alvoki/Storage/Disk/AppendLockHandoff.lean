import Alvoki.Storage.Disk.CheckpointLockHandoff
import Alvoki.Storage.Disk.WalSegmentCommitEffects

namespace Alvoki.Storage.DiskSession

open System WAL.Boundary WalSegmentCommit

/-- Interpret the same publication tail as `DiskTable.writeWithOutcome`
after its preparation and active-file guards have passed. -/
def runPreparedWrite {image : Type} (next : Installed) (sequence : UInt64)
    (commit : EStateM IO.Error image Unit) :
    EStateM DiskWriteError (Phase Installed × LockedFileState image) UInt64 :=
  publishPreparedWrite next sequence (fun phase => modify fun state => (phase, state.2))
    fun state => match commit state.2.image with
      | .ok _ after => .ok () (state.1, { state.2 with image := after })
      | .error cause after => .error (.commitUnknown cause) (state.1, { state.2 with image := after })

theorem runPreparedWrite_success {image : Type} {before : LockedFileState image} {after : image}
    (previous next : Installed) (sequence : UInt64) {commit : EStateM IO.Error image Unit}
    (committed : commit before.image = .ok () after) :
    runPreparedWrite next sequence commit (.ready previous, before) =
      .ok sequence (.ready next, { before with image := after }) := by
  simp only [runPreparedWrite, publishPreparedWrite, publishPrepared, Bind.bind, EStateM.bind,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, committed, Pure.pure, EStateM.pure]

theorem runPreparedWrite_failure_handoff {image : Type} {directory : DiskDirectory}
    {descriptor : Nat} {before : LockedFileState image} {after : image} {cause : IO.Error}
    (previous next : Installed) (sequence : UInt64) {commit : EStateM IO.Error image Unit}
    (failed : commit before.image = .error cause after) (ownership : before.owners.Owns directory descriptor) :
    let poisoned : Phase Installed × LockedFileState image := (.poisoned, ⟨after, before.owners⟩)
    let released : LockedFileState image := ⟨after, before.owners.set (directory.file .lock) none⟩
    runPreparedWrite next sequence commit (.ready previous, before) = .error (.commitUnknown cause) poisoned ∧
      runCloseWithFiles directory descriptor .success poisoned = .ok () (.closed, released) ∧
      (∀ (references : HeldLockReferences descriptor) (drops : List LockReferenceDrop),
        references.remaining drops = [] → references.afterFileDrops drops directory poisoned.2 = released) ∧
      TryLockObserves released.owners directory (.ok true) := by
  dsimp only
  refine ⟨?_, runCloseWithFiles_handoff (by simp) ownership⟩
  · simp only [runPreparedWrite, publishPreparedWrite, publishPrepared, Bind.bind, EStateM.bind,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, failed]

/-- The actual callbacks on the reached append and marker steps, with the
original IO error retained by the writer and erased for cut accounting. -/
structure AppendCommitReports (directory : DiskDirectory) (first : Nat) (before : List WAL.Write)
    (event : WAL.Write) (newBytes : Nat) (effects : WriteEffects) (scratch : Option (ByteArray × Bool))
    (append write : FilePath → ByteArray → EStateM IO.Error WriteFiles Unit)
    (sync : Array FilePath → EStateM IO.Error WriteFiles Unit)
    (rename : FilePath → FilePath → EStateM IO.Error WriteFiles Unit) : Prop where
  appendFrame : forgetError (append (directory.file (.walSegment first)) (WAL.encodeFrame event))
      (WriteFiles.initial before scratch) = effects.appendFrame event (WriteFiles.initial before scratch)
  marker : ∀ appended, effects.appendFrame event (WriteFiles.initial before scratch) = .ok () appended →
    ∀ prior action remaining state, Publication.steps = prior ++ action :: remaining →
    (prior.forM (effects.markerStep (WAL.Boundary.encode newBytes.toUInt64))) appended = .ok () state →
    forgetError (performMarkerAt directory first newBytes write sync rename action) state =
      effects.markerStep (WAL.Boundary.encode newBytes.toUInt64) action state

theorem AppendCommitReports.run {directory first before event newBytes effects scratch append write sync rename}
    (reports : AppendCommitReports directory first before event newBytes effects scratch append write sync rename)
    (count : newBytes = (WAL.encode (before ++ [event])).size) :
    forgetError (commitAt directory first event newBytes append write sync rename) (WriteFiles.initial before scratch) =
      runWriteEffects before event effects scratch := by
  rw [forgetError_commitAt]
  apply commitAt_reports directory first before event newBytes count effects scratch _ _ _ _ reports.appendFrame
  intro appended added prior action remaining state schedule reached
  have agree := reports.marker appended added prior action remaining state schedule reached
  cases action <;> exact agree

end Alvoki.Storage.DiskSession
