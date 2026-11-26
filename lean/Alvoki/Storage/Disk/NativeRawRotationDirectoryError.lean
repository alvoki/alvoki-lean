import Alvoki.Storage.Disk.NativeOpenRotation
import Alvoki.Storage.Disk.NativeRawSync

namespace Alvoki.Storage.DiskSession

open System

section FilePrefix

variable {heap : Type} {calls : OpenRotationCallbacks heap} {directory : DiskDirectory}
  {first : Nat} {entry synced : heap}

/-- The reached probe, optional create and file sync leave exactly the
final root callback. Its returned diagnostic is the rotation error. -/
theorem OpenRotationCallbacks.SuccessorFilePrefix.returnsDirectoryError
    (filePrefix : calls.SuccessorFilePrefix directory first entry synced)
    {cause : IO.Error} {reached : heap}
    (failed : calls.sync directory.path synced = .error cause reached) :
    WalSegmentRotation.runAt directory first calls.read calls.create calls.sync entry = .error cause reached := by
  rw [WalSegmentRotation.runAt_fileEffects]
  have selected := filePrefix.successor
  cases observed : filePrefix.observed with
  | none =>
    simp only [observed, Option.elim] at selected
    simp [WalSegmentRotation.observeSuccessorWith, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
      filePrefix.read, observed, selected, filePrefix.sync, failed]
  | some bytes =>
    simp only [observed, Option.elim] at selected
    have fileSynced := selected.2 ▸ filePrefix.sync
    simp only [WalSegmentRotation.observeSuccessorWith, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
      filePrefix.read, observed, selected.1, ↓reduceIte, fileSynced, failed]

end FilePrefix

/-- The literal rotation propagates the failed cached root fsync at its
returned heap. The active-cache clear and final ready setter lie beyond
this failure. Scope facts use only the callbacks that reached this heap. -/
theorem NativeOpenedPosition.rotationReturnsDirectoryError
    {heap : Type} {opened : NativeOpenedHandle heap} (current : NativeOpenedPosition opened)
    (calls : OpenRotationCallbacks heap) (raw : RawSyncCalls heap)
    (cache : OpenSyncCacheRefs opened.files opened.directory.path)
    (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    {poisoned afterFileSync issued reached : heap} {handle : IO.FS.Handle} {cause : IO.Error}
    (nonempty : current.current.ready.state.writer.installed.activeFirst <
      current.current.ready.state.writer.installed.walBytes / WAL.frameSize)
    (checked : checkActiveSegmentWith (m := EStateM IO.Error heap)
      opened.directory current.current.ready.state.writer.installed (fun path => liftExcept (lookup path))
      current.reached = .ok () current.reached)
    (poisonedAt : opened.set opened.phase .poisoned current.reached = .ok () poisoned)
    (filePrefix : calls.SuccessorFilePrefix opened.directory
      (current.current.ready.state.writer.installed.walBytes / WAL.frameSize) poisoned afterFileSync)
    (rootSync : calls.sync opened.directory.path afterFileSync =
      raw.group opened.directory.path cache.directory cache.active cache.pending #[opened.directory.path] afterFileSync)
    (loaded : raw.readDirectory cache.directory afterFileSync = .ok (some handle) issued)
    (failed : raw.fsync handle issued = .error cause reached) :
    UsesRotationSchedule opened.table opened.directory opened.phase cache.active cache.pending cache.directory ∧
    opened.contents poisoned opened.phase = some .poisoned ∧
    calls.run opened lookup cache.active current.reached =
      .error (IO.userError s!"sync failed for '{opened.directory.path}': {cause}") reached ∧
    ∀ {frame : heap → heap → Prop}
      (_trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after),
      let keeps := fun before after => frame before after ∧ opened.contents after opened.phase = opened.contents before opened.phase
      keeps poisoned filePrefix.afterRead →
      (filePrefix.observed = none → keeps filePrefix.afterRead filePrefix.beforeSync) →
      keeps filePrefix.beforeSync afterFileSync → keeps afterFileSync issued → keeps issued reached →
      opened.contents reached opened.phase = some .poisoned ∧
        frame poisoned reached ∧ (frame current.reached poisoned → frame current.reached reached) := by
  have phase := current.current.ready.readPrefix.refines.1.phase
  have stored := current.stored.trans (congrArg some phase)
  have original := opened.phaseEffects.reads current.reached opened.phase _ stored
  obtain ⟨actual, assigned, storedPoison⟩ :=
    opened.phaseEffects.writes current.reached opened.phase _ .poisoned stored
  have same := (EStateM.Result.ok.inj (assigned.symm.trans poisonedAt)).2
  have rootError : calls.sync opened.directory.path afterFileSync =
      .error (IO.userError s!"sync failed for '{opened.directory.path}': {cause}") reached := by
    rw [rootSync, (raw.rootBarrier cache loaded).2, failed]
  have stopped := filePrefix.returnsDirectoryError rootError
  refine ⟨rotationSchedule opened.uses cache.references cache.atRoot, same ▸ storedPoison, ?_, ?_⟩
  · simp only [OpenRotationCallbacks.run, rotateWalSchedule, Bind.bind, EStateM.bind, original, Phase.installed,
      Pure.pure, EStateM.pure, nonempty, ↓reduceIte, checked, publishPrepared, poisonedAt, stopped]
  · intro frame trans keeps read created fileSync load failedSync
    have compose {a b c} (first : keeps a b) (second : keeps b c) : keeps a c :=
      ⟨trans first.1 second.1, second.2.trans first.2⟩
    have touched := compose (filePrefix.frames compose read created fileSync) (compose load failedSync)
    exact ⟨touched.2.trans (same ▸ storedPoison), touched.1, fun poison => trans poison touched.1⟩

end Alvoki.Storage.DiskSession
