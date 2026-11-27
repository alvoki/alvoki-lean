import Alvoki.Storage.Disk.Proofs.Rotation.NativeOpenRotation
import Alvoki.Storage.Disk.Proofs.Native.WAL.NativeWalStage

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting

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

/-- The exclusive-created handle is remembered and consumed by the
first file barrier. These receipts stop before any root directory sync. -/
structure OpenRotationCallbacks.SuccessorFilePrefix.ExclusiveSync
    (filePrefix : calls.SuccessorFilePrefix directory first entry synced)
    (create : RawWalStageCalls heap) (raw : RawSyncCalls heap)
    {files : DiskTable.OpenSyncFiles} (cache : OpenSyncCacheRefs files directory.path) where
  handle : IO.FS.Handle
  opened : heap
  entries : List (FilePath × IO.FS.Handle)
  loaded : heap
  issued : heap
  openNew : create.create (directory.file (.walSegment first)) filePrefix.afterRead = .ok handle opened
  remember : create.remember cache.pending (pushPending (directory.file (.walSegment first)) handle)
    opened = .ok () filePrefix.beforeSync
  load : raw.readPending cache.pending filePrefix.beforeSync = .ok entries loaded
  consume : raw.setPending cache.pending (entries.filter (fun item => item.1 != directory.file (.walSegment first)))
    loaded = .ok () issued
  sync : raw.fsync handle issued = .ok () synced
  absent : filePrefix.observed = none
  creates : let path := directory.file (.walSegment first)
    calls.create path filePrefix.afterRead = (do
      let handle ← create.create path
      create.remember cache.pending (pushPending path handle)) filePrefix.afterRead
  dispatches : let path := directory.file (.walSegment first)
    calls.sync path filePrefix.beforeSync = raw.group directory.path cache.directory cache.active cache.pending
      #[path] filePrefix.beforeSync
  selects : entries.find? (fun item => item.1 == directory.file (.walSegment first)) =
    some (directory.file (.walSegment first), handle)


/-- The reached absent branch uses exclusive creation. Invert the
existing two callbacks and derive that the pending hit selects the very
handle the create returned, even with older pending entries. -/
theorem OpenRotationCallbacks.SuccessorFilePrefix.reachesExclusiveSync
    (filePrefix : calls.SuccessorFilePrefix directory first entry synced)
    (create : RawWalStageCalls heap) (raw : RawSyncCalls heap)
    {files : DiskTable.OpenSyncFiles} (cache : OpenSyncCacheRefs files directory.path)
    {image : Type} (view : OpenCloseHeapView heap image)
    (absent : filePrefix.observed = none)
    (creation : let path := directory.file (.walSegment first)
      calls.create path filePrefix.afterRead = (do
        let handle ← create.create path
        create.remember cache.pending (pushPending path handle)) filePrefix.afterRead)
    (fileSync : let path := directory.file (.walSegment first)
      calls.sync path filePrefix.beforeSync = raw.group directory.path cache.directory cache.active cache.pending
        #[path] filePrefix.beforeSync)
    (stored : let path := directory.file (.walSegment first)
      ∀ {handle opened}, create.create path filePrefix.afterRead = .ok handle opened →
        create.remember cache.pending (pushPending path handle) opened = .ok () filePrefix.beforeSync →
        view.pending filePrefix.beforeSync cache.pending = pushPending path handle (view.pending opened cache.pending))
    (readPending : ∀ {entries loaded}, raw.readPending cache.pending filePrefix.beforeSync = .ok entries loaded →
      entries = view.pending filePrefix.beforeSync cache.pending) :
    Nonempty (filePrefix.ExclusiveSync create raw cache) := by
  let path := directory.file (.walSegment first)
  have created := filePrefix.successor
  rw [absent] at created
  change calls.create path filePrefix.afterRead = _ at created
  rw [creation] at created
  change (create.create path >>= fun handle =>
    create.remember cache.pending (pushPending path handle)) filePrefix.afterRead = _ at created
  cases exclusive : create.create path filePrefix.afterRead with
  | error cause stopped =>
    simp [Bind.bind, EStateM.bind, exclusive] at created
  | ok handle opened =>
    have remembered : create.remember cache.pending (pushPending path handle) opened = .ok () filePrefix.beforeSync := by
      simpa only [Bind.bind, EStateM.bind, exclusive] using created
    have selected {entries loaded} (read : raw.readPending cache.pending filePrefix.beforeSync = .ok entries loaded) :
        entries.find? (fun item => item.1 == path) = some (path, handle) := by
      rw [readPending read, stored exclusive remembered]
      simp [pushPending, path]
    have grouped : raw.group directory.path cache.directory cache.active cache.pending #[path] filePrefix.beforeSync =
        .ok () synced := fileSync.symm.trans filePrefix.sync
    obtain ⟨entries, loaded, issued, read, firstHit, consume, fsync⟩ :=
      raw.pendingGroupReturned (file_ne_directory directory (.walSegment first)) (fun read => selected read) grouped
    exact ⟨⟨handle, opened, entries, loaded, issued, exclusive, remembered, read, consume, fsync,
      absent, creation, fileSync, firstHit⟩⟩

end FilePrefix

/-- The literal rotation propagates the failed cached root fsync at its
returned heap. The active stat supplies the guard before poisoning. The
active-cache clear and final ready setter lie beyond this failure. -/
theorem NativeOpenedPosition.rotationReturnsDirectoryError
    {heap : Type} {opened : NativeOpenedHandle heap} (current : NativeOpenedPosition opened)
    (calls : OpenRotationCallbacks heap) (raw : RawSyncCalls heap)
    (cache : OpenSyncCacheRefs opened.files opened.directory.path)
    (guard : BatchActiveGuard opened.directory current.current.ready.state.writer.installed)
    {poisoned afterFileSync issued reached : heap} {handle : IO.FS.Handle} {cause : IO.Error}
    (nonempty : current.current.ready.state.writer.installed.activeFirst <
      current.current.ready.state.writer.installed.walBytes / WAL.frameSize)
    (poisonedAt : opened.set opened.phase .poisoned current.reached = .ok () poisoned)
    (filePrefix : calls.SuccessorFilePrefix opened.directory
      (current.current.ready.state.writer.installed.walBytes / WAL.frameSize) poisoned afterFileSync)
    (rootSync : calls.sync opened.directory.path afterFileSync =
      raw.group opened.directory.path cache.directory cache.active cache.pending #[opened.directory.path] afterFileSync)
    (loaded : raw.readDirectory cache.directory afterFileSync = .ok (some handle) issued)
    (failed : raw.fsync handle issued = .error cause reached) :
    UsesRotationSchedule opened.table opened.directory opened.phase cache.active cache.pending cache.directory ∧
    opened.contents poisoned opened.phase = some .poisoned ∧
    calls.run opened guard.lookup cache.active current.reached =
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
  have checked := guard.checked current.reached
  refine ⟨rotationSchedule opened.uses cache.references cache.atRoot, same ▸ storedPoison, ?_, ?_⟩
  · simp only [OpenRotationCallbacks.run, rotateWalSchedule, Bind.bind, EStateM.bind, original, Phase.installed,
      Pure.pure, EStateM.pure, nonempty, ↓reduceIte, checked, publishPrepared, poisonedAt, stopped]
  · intro frame trans keeps read created fileSync load failedSync
    have compose {a b c} (first : keeps a b) (second : keeps b c) : keeps a c :=
      ⟨trans first.1 second.1, second.2.trans first.2⟩
    have touched := compose (filePrefix.frames compose read created fileSync) (compose load failedSync)
    exact ⟨touched.2.trans (same ▸ storedPoison), touched.1, fun poison => trans poison touched.1⟩

end Alvoki.Storage.DiskSession
