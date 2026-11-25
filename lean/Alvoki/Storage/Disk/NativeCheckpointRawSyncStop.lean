import Alvoki.Storage.Disk.NativeOpenCheckpointScheduleStop
import Alvoki.Storage.Disk.NativeRawSync

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting

private abbrev RawSyncM (heap : Type) := ExceptT IO.Error (EStateM FilePath heap)

private def returned {heap α : Type} (action : EStateM IO.Error heap α) : RawSyncM heap α :=
  fun before => match action before with
    | .ok value reached => .ok (.ok value) reached
    | .error cause reached => .ok (.error cause) reached

/-- The native cache selectors and syscall, interpreted at their raw
heap. Only the syscall can issue without returning. -/
structure CheckpointRawSyncCalls (heap : Type) extends RawSyncCacheCalls heap where
  fsync : IO.FS.Handle → EStateM FilePath heap (Except IO.Error Unit)

variable {heap image : Type} {opened : NativeOpenedHandle heap}

abbrev CheckpointRawSyncCalls.select (calls : CheckpointRawSyncCalls heap) (dir path : FilePath)
    (directory : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) : RawSyncM heap Unit :=
  calls.toRawSyncCacheCalls.syncPath returned calls.fsync dir path directory active pending

abbrev CheckpointRawSyncCalls.group (calls : CheckpointRawSyncCalls heap) (dir path : FilePath)
    (directory : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) :
    EStateM FilePath heap (Except IO.Error Unit) :=
  (SyncPathGroup.run (fun name => calls.select dir name directory active pending) #[path]).run

private theorem checkpointRawGroupStops (call : FilePath → RawSyncM heap Unit)
    {path reason : FilePath} {before after : heap}
    (issued : (call path).run before = .error reason after) :
    (SyncPathGroup.run call #[path]).run before = .error reason after := by
  change call path before = _ at issued
  simp [SyncPathGroup.run, ← Array.forIn_toList, List.forIn_cons, List.forIn_nil,
    MonadExcept.tryCatch, MonadExceptOf.tryCatch, tryCatchThe, ExceptT.tryCatch, Bind.bind,
    ExceptT.bind, ExceptT.run, ExceptT.mk, EStateM.bind, StateT.pure, Pure.pure, ExceptT.pure, issued]

/-- The literal selected handle still carries the same open slot and
inode at the syscall. Other live descriptions may have changed. -/
structure CheckpointFsyncTarget (view : OpenCloseHeapView heap image) (selected issued : heap)
    (handle : IO.FS.Handle) : Prop where
  slot : (view.handle issued handle).2.1 = (view.handle selected handle).2.1
  live : (view.handle issued handle).2.1 ∈ (view.descriptors issued).slots
  inode : (view.descriptors issued).inode (view.handle issued handle).2.1.description =
    (view.handle selected handle).1.inode (view.handle selected handle).2.1.description

variable {current : NativeOpenedPosition opened}
  {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap} {fsync : CheckpointFsync heap}
  {reason : FilePath} {reached : CheckpointWorld heap}
  {view : OpenCloseHeapView heap image}
  {directory : IO.Ref (Option IO.FS.Handle)} {active : IO.Ref (Option (FilePath × IO.FS.Handle))}
  {pending : IO.Ref (List (FilePath × IO.FS.Handle))}

/-- Invert the raw pending-cell projection at the selected path. The
literal handle is the first matching entry, including when the list
contains unrelated entries or older handles for the same path. -/
private theorem rawPendingSelection {before : heap} {cache : CensusDirectoryCache}
    {path : FilePath} {handle : CheckpointOpenHandle}
    (projected : view.cacheAt before directory active pending = cache.remember path handle) :
    ∃ literal,
      (view.pending before pending).find? (fun entry => entry.1 == path) = some (path, literal) ∧
      view.handle before literal = handle := by
  have entries := congrArg Cache.pending projected
  change (view.pending before pending).map (fun entry => (entry.1, view.handle before entry.2)) =
    (path, handle) :: cache.pending at entries
  cases observed : view.pending before pending with
  | nil => simp [observed] at entries
  | cons entry rest =>
    obtain ⟨name, literal⟩ := entry
    simp only [observed, List.map_cons, List.cons.injEq, Prod.mk.injEq] at entries
    obtain ⟨⟨rfl, identity⟩, _⟩ := entries
    exact ⟨literal, by simp, identity⟩

/-- The run's stopped primitive consumes the pending ref before calling
fsync on the literal handle selected by the source run. The primitive
simulation relates that syscall's actual entry heap to the normalized
operation, which consumes its projected cache in a single step. -/
theorem NativeCheckpointSourceStop.runFileIssuesRawSync {index : Nat}
    (stop : NativeCheckpointSourceStop current primitives fsync (.syncRun index) reason reached)
    (calls : CheckpointRawSyncCalls heap)
    (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
    (projected : view.cacheAt stop.atIssue.2 cache.directory cache.active cache.pending = stop.atIssue.1)
    (load : calls.readPending cache.pending stop.atIssue.2 = .ok (view.pending stop.atIssue.2 cache.pending) stop.atIssue.2)
    {atFsync : heap}
    (store : calls.setPending cache.pending
      ((view.pending stop.atIssue.2 cache.pending).filter
        (fun entry => entry.1 != current.current.ready.state.session.directory.file (.run stop.next.generation index)))
      stop.atIssue.2 = .ok () atFsync)
    (stored : view.pending atFsync cache.pending = (view.pending stop.atIssue.2 cache.pending).filter
      (fun entry => entry.1 != current.current.ready.state.session.directory.file (.run stop.next.generation index)))
    (primitive : ∀ literal,
      (view.pending stop.atIssue.2 cache.pending).find? (fun entry => entry.1 ==
        current.current.ready.state.session.directory.file (.run stop.next.generation index)) =
        some (current.current.ready.state.session.directory.file (.run stop.next.generation index), literal) →
      fsync (view.handle stop.atIssue.2 literal) stop.atIssue.2 = calls.fsync literal atFsync ∧
        CheckpointFsyncTarget view stop.atIssue.2 atFsync literal) :
    let root := current.current.ready.state.session.directory
    let path := root.file (.run stop.next.generation index)
    ∃ literal,
      (view.pending stop.atIssue.2 cache.pending).find? (fun entry => entry.1 == path) = some (path, literal) ∧
      (view.pending atFsync cache.pending).find? (fun entry => entry.1 == path) = none ∧
      CheckpointFsyncTarget view stop.atIssue.2 atFsync literal ∧
      fsync (view.handle stop.atIssue.2 literal) stop.atIssue.2 = .error reason reached.2 ∧
      calls.fsync literal atFsync = .error reason reached.2 ∧
      calls.group root.path path cache.directory cache.active cache.pending stop.atIssue.2 = .error reason reached.2 := by
  intro root path
  obtain ⟨beforeWrite, _, handle, _, _, _, remembered, _, stopped⟩ := stop.runFileUsesWrittenHandle
  have rememberedCache : view.cacheAt stop.atIssue.2 cache.directory cache.active cache.pending = beforeWrite.1.remember path handle :=
    projected.trans remembered
  obtain ⟨literal, found, identity⟩ := rawPendingSelection rememberedCache
  have sourceFsync := identity.symm ▸ stopped
  obtain ⟨physical, custody⟩ := primitive literal found
  have rawFsync := physical.symm.trans sourceFsync
  have separate : path ≠ root.path := file_ne_directory _ _
  change calls.setPending cache.pending ((view.pending stop.atIssue.2 cache.pending).filter (fun entry => entry.1 != path))
    stop.atIssue.2 = .ok () atFsync at store
  have selected : (calls.select root.path path cache.directory cache.active cache.pending).run stop.atIssue.2 =
      .error reason reached.2 := by
    simp [CheckpointRawSyncCalls.select, syncWithHandles, separate, returned, load, found, store,
      rawFsync, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.run, ExceptT.mk, EStateM.bind,
      Pure.pure, ExceptT.pure, EStateM.pure]
  have missing : (view.pending atFsync cache.pending).find? (fun entry => entry.1 == path) = none := by
    change view.pending atFsync cache.pending = (view.pending stop.atIssue.2 cache.pending).filter
      (fun entry => entry.1 != path) at stored
    rw [stored, List.find?_eq_none]
    intro entry member
    have separate : entry.1 ≠ path := by simpa using (List.mem_filter.mp member).2
    exact fun same => separate (beq_iff_eq.mp same)
  exact ⟨literal, found, missing, custody, sourceFsync, rawFsync, checkpointRawGroupStops _ selected⟩

/-- The first directory barrier chooses the literal handle held in the
original directory cache, at the exact heap reached by the file prefix.
It neither consumes a pending entry nor consults a fallback file open. -/
theorem NativeCheckpointSourceStop.runsDirectoryIssuesRawSync
    (stop : NativeCheckpointSourceStop current primitives fsync .syncRunsDirectory reason reached)
    (calls : CheckpointRawSyncCalls heap)
    (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
    (projected : view.cacheAt stop.atIssue.2 cache.directory cache.active cache.pending = stop.atIssue.1)
    (load : calls.readDirectory cache.directory stop.atIssue.2 = .ok (view.directory stop.atIssue.2 cache.directory) stop.atIssue.2)
    (primitive : ∀ literal, view.directory stop.atIssue.2 cache.directory = some literal →
      fsync (view.handle stop.atIssue.2 literal) stop.atIssue.2 = calls.fsync literal stop.atIssue.2 ∧
        CheckpointFsyncTarget view stop.atIssue.2 stop.atIssue.2 literal) :
    let dir := current.current.ready.state.session.directory.path
    ∃ literal, view.directory stop.atIssue.2 cache.directory = some literal ∧
      current.current.ready.state.cache.directory = some (view.handle stop.atIssue.2 literal) ∧
      CheckpointFsyncTarget view stop.atIssue.2 stop.atIssue.2 literal ∧
      calls.fsync literal stop.atIssue.2 = .error reason reached.2 ∧
      calls.group dir dir cache.directory cache.active cache.pending stop.atIssue.2 = .error reason reached.2 := by
  intro dir
  obtain ⟨handle, cached, issuing, _, stopped⟩ := stop.runsDirectoryUsesCachedHandle
  have projectedDirectory := congrArg Cache.directory projected
  change (view.directory stop.atIssue.2 cache.directory).map (view.handle stop.atIssue.2) = stop.atIssue.1.directory at projectedDirectory
  rw [issuing] at projectedDirectory
  cases rawDirectory : view.directory stop.atIssue.2 cache.directory with
  | none => simp [rawDirectory] at projectedDirectory
  | some literal =>
    simp only [rawDirectory, Option.map_some, Option.some.injEq] at projectedDirectory
    have sourceFsync := projectedDirectory.symm ▸ stopped
    obtain ⟨physical, custody⟩ := primitive literal rawDirectory
    have rawFsync := physical.symm.trans sourceFsync
    have selected : (calls.select dir dir cache.directory cache.active cache.pending).run stop.atIssue.2 =
        .error reason reached.2 := by
      simp [CheckpointRawSyncCalls.select, syncWithHandles, returned, load, rawDirectory,
        rawFsync, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.run, ExceptT.mk, EStateM.bind,
        Pure.pure, ExceptT.pure, EStateM.pure]
    exact ⟨literal, rfl, projectedDirectory.symm ▸ cached, custody, rawFsync, checkpointRawGroupStops _ selected⟩

end Alvoki.Storage.DiskSession
