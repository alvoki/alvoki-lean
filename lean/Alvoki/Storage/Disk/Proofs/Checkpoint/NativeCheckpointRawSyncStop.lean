import Alvoki.Storage.Disk.Proofs.Native.Checkpoint.NativeOpenCheckpointScheduleStop
import Alvoki.Storage.Disk.Proofs.Native.Recovery.NativeRawSync

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

/-- Observations of the pending-cell selection at one file barrier.
The retained descriptor is checked again at the resulting syscall heap. -/
structure CheckpointPendingSyncAt (calls : CheckpointRawSyncCalls heap)
    (view : OpenCloseHeapView heap image) (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (fsync : CheckpointFsync heap) (path : FilePath) (entry atFsync : heap) : Prop where
  loaded : calls.readPending pending entry = .ok (view.pending entry pending) entry
  stored : calls.setPending pending ((view.pending entry pending).filter (fun pair => pair.1 != path)) entry = .ok () atFsync
  consumed : view.pending atFsync pending = (view.pending entry pending).filter (fun pair => pair.1 != path)
  primitive : ∀ literal, (view.pending entry pending).find? (fun pair => pair.1 == path) = some (path, literal) →
    fsync (view.handle entry literal) entry = calls.fsync literal atFsync ∧ RawFsyncTarget view entry atFsync literal

private theorem checkpointPendingIssuesRawSync {files : DiskTable.OpenSyncFiles} {root path : FilePath}
    (calls : CheckpointRawSyncCalls heap) (cache : OpenSyncCacheRefs files root)
    {entry atFsync rawReached : heap} {earlier : CensusDirectoryCache} {handle : CheckpointOpenHandle}
    (separate : path ≠ root)
    (remembered : view.cacheAt entry cache.directory cache.active cache.pending = earlier.remember path handle)
    (observed : CheckpointPendingSyncAt calls view cache.pending fsync path entry atFsync)
    (stopped : fsync handle entry = .error reason rawReached) :
    ∃ literal, (view.pending entry cache.pending).find? (fun pair => pair.1 == path) = some (path, literal) ∧
      (view.pending atFsync cache.pending).find? (fun pair => pair.1 == path) = none ∧
      RawFsyncTarget view entry atFsync literal ∧
      fsync (view.handle entry literal) entry = .error reason rawReached ∧
      calls.fsync literal atFsync = .error reason rawReached ∧
      calls.group root path cache.directory cache.active cache.pending entry = .error reason rawReached := by
  obtain ⟨literal, found, identity⟩ := rawPendingSelection remembered
  have sourceFsync := identity.symm ▸ stopped
  obtain ⟨physical, custody⟩ := observed.primitive literal found
  have rawFsync := physical.symm.trans sourceFsync
  have selected : (calls.select root path cache.directory cache.active cache.pending).run entry =
      .error reason rawReached := by
    simp [CheckpointRawSyncCalls.select, syncWithHandles, separate, returned, observed.loaded, found, observed.stored,
      rawFsync, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.run, ExceptT.mk, EStateM.bind,
      Pure.pure, ExceptT.pure, EStateM.pure]
  have missing : (view.pending atFsync cache.pending).find? (fun pair => pair.1 == path) = none := by
    rw [observed.consumed, List.find?_eq_none]
    intro pair member
    have other : pair.1 ≠ path := by simpa using (List.mem_filter.mp member).2
    exact fun same => other (beq_iff_eq.mp same)
  exact ⟨literal, found, missing, custody, sourceFsync, rawFsync, checkpointRawGroupStops _ selected⟩

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
        RawFsyncTarget view stop.atIssue.2 atFsync literal) :
    let root := current.current.ready.state.session.directory
    let path := root.file (.run stop.next.generation index)
    ∃ literal,
      (view.pending stop.atIssue.2 cache.pending).find? (fun entry => entry.1 == path) = some (path, literal) ∧
      (view.pending atFsync cache.pending).find? (fun entry => entry.1 == path) = none ∧
      RawFsyncTarget view stop.atIssue.2 atFsync literal ∧
      fsync (view.handle stop.atIssue.2 literal) stop.atIssue.2 = .error reason reached.2 ∧
      calls.fsync literal atFsync = .error reason reached.2 ∧
      calls.group root.path path cache.directory cache.active cache.pending stop.atIssue.2 = .error reason reached.2 := by
  intro root path
  obtain ⟨beforeWrite, _, handle, _, _, _, remembered, _, stopped⟩ := stop.runFileUsesWrittenHandle
  exact checkpointPendingIssuesRawSync calls cache (file_ne_directory _ _) (projected.trans remembered)
    ⟨load, store, stored, primitive⟩ stopped

/-- The staged manifest barrier consumes the same literal handle
selected by the completed write from the whole stopped checkpoint. -/
theorem NativeCheckpointSourceStop.manifestSyncIssuesRawSync
    (stop : NativeCheckpointSourceStop current primitives fsync (.manifest .syncStaged) reason reached)
    (calls : CheckpointRawSyncCalls heap)
    (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
    (projected : view.cacheAt stop.atIssue.2 cache.directory cache.active cache.pending = stop.atIssue.1)
    {atFsync : heap}
    (observed : CheckpointPendingSyncAt calls view cache.pending fsync
      (current.current.ready.state.session.directory.file .stagedManifest) stop.atIssue.2 atFsync) :
    let root := current.current.ready.state.session.directory
    let path := root.file .stagedManifest
    ∃ literal,
      (view.pending stop.atIssue.2 cache.pending).find? (fun entry => entry.1 == path) = some (path, literal) ∧
      (view.pending atFsync cache.pending).find? (fun entry => entry.1 == path) = none ∧
      RawFsyncTarget view stop.atIssue.2 atFsync literal ∧
      fsync (view.handle stop.atIssue.2 literal) stop.atIssue.2 = .error reason reached.2 ∧
      calls.fsync literal atFsync = .error reason reached.2 ∧
      calls.group root.path path cache.directory cache.active cache.pending stop.atIssue.2 = .error reason reached.2 := by
  intro root path
  obtain ⟨beforeWrite, _, _, _, remembered, _, stopped⟩ := stop.manifestSyncUsesWrittenHandle
  exact checkpointPendingIssuesRawSync calls cache (file_ne_directory _ .stagedManifest)
    (projected.trans remembered) observed stopped

/-- The actual cache load and fsync at one directory barrier. -/
structure CheckpointRawSyncCalls.DirectoryAt (calls : CheckpointRawSyncCalls heap)
    (view : OpenCloseHeapView heap image) (directory : IO.Ref (Option IO.FS.Handle))
    (fsync : CheckpointFsync heap) (entry : heap) : Prop where
  load : calls.readDirectory directory entry = .ok (view.directory entry directory) entry
  primitive : ∀ literal, view.directory entry directory = some literal →
    fsync (view.handle entry literal) entry = calls.fsync literal entry ∧ RawFsyncTarget view entry entry literal

private abbrev directoryProjection (view : OpenCloseHeapView heap image)
    (directory : IO.Ref (Option IO.FS.Handle)) (atHeap : heap) : Option CheckpointOpenHandle :=
  (view.directory atHeap directory).map (view.handle atHeap)

/-- Frame the opened directory projection at the phase update and at
returned checkpoint steps. Rename is framed at its literal callback. -/
structure NativeCheckpointSourcePrefix.DirectoryProjectionEffects {stage : Step}
    (prior : NativeCheckpointSourcePrefix current primitives fsync stage)
    (view : OpenCloseHeapView heap image) (directory : IO.Ref (Option IO.FS.Handle)) : Prop where
  poison : opened.set opened.phase .poisoned current.reached = .ok () prior.poisoned →
    directoryProjection view directory prior.poisoned = directoryProjection view directory current.reached
  returned : ∀ step ∈ prior.completed, step ≠ .manifest .renameStaged → ∀ before after,
    (primitives.checkpointStepUntilStop current.current.ready.state.session.directory fsync
      prior.next prior.manifest step).run before = .ok (.ok ()) after →
    directoryProjection view directory after.2 = directoryProjection view directory before.2
  rename : ∀ {before after},
    let root := current.current.ready.state.session.directory
    primitives.rename (root.file .stagedManifest) (root.file .manifest) before = .ok () after →
    directoryProjection view directory after = directoryProjection view directory before

/-- Derive agreement at issue from the raw cache of the opened handle,
the actual poison setter and the reached successful checkpoint prefix. -/
theorem NativeCheckpointSourcePrefix.projectsDirectoryAtIssue {stage : Step}
    (prior : NativeCheckpointSourcePrefix current primitives fsync stage)
    (view : OpenCloseHeapView heap image) (directory : IO.Ref (Option IO.FS.Handle))
    (initial : (view.directory current.reached directory).map (view.handle current.reached) =
      current.current.ready.state.cache.directory)
    (effects : prior.DirectoryProjectionEffects view directory) :
    (view.directory prior.atIssue.2 directory).map (view.handle prior.atIssue.2) =
      prior.atIssue.1.directory := by
  let project := directoryProjection view directory
  let root := current.current.ready.state.session.directory
  have kept : project prior.atIssue.2 = project prior.poisoned :=
    successfulCheckpointStepsPreserve _ (fun world => project world.2) (fun before after => after = before)
      (fun _ => rfl) (fun earlier later => later.trans earlier) prior.completed (by
        intro step member before after returned
        by_cases isRename : step = .manifest .renameStaged
        · subst step
          exact effects.rename (primitives.manifestRenameReturned root fsync prior.next prior.manifest returned).1
        · exact effects.returned step member isRename before after returned) prior.returnedPrefix
  exact kept.trans ((effects.poison prior.setsPoisoned).trans (initial.trans prior.directoryCacheAtIssue.symm))

private theorem checkpointDirectoryIssuesRawSync {files : DiskTable.OpenSyncFiles} {dir : FilePath}
    (calls : CheckpointRawSyncCalls heap)
    (cache : OpenSyncCacheRefs files dir) {issued rawReached : heap}
    {original : Option CheckpointOpenHandle} {handle : CheckpointOpenHandle}
    (cached : original = some handle)
    (projected : (view.directory issued cache.directory).map (view.handle issued) = some handle)
    (routing : calls.DirectoryAt view cache.directory fsync issued)
    (stopped : fsync handle issued = .error reason rawReached) :
    ∃ literal, view.directory issued cache.directory = some literal ∧
      original = some (view.handle issued literal) ∧
      RawFsyncTarget view issued issued literal ∧ calls.fsync literal issued = .error reason rawReached ∧
      calls.group dir dir cache.directory cache.active cache.pending issued = .error reason rawReached := by
  cases rawDirectory : view.directory issued cache.directory with
  | none => simp [rawDirectory] at projected
  | some literal =>
    simp only [rawDirectory, Option.map_some, Option.some.injEq] at projected
    have sourceFsync := projected.symm ▸ stopped
    obtain ⟨physical, custody⟩ := routing.primitive literal rawDirectory
    have rawFsync := physical.symm.trans sourceFsync
    have selected : (calls.select dir dir cache.directory cache.active cache.pending).run issued =
        .error reason rawReached := by
      simp [CheckpointRawSyncCalls.select, syncWithHandles, returned, routing.load, rawDirectory,
        rawFsync, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.run, ExceptT.mk, EStateM.bind,
        Pure.pure, ExceptT.pure, EStateM.pure]
    exact ⟨literal, rfl, projected.symm ▸ cached, custody, rawFsync, checkpointRawGroupStops _ selected⟩

/-- The first directory barrier chooses the literal handle held in the
original directory cache, at the exact heap reached by the file prefix.
It neither consumes a pending entry nor consults a fallback file open. -/
theorem NativeCheckpointSourceStop.runsDirectoryIssuesRawSync
    (stop : NativeCheckpointSourceStop current primitives fsync .syncRunsDirectory reason reached)
    (calls : CheckpointRawSyncCalls heap)
    (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
    (projected : (view.directory stop.atIssue.2 cache.directory).map (view.handle stop.atIssue.2) =
      stop.atIssue.1.directory)
    (routing : calls.DirectoryAt view cache.directory fsync stop.atIssue.2) :
    let dir := current.current.ready.state.session.directory.path
    ∃ literal, view.directory stop.atIssue.2 cache.directory = some literal ∧
      current.current.ready.state.cache.directory = some (view.handle stop.atIssue.2 literal) ∧
      RawFsyncTarget view stop.atIssue.2 stop.atIssue.2 literal ∧
      calls.fsync literal stop.atIssue.2 = .error reason reached.2 ∧
      calls.group dir dir cache.directory cache.active cache.pending stop.atIssue.2 = .error reason reached.2 := by
  obtain ⟨_, cached, issuing, _, stopped⟩ := stop.runsDirectoryUsesCachedHandle
  exact checkpointDirectoryIssuesRawSync calls cache cached (projected.trans issuing) routing stopped

/-- The same literal routing proof applies after the returned rename.
Only the directory cell needs to match the modeled cache at issue. -/
theorem NativeCheckpointSourceStop.manifestDirectoryIssuesRawSync
    (stop : NativeCheckpointSourceStop current primitives fsync (.manifest .syncDirectory) reason reached)
    (calls : CheckpointRawSyncCalls heap)
    (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
    (projected : (view.directory stop.atIssue.2 cache.directory).map (view.handle stop.atIssue.2) =
      stop.atIssue.1.directory)
    (routing : calls.DirectoryAt view cache.directory fsync stop.atIssue.2) :
    let dir := current.current.ready.state.session.directory.path
    ∃ literal, view.directory stop.atIssue.2 cache.directory = some literal ∧
      current.current.ready.state.cache.directory = some (view.handle stop.atIssue.2 literal) ∧
      RawFsyncTarget view stop.atIssue.2 stop.atIssue.2 literal ∧
      calls.fsync literal stop.atIssue.2 = .error reason reached.2 ∧
      calls.group dir dir cache.directory cache.active cache.pending stop.atIssue.2 = .error reason reached.2 := by
  obtain ⟨_, cached, issuing, _, stopped⟩ := stop.manifestDirectoryUsesCachedHandle
  exact checkpointDirectoryIssuesRawSync calls cache cached (projected.trans issuing) routing stopped

end Alvoki.Storage.DiskSession
