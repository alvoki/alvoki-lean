import Alvoki.Storage.Disk.NativeOpenClose
import Alvoki.Storage.Disk.WriteGroupFsync

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting

/-- The cache references installed in one opened table and the root used
for its directory-handle dispatch. -/
structure OpenSyncCacheRefs (files : DiskTable.OpenSyncFiles) (root : FilePath) where
  directory : IO.Ref (Option IO.FS.Handle)
  active : IO.Ref (Option (FilePath × IO.FS.Handle))
  pending : IO.Ref (List (FilePath × IO.FS.Handle))
  references : files.UsesCacheReferences active pending directory
  atRoot : files.AtDirectory root

/-- Cache and fallback-open primitives shared by file sync interpreters. -/
structure RawSyncCacheCalls (heap : Type) where
  readDirectory : IO.Ref (Option IO.FS.Handle) → EStateM IO.Error heap (Option IO.FS.Handle)
  readPending : IO.Ref (List (FilePath × IO.FS.Handle)) → EStateM IO.Error heap (List (FilePath × IO.FS.Handle))
  setPending : IO.Ref (List (FilePath × IO.FS.Handle)) → List (FilePath × IO.FS.Handle) → EStateM IO.Error heap Unit
  readActive : IO.Ref (Option (FilePath × IO.FS.Handle)) → EStateM IO.Error heap (Option (FilePath × IO.FS.Handle))
  openRead : FilePath → EStateM IO.Error heap IO.FS.Handle

/-- Both ordinary returned calls and stopped fsyncs use the same cache
access and order before invoking the selected filesystem primitive. -/
abbrev RawSyncCacheCalls.syncPath (calls : RawSyncCacheCalls heap) [Monad m] [MonadExceptOf IO.Error m]
    (lift : {α : Type} → EStateM IO.Error heap α → m α) (fsync : IO.FS.Handle → m Unit) (root path : FilePath)
    (directory : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) : m Unit :=
  syncWithHandles root path (lift (calls.readDirectory directory)) (lift (calls.readPending pending))
    (fun entries => lift (calls.setPending pending entries)) (lift (calls.readActive active))
    (fun name => lift (calls.openRead name)) fsync

structure RawSyncCalls (heap : Type) extends RawSyncCacheCalls heap where
  fsync : IO.FS.Handle → EStateM IO.Error heap Unit

abbrev RawSyncCalls.syncPath (calls : RawSyncCalls heap) (root path : FilePath)
    (directory : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) : EStateM IO.Error heap Unit :=
  calls.toRawSyncCacheCalls.syncPath (fun action => action) calls.fsync root path directory active pending

/-- Interpret the ordinary grouped `OpenSyncFiles.keeperCacheSchedules`
callback using the original cache cells. -/
def RawSyncCalls.group (calls : RawSyncCalls heap) (root : FilePath)
    (directory : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (paths : Array FilePath) : EStateM IO.Error heap Unit :=
  SyncPathGroup.run (fun path => calls.syncPath root path directory active pending) paths

namespace RawSyncCalls

variable {heap : Type} (calls : RawSyncCalls heap) {files : DiskTable.OpenSyncFiles}

/-- The first matching pending entry is consumed before the syscall.
The raw heap after consuming entries supplies the fsync operand. -/
theorem syncPending {root path : FilePath} (cache : OpenSyncCacheRefs files root) {before consumed : heap}
    {entries : List (FilePath × IO.FS.Handle)} {handle : IO.FS.Handle}
    (notDirectory : path ≠ root) (loaded : calls.readPending cache.pending before = .ok entries before)
    (selected : entries.find? (fun entry => entry.1 == path) = some (path, handle))
    (removed : calls.setPending cache.pending (entries.filter (fun entry => entry.1 != path)) before =
      .ok () consumed) :
    calls.syncPath root path cache.directory cache.active cache.pending before = calls.fsync handle consumed := by
  simp [syncPath, syncWithHandles, notDirectory, loaded, selected, removed, Bind.bind, EStateM.bind,
    Pure.pure, EStateM.pure]

variable
  {directory : DiskDirectory} (cache : OpenSyncCacheRefs files directory.path) {first : Nat}

/-- The active keeper is selected after a pending miss. The staged
marker is consumed on the heap returned by that keeper fsync, including
a keeper error. The pending store can advance the heap before its sync. -/
theorem groupedWal {before consumed : heap} {keeperHandle markerHandle : IO.FS.Handle}
    {keeperEntries markerEntries : List (FilePath × IO.FS.Handle)}
    (loadedKeeper : calls.readPending cache.pending before = .ok keeperEntries before)
    (noPendingKeeper : keeperEntries.find? (fun entry => entry.1 == directory.file (.walSegment first)) = none)
    (activeKeeper : calls.readActive cache.active before =
      .ok (some (directory.file (.walSegment first), keeperHandle)) before)
    (loadedMarker : let afterKeeper := reachedState (calls.fsync keeperHandle before)
      calls.readPending cache.pending afterKeeper = .ok markerEntries afterKeeper)
    (pendingMarker : markerEntries.find? (fun entry => entry.1 == directory.file .stagedWalBoundary) =
      some (directory.file .stagedWalBoundary, markerHandle))
    (removed : calls.setPending cache.pending
      (markerEntries.filter (fun entry => entry.1 != directory.file .stagedWalBoundary))
      (reachedState (calls.fsync keeperHandle before)) = .ok () consumed) :
    let keeper := directory.file (.walSegment first)
    let staged := directory.file .stagedWalBoundary
    let perform := fun path => calls.syncPath directory.path path cache.directory cache.active cache.pending
    perform keeper before = calls.fsync keeperHandle before ∧
    perform staged (reachedState (calls.fsync keeperHandle before)) = calls.fsync markerHandle consumed ∧
    calls.group directory.path cache.directory cache.active cache.pending #[keeper, staged] before =
      match calls.fsync keeperHandle before with
      | .ok () _ => match calls.fsync markerHandle consumed with
        | .ok () reached => .ok () reached
        | .error cause reached => .error (IO.userError s!"sync failed for '{staged}': {cause}") reached
      | .error cause _ => .error (IO.userError s!"sync failed for '{keeper}': {cause}")
          (reachedState (calls.fsync markerHandle consumed)) := by
  intro keeper staged perform
  have keeperFile : keeper ≠ directory.path := file_ne_directory _ _
  have stagedFile : staged ≠ directory.path := file_ne_directory _ _
  have first : perform keeper before = calls.fsync keeperHandle before := by
    simp [perform, syncWithHandles, keeperFile, loadedKeeper, noPendingKeeper, activeKeeper, keeper,
      Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  have second : perform staged (reachedState (calls.fsync keeperHandle before)) = calls.fsync markerHandle consumed :=
    calls.syncPending cache stagedFile loadedMarker pendingMarker removed
  refine ⟨first, second, ?_⟩
  change SyncPathGroup.run perform #[keeper, staged] before = _
  rw [SyncPathGroup.run_pair, first]
  cases outcome : calls.fsync keeperHandle before with
  | ok result reached =>
    cases result
    simp only [outcome, reachedState] at second
    exact congrArg (fun result : EStateM.Result IO.Error heap Unit =>
      show EStateM.Result IO.Error heap Unit from match result with
      | .ok () after => .ok () after
      | .error cause after => .error (IO.userError s!"sync failed for '{staged}': {cause}") after) second
  | error cause reached =>
    simp only [outcome, reachedState] at second
    have retained := congrArg (fun result : EStateM.Result IO.Error heap Unit =>
      show EStateM.Result IO.Error heap Unit from match result with
      | .ok () after | .error _ after => .error (IO.userError s!"sync failed for '{keeper}': {cause}") after) second
    refine retained.trans ?_
    cases calls.fsync markerHandle consumed <;> rfl

end RawSyncCalls
end Alvoki.Storage.DiskSession
