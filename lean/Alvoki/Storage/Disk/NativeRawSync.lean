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

end RawSyncCalls
end Alvoki.Storage.DiskSession
