import Alvoki.Storage.Publication.RunCollection

namespace Alvoki.Storage
open System

private def removeStaleStagingFile (path : FilePath) : IO Unit := do
  match ← path.symlinkMetadata.toBaseIO with
  | .ok metadata =>
    unless metadata.type == .file do
      throw (IO.userError s!"expected a regular database staging file: '{path}'")
    match RunCollection.ownedUnlinkResult (← (IO.FS.removeFile path).toBaseIO) with
    | .ok () => pure ()
    | .error error => throw error
  | .error (.noFileOrDirectory _ 2 _) => pure ()
  | .error error => throw error

/-- Write a fresh inode at a reserved inactive staging path under the
caller's directory lock. A stale regular binding is detached before
writing, so even a hard link leaves its other names unchanged. A failed
attempt can leave absent or partial scratch contents for the next retry.
The caller syncs the file and publishes it with the separate schedule. -/
def writeFreshStagedHandle (path : FilePath) (bytes : ByteArray) : IO IO.FS.Handle := do
  let file ← match ← (IO.FS.Handle.mk path .writeNew).toBaseIO with
    | .ok file => pure file
    | .error (.alreadyExists _ 17 _) => do
      removeStaleStagingFile path
      IO.FS.Handle.mk path .writeNew
    | .error error => throw error
  file.write bytes
  file.flush
  return file

def writeFreshStagedFile (path : FilePath) (bytes : ByteArray) : IO Unit := do
  let _ ← writeFreshStagedHandle path bytes
  pure ()

/-- Interpret the stale-name cleanup with filesystem reports. Only a
regular binding is detached. A missing name also allows another create. -/
noncomputable def removeStaleStagingWith [Monad m] [MonadExceptOf IO.Error m]
    (stat : FilePath → m (Except IO.Error IO.FS.Metadata))
    (unlink : FilePath → m (Except IO.Error Unit)) (path : FilePath) : m Unit := do
  match ← stat path with
  | .ok metadata =>
    unless metadata.type == .file do
      throw (IO.userError s!"expected a regular database staging file: '{path}'")
    match RunCollection.ownedUnlinkResult (← unlink path) with
    | .ok () => pure ()
    | .error error => throw error
  | .error (.noFileOrDirectory _ 2 _) => pure ()
  | .error error => throw error

/-- Only a reported exclusive-create conflict retries after cleanup. -/
noncomputable def withFreshStaging [Monad m] [MonadExceptOf IO.Error m] {handle α : Type}
    (tryCreate : FilePath → m (Except IO.Error handle)) (detachStale : FilePath → m Unit)
    (create : FilePath → m handle) (path : FilePath) (use : handle → m α) : m α := do
  let file ← match ← tryCreate path with
    | .ok file => pure file
    | .error (.alreadyExists _ 17 _) => do
      detachStale path
      create path
    | .error error => throw error
  use file

/-- Interpret the actual staging schedule under a callback model. The
return value is the exact description opened by the successful create. -/
noncomputable def writeFreshStagedWith [Monad m] [MonadExceptOf IO.Error m] {handle : Type}
    (tryCreate : FilePath → m (Except IO.Error handle)) (detachStale : FilePath → m Unit)
    (create : FilePath → m handle) (write : handle → ByteArray → m Unit)
    (flush : handle → m Unit) (path : FilePath) (bytes : ByteArray) : m handle :=
  withFreshStaging tryCreate detachStale create path fun file => do
    write file bytes
    flush file
    return file

/-- The callback model uses exactly the native staged-file acquisition,
cleanup, write and flush schedule. Native IO continues to use its original
compiled body. -/
theorem writeFreshStagedHandle_schedule (path : FilePath) (bytes : ByteArray) :
    writeFreshStagedHandle path bytes =
      writeFreshStagedWith (m := IO) (fun name => (IO.FS.Handle.mk name .writeNew).toBaseIO)
        (removeStaleStagingWith (m := IO) (fun name => name.symlinkMetadata.toBaseIO)
          (fun name => (IO.FS.removeFile name).toBaseIO))
        (fun name => IO.FS.Handle.mk name .writeNew) IO.FS.Handle.write IO.FS.Handle.flush path bytes := by
  unfold writeFreshStagedHandle writeFreshStagedWith withFreshStaging removeStaleStagingFile removeStaleStagingWith
  congr 1
  funext result
  cases result with
  | ok file => rfl
  | error error =>
    cases error <;> try rfl
    case alreadyExists filename osCode details =>
      unfold writeFreshStagedHandle.match_1 withFreshStaging.match_1
      rfl

end Alvoki.Storage
