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

end Alvoki.Storage
