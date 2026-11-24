import Alvoki.Storage.Disk.DiskPaths

namespace Alvoki.Storage.WalSegmentRotation
open System

inductive Step where
  | createEmpty
  | syncFile
  | syncDirectory
  deriving DecidableEq

/-- Creation is needed only for an absent successor. An existing empty
successor still needs both durability operations. -/
def steps (present : Bool) : List Step :=
  if present then [.syncFile, .syncDirectory] else [.createEmpty, .syncFile, .syncDirectory]

def run [Monad m] (present : Bool) (perform : Step → m Unit) : m Unit :=
  (steps present).forM perform

/-- Interpret an optional regular-file read in the locked directory. -/
def observeSuccessorWith [Monad m] [MonadExceptOf IO.Error m] (read : m (Option ByteArray)) : m Bool := do
  match ← read with
  | none => pure false
  | some bytes =>
    if bytes.size = 0 then pure true else throw (IO.userError "WAL segment successor is not empty")

/-- The new inode is empty from exclusive creation until the caller starts
appending after settlement. The file sync belongs to the schedule. -/
def createEmptyExclusive (path : FilePath) : IO Unit := do
  let _ ← IO.FS.Handle.mk path .writeNew
  pure ()

def performPaths [Monad m] (dir : DiskDirectory) (first : Nat)
    (createEmpty sync : FilePath → m Unit) : Step → m Unit
  | .createEmpty => createEmpty (dir.file (.walSegment first))
  | .syncFile => sync (dir.file (.walSegment first))
  | .syncDirectory => sync dir.path

/-- Route rotation under a caller-held writer lock. The caller has selected
the successor's start, supplies the no-follow regular-file read, and keeps
the directory and file identities stable through both syncs. -/
def runAt [Monad m] [MonadExceptOf IO.Error m] (dir : DiskDirectory) (first : Nat)
    (readOptional : FilePath → m (Option ByteArray)) (createEmpty sync : FilePath → m Unit) : m Unit := do
  let present ← observeSuccessorWith (readOptional (dir.file (.walSegment first)))
  run present (performPaths dir first createEmpty sync)

theorem runAt_fileEffects [Monad m] [MonadExceptOf IO.Error m]
    (dir : DiskDirectory) (first : Nat) (readOptional : FilePath → m (Option ByteArray))
    (createEmpty sync : FilePath → m Unit) :
    runAt dir first readOptional createEmpty sync = (do
      let path := dir.file (.walSegment first)
      let present ← observeSuccessorWith (readOptional path)
      if present then
        sync path
        sync dir.path
        pure ()
      else
        createEmpty path
        sync path
        sync dir.path
        pure ()) := by
  unfold runAt
  congr 1
  funext present
  cases present <;> rfl

end Alvoki.Storage.WalSegmentRotation
