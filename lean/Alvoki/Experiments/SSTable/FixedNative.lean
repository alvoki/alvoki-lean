import Alvoki.Experiments.SSTable.FixedBuilder
import Alvoki.Experiments.SSTable.FixedReader
import Alvoki.Experiments.SSTable.Native

namespace ImmutableSSTable.Fixed

def openNative (path : System.FilePath) : EIO String (Table (EIO String)) := do
  let handle ← (IO.FS.Handle.mk path .read).toEIO toString
  openTable (handleSource handle)

def openNativeChecked (path : System.FilePath) (expectedTableId : UInt64) :
    EIO String (Table (EIO String)) := do
  let handle ← (IO.FS.Handle.mk path .read).toEIO toString
  openTableChecked (handleSource handle) expectedTableId

private def buildFileWithSync (path : System.FilePath) (layout : Layout) (nextRow : IO (Option Entry))
    (syncOutput : IO.FS.Handle → IO Unit) : IO Nat :=
  withFreshOutput path (fun handle => buildStream layout ⟨handle.write, handle.flush⟩ nextRow IO.userError)
    syncOutput

/-- Construct an experimental fixed-width table at a fresh, exclusively owned path. -/
def buildFile (path : System.FilePath) (layout : Layout) (nextRow : IO (Option Entry)) : IO Nat :=
  buildFileWithSync path layout nextRow (fun _ => pure ())

/-- Sync the completed image through the original handle. Publication and
directory syncing belong to the caller. -/
def buildFileSynced (path : System.FilePath) (layout : Layout) (nextRow : IO (Option Entry)) : IO Nat :=
  buildFileWithSync path layout nextRow syncFileHandle

end ImmutableSSTable.Fixed
