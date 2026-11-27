import Alvoki.Experiments.SSTable.UnifiedBuilder
import Alvoki.Experiments.SSTable.UnifiedReader
import Alvoki.Experiments.SSTable.UnifiedNativeIntegrity
import Alvoki.Experiments.SSTable.Native

namespace ImmutableSSTable.Unified

def openNativeChecked (path : System.FilePath) (expectedId : UInt64) :
    EIO String (Table (EIO String)) := do
  let handle ← (IO.FS.Handle.mk path .read).toEIO toString
  openTableChecked (handleSource handle) nativeCRC32C expectedId

/-- Use the original flushed descriptor for the caller's sync operation. -/
def buildFileWithSync (path : System.FilePath) (layout : Layout)
    (nextRow : IO (Option Entry)) (options : BuildOptions)
    (syncOutput : IO.FS.Handle → IO Unit) : IO Nat :=
  withFreshOutput path
    (fun handle => buildStream nativeCRC32C layout ⟨handle.write, handle.flush⟩
      nextRow IO.userError options) syncOutput

def buildFile (path : System.FilePath) (layout : Layout) (nextRow : IO (Option Entry))
    (options : BuildOptions := {}) : IO Nat :=
  buildFileWithSync path layout nextRow options (fun _ => pure ())

def buildFileSynced (path : System.FilePath) (layout : Layout) (nextRow : IO (Option Entry))
    (options : BuildOptions := {}) : IO Nat :=
  buildFileWithSync path layout nextRow options syncFileHandle

end ImmutableSSTable.Unified
