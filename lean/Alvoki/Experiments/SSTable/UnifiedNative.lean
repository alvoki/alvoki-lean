import Alvoki.Experiments.SSTable.UnifiedBuilder
import Alvoki.Experiments.SSTable.UnifiedReader
import Alvoki.Codec.CRC32C
import Alvoki.Experiments.SSTable.Native

namespace ImmutableSSTable.Unified

@[inline] def openCheckedWith [Monad m] [MonadExceptOf String m] (ops : ReadPrimitives m handle)
    (crc : Checksum) (path : System.FilePath) (expectedId : UInt64) : m (Table m) := do
  let held ← ops.openFile path .read
  openTableChecked (ops.source held) crc expectedId

def openNativeChecked (path : System.FilePath) (expectedId : UInt64) :
    EIO String (Table (EIO String)) :=
  openCheckedWith nativeReadPrimitives Alvoki.CRC32C.extend path expectedId

/-- The shared exclusive-create, streaming-write, flush and sync schedule. -/
@[inline] def buildFileWith [Monad m] [MonadExceptOf ε m] (ops : OutputOps m handle)
    (crc : Checksum) (path : System.FilePath) (layout : Layout) (nextRow : m (Option Entry))
    (invalid : String → ε) (options : BuildOptions := {}) : m Nat :=
  withFreshOutputWith (ε := ε) ops path fun handle =>
    buildStream crc layout (ops.sink handle) nextRow invalid options

/-- Use the original flushed descriptor for the caller's sync operation. -/
def buildFileWithSync (path : System.FilePath) (layout : Layout)
    (nextRow : IO (Option Entry)) (options : BuildOptions)
    (syncOutput : IO.FS.Handle → IO Unit) : IO Nat :=
  buildFileWith (nativeOutputOps syncOutput) Alvoki.CRC32C.extend path layout nextRow IO.userError options

def buildFile (path : System.FilePath) (layout : Layout) (nextRow : IO (Option Entry))
    (options : BuildOptions := {}) : IO Nat :=
  buildFileWithSync path layout nextRow options (fun _ => pure ())

def buildFileSynced (path : System.FilePath) (layout : Layout) (nextRow : IO (Option Entry))
    (options : BuildOptions := {}) : IO Nat :=
  buildFileWithSync path layout nextRow options syncFileHandle

end ImmutableSSTable.Unified
