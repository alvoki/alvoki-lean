import Alvoki.Experiments.SSTable.Recursive.Builder
import Alvoki.Experiments.SSTable.Recursive.Reader
import Alvoki.Experiments.SSTable.Native
import Alvoki.Codec.CRC32C

namespace ImmutableSSTable.Recursive

open Unified (Checksum Layout)

@[inline] def buildFileWith [Monad m] [MonadExceptOf ε m] (ops : OutputOps m handle)
    (crc : Checksum) (path : System.FilePath) (layout : Layout) (nextRow : m (Option Entry))
    (invalid : String → ε) (options : BuildOptions := {}) : m Nat :=
  withFreshOutputWith (ε := ε) ops path fun held =>
    buildStream crc layout (ops.sink held) nextRow invalid options

def buildFileSynced (path : System.FilePath) (layout : Layout) (nextRow : IO (Option Entry))
    (options : BuildOptions := {}) : IO Nat :=
  buildFileWith (nativeOutputOps syncFileHandle) Alvoki.CRC32C.extend path layout nextRow
    IO.userError options

@[inline] def openCheckedWith [Monad m] [MonadExceptOf String m] (ops : ReadPrimitives m handle)
    (crc : Checksum) (path : System.FilePath) (expectedId : UInt64) : m (Handle m) := do
  let held ← ops.openFile path .read
  openChecked (ops.source held) crc expectedId

def openNativeChecked (path : System.FilePath) (expectedId : UInt64) :
    EIO String (Table (EIO String)) := do
  return (← openCheckedWith nativeReadPrimitives Alvoki.CRC32C.extend path expectedId).table

end ImmutableSSTable.Recursive
