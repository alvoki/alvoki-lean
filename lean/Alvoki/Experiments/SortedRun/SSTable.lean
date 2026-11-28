import Alvoki.Experiments.SortedRun.Merge
import Alvoki.Experiments.SSTable.UnifiedNative

namespace SortedRun

open ImmutableSSTable ImmutableSSTable.Unified

/-- SSTable rows carry opaque values. The indexed and typed readers can
both serve as pulls without an adapter to their underlying index. -/
@[inline] def buildMergedWith [Monad m] [MonadExceptOf ε m]
    [LT key] [DecidableLT key] (keyOf : row → key) (encode : row → Entry)
    (newer : Pull m left row) (older : Pull m right row) (slot : Slot m (Frontier left right row))
    (output : OutputOps m handle) (crc : Checksum) (path : System.FilePath)
    (layout : Layout) (invalid : String → ε) (options : BuildOptions := {}) : m Nat :=
  buildFileWith output crc path layout (Option.map encode <$> next keyOf newer older slot)
    invalid options

/-- The native frontier slot touches only the reference allocated for this
merge. The input callbacks and output primitives never receive that reference. -/
def nativeSlot (ref : IO.Ref α) : Slot IO α :=
  ⟨ref.get, ref.set⟩

def tablePullIO (table : Table (EIO String)) : Pull IO Nat Entry :=
  fun index => (table.next index).adapt IO.userError

/-- Run the synced writer with the private frontier allocated by the caller. -/
def buildMergedOnRef (newer older : Table (EIO String))
    (cursor : IO.Ref (Frontier Nat Nat Entry)) (path : System.FilePath)
    (layout : Layout) (options : BuildOptions) : IO Nat :=
  buildMergedWith Entry.key id (tablePullIO newer) (tablePullIO older)
    (nativeSlot cursor) (nativeOutputOps syncFileHandle) Alvoki.CRC32C.extend
    path layout IO.userError options

/-- Start a fresh merge of two independently checked byte tables. Input
acquisition, lifetime and directory durability belong to the caller. -/
def buildMergedFileSynced (newer older : Table (EIO String)) (path : System.FilePath)
    (layout : Layout) (options : BuildOptions := {}) : IO Nat := do
  let cursor ← IO.mkRef (Frontier.start (row := Entry) 0 0)
  buildMergedOnRef newer older cursor path layout options

end SortedRun
