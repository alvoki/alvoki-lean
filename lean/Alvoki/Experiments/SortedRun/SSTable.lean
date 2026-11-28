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

/-- Start a fresh merge of two independently checked byte tables. The
returned count follows the synced writer. Directory durability belongs
to the caller that publishes the output name. -/
def buildMergedFileSynced (newer older : Table (EIO String)) (path : System.FilePath)
    (layout : Layout) (options : BuildOptions := {}) : IO Nat := do
  let cursor ← IO.mkRef (Frontier.start (row := Entry) 0 0)
  let slot : Slot IO (Frontier Nat Nat Entry) := ⟨cursor.get, cursor.set⟩
  buildMergedWith Entry.key id
    (fun i => (newer.next i).adapt IO.userError) (fun i => (older.next i).adapt IO.userError)
    slot (nativeOutputOps syncFileHandle) Alvoki.CRC32C.extend path layout IO.userError options

end SortedRun
