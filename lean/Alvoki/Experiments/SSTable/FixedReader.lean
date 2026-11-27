import Alvoki.Experiments.SSTable.FixedFormat

namespace ImmutableSSTable.Fixed

/-- Read one footer and verify the exact file extent. Data blocks are lazy. -/
def openLayout [Monad m] [MonadExceptOf String m] (source : Source m) : m (Layout × Nat) := do
  let size ← source.size
  unless footerSize ≤ size ∧ size ≤ maxFileSize do throw "invalid fixed SSTable file size"
  let bytes ← source.readAt (size - footerSize) footerSize
  let (layout, count) ← liftDecode (decodeFooter bytes)
  unless layout.fileSize count = size do throw "invalid fixed SSTable extent"
  return (layout, count)

/-- Read and verify the block at the reader's independently calculated position.
The layout and count come from a checked footer. -/
def readBlock [Monad m] [MonadExceptOf String m] (source : Source m)
    (layout : Layout) (count block : Nat) : m ByteArray := do
  let rows := layout.blockRows count block
  unless 0 < rows do throw "fixed SSTable block out of bounds"
  let bytes ← source.readAt (layout.blockOffset block) (layout.blockReadSize count block)
  liftDecode (decodeBlock layout block rows bytes)

def readEntry [Monad m] [MonadExceptOf String m] (source : Source m)
    (layout : Layout) (count index : Nat) : m Entry := do
  let payload ← readBlock source layout count (index / layout.rowsPerBlock)
  return readRow layout payload (index % layout.rowsPerBlock)

/-- Use the same row cursor, lookup, seek and typed adapters as ALVSST03. -/
def openTable [Monad m] [MonadExceptOf String m] (source : Source m) : m (Table m) := do
  let (layout, count) ← openLayout source
  return Table.ofReader count (readEntry source layout count)

end ImmutableSSTable.Fixed
