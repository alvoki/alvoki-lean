import Alvoki.Experiments.SSTable.Builder

namespace ImmutableSSTable

@[extern "alvoki_sstable_size"]
private opaque handleSize (handle : @& IO.FS.Handle) : IO Nat

@[extern "alvoki_sstable_pread"]
private opaque pread (handle : @& IO.FS.Handle) (offset : UInt64) (count : USize) : IO ByteArray

/-- Retaining the source retains the same open file across rename/unlink. Callers
    keep its contents immutable for the lifetime of any table opened on it. -/
def handleSource (handle : IO.FS.Handle) : Source (EIO String) where
  size := (handleSize handle).toEIO toString
  readAt offset count := do
    if count > maxRowSize || offset + count > maxFileSize then
      throw "SSTable read outside positional I/O bounds"
    (pread handle offset.toUInt64 count.toUSize).toEIO toString

def openNative (path : System.FilePath) : EIO String (Table (EIO String)) := do
  let handle ← (IO.FS.Handle.mk path .read).toEIO toString
  openTable (handleSource handle)

private def copyOffsets (scratch output : IO.FS.Handle) : IO Unit := do
  scratch.flush
  let size ← handleSize scratch
  if size > maxFileSize then
    throw (IO.userError "SSTable offset table exceeds signed offset limit")
  let mut offset := 0
  while offset < size do
    let count := min (64 * 1024) (size - offset)
    let bytes ← pread scratch offset.toUInt64 count.toUSize
    unless bytes.size = count do
      throw (IO.userError "short read from SSTable offset table")
    output.write bytes
    offset := offset + count

/-- On Linux an unlinked temporary file remains accessible through its open
    descriptor. Releasing the handle also releases the scratch space. -/
private def openScratch : IO IO.FS.Handle := do
  let (scratch, path) ← IO.FS.createTempFile
  try
    IO.FS.removeFile path
  catch err =>
    try IO.FS.removeFile path catch _ => pure ()
    throw err
  return scratch

/-- Build at a fresh path owned exclusively by the caller until return.
    Retains one entry and a bounded offset-copy buffer. Crash publication and
    durability belong to the caller. -/
def buildFile (path : System.FilePath) (nextRow : IO (Option Entry)) : IO Nat := do
  let handle ← IO.FS.Handle.mk path .writeNew
  try
    let scratch ← openScratch
    buildStream {
      writeData := handle.write
      writeOffset := scratch.write
      appendOffsets := copyOffsets scratch handle
      flush := handle.flush
    } nextRow IO.userError
  catch err =>
    try IO.FS.removeFile path catch _ => pure ()
    throw err

end ImmutableSSTable
