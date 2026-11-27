import Alvoki.Experiments.SSTable.FixedNative

namespace ImmutableSSTable.Fixed.Aligned

private def extensionSize : Nat := 24
private def marker : ByteArray := "ALVALN01".toUTF8
private def physicalSize (layout : Layout) (blockSize count : Nat) : Nat :=
  layout.blockCount count * blockSize + Fixed.footerSize + extensionSize

def layoutFor (keyWidth valueWidth blockSize : Nat) (tableId : UInt64) : Layout :=
  ⟨keyWidth, valueWidth, (blockSize - 8) / (keyWidth + valueWidth), tableId⟩

private def valid (layout : Layout) (blockSize : Nat) : Prop :=
  layout.Valid ∧ layout.blockSize ≤ blockSize ∧ blockSize ≤ maxRowSize ∧
    layout = layoutFor layout.keyWidth layout.valueWidth blockSize layout.tableId

private instance (layout : Layout) (blockSize : Nat) : Decidable (valid layout blockSize) := by
  unfold valid
  infer_instance

private def footer (layout : Layout) (blockSize count : Nat) : ByteArray :=
  let metadata := encodeFooter layout count ++ marker ++ encodeOffset blockSize
  Alvoki.pushWordFast metadata (checksum metadata)

/-- Pad every block, including the final one, to the declared physical size.
The placement extension is checked independently of the packed row codec. -/
private def buildFileWithSync (path : System.FilePath) (keyWidth valueWidth blockSize : Nat)
    (tableId : UInt64) (nextRow : IO (Option Entry))
    (syncOutput : IO.FS.Handle → IO Unit) : IO Nat :=
  withFreshOutput path (fun handle => do
    let layout := layoutFor keyWidth valueWidth blockSize tableId
    unless valid layout blockSize do throw (IO.userError "invalid aligned SSTable block size")
    let counter ← IO.mkRef 0
    let next := do
      let row ← nextRow
      if row.isSome then
        let count ← counter.get
        unless physicalSize layout blockSize (count + 1) ≤ maxFileSize do
          throw (IO.userError "aligned SSTable file exceeds offset limit")
        counter.set (count + 1)
      return row
    let writeBlock (bytes : ByteArray) := do
      let padding := ByteArray.mk (Array.replicate (blockSize - bytes.size) 0)
      handle.write (bytes ++ padding)
    let state ← streamRows layout ⟨writeBlock, handle.flush⟩ next IO.userError {} maxFileSize
    if state.pendingRows != 0 then
      writeBlock (encodeBlock layout state.blocks state.pending)
    handle.write (footer layout blockSize state.count)
    handle.flush
    return state.count) syncOutput

def buildFile (path : System.FilePath) (keyWidth valueWidth blockSize : Nat)
    (tableId : UInt64) (nextRow : IO (Option Entry)) : IO Nat :=
  buildFileWithSync path keyWidth valueWidth blockSize tableId nextRow (fun _ => pure ())

def buildFileSynced (path : System.FilePath) (keyWidth valueWidth blockSize : Nat)
    (tableId : UInt64) (nextRow : IO (Option Entry)) : IO Nat :=
  buildFileWithSync path keyWidth valueWidth blockSize tableId nextRow syncFileHandle

/-- Present the original block codec with its logical byte positions.
Each underlying data request reads an entire physical block. Padding has
no logical meaning and is outside the packed block checksum. -/
def openSource (source : Source (EIO String)) :
    EIO String (Layout × Nat × Source (EIO String)) := do
  let size ← source.size
  let footerBytes := Fixed.footerSize + extensionSize
  unless footerBytes ≤ size ∧ size ≤ maxFileSize do throw "invalid aligned SSTable extent"
  let bytes ← source.readAt (size - footerBytes) footerBytes
  unless bytes.size = footerBytes do throw "short aligned SSTable footer"
  let metadata := bytes.extract 0 (footerBytes - 8)
  unless Alvoki.word bytes (footerBytes - 8) = checksum metadata do
    throw "invalid aligned SSTable footer checksum"
  unless bytes.extract Fixed.footerSize (Fixed.footerSize + 8) == marker do
    throw "invalid aligned SSTable format"
  let (layout, count) ← liftDecode (decodeFooter (bytes.extract 0 Fixed.footerSize))
  let blockSize := (Alvoki.word bytes (Fixed.footerSize + 8)).toNat
  unless valid layout blockSize ∧ physicalSize layout blockSize count = size do
    throw "invalid aligned SSTable layout"
  return (layout, count, {
    size := pure (layout.fileSize count)
    readAt := fun offset length => do
      let ordinal := offset / layout.blockSize
      unless offset = layout.blockOffset ordinal ∧ ordinal < layout.blockCount count ∧
          length = layout.blockReadSize count ordinal do
        throw "invalid aligned SSTable block request"
      let block ← source.readAt (ordinal * blockSize) blockSize
      unless block.size = blockSize do throw "short aligned SSTable block"
      return block.extract 0 length })

def openSourceChecked (source : Source (EIO String)) (expectedTableId : UInt64) :
    EIO String (Layout × Nat × Source (EIO String)) := do
  let result ← openSource source
  unless result.1.tableId = expectedTableId do throw "fixed SSTable table ID mismatch"
  return result

end ImmutableSSTable.Fixed.Aligned
