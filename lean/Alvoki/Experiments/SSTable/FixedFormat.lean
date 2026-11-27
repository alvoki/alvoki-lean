import Alvoki.Experiments.SSTable.Core

namespace ImmutableSSTable.Fixed

structure Layout where
  keyWidth : Nat
  valueWidth : Nat
  rowsPerBlock : Nat
  tableId : UInt64
  deriving Repr, DecidableEq

def magic : ByteArray := "ALVSST04".toUTF8

def footerSize : Nat := 56

def Layout.rowWidth (layout : Layout) : Nat := layout.keyWidth + layout.valueWidth

def Layout.blockSize (layout : Layout) : Nat := layout.rowsPerBlock * layout.rowWidth + 8

def Layout.blockOffset (layout : Layout) (block : Nat) : Nat := block * layout.blockSize

def Layout.blockRows (layout : Layout) (rowCount block : Nat) : Nat :=
  min layout.rowsPerBlock (rowCount - block * layout.rowsPerBlock)

def Layout.blockReadSize (layout : Layout) (rowCount block : Nat) : Nat :=
  layout.blockRows rowCount block * layout.rowWidth + 8

def Layout.blockCount (layout : Layout) (rowCount : Nat) : Nat :=
  rowCount / layout.rowsPerBlock + if rowCount % layout.rowsPerBlock = 0 then 0 else 1

def Layout.dataSize (layout : Layout) (rowCount : Nat) : Nat :=
  rowCount * layout.rowWidth + 8 * layout.blockCount rowCount

def Layout.fileSize (layout : Layout) (rowCount : Nat) : Nat :=
  layout.dataSize rowCount + footerSize

def Layout.Valid (layout : Layout) : Prop :=
  0 < layout.rowsPerBlock ∧ layout.rowsPerBlock ≤ maxRowSize ∧ layout.blockSize ≤ maxRowSize

instance (layout : Layout) : Decidable layout.Valid := by
  unfold Layout.Valid
  infer_instance

def Layout.Fits (layout : Layout) (rowCount : Nat) : Prop :=
  layout.Valid ∧ rowCount ≤ maxFileSize ∧ layout.fileSize rowCount ≤ maxFileSize

instance (layout : Layout) (rowCount : Nat) : Decidable (layout.Fits rowCount) := by
  unfold Layout.Fits
  infer_instance

def Layout.RowFits (layout : Layout) (row : Entry) : Prop :=
  row.key.size = layout.keyWidth ∧ row.value.size = layout.valueWidth

instance (layout : Layout) (row : Entry) : Decidable (layout.RowFits row) := by
  unfold Layout.RowFits
  infer_instance

def encodeRow (row : Entry) : ByteArray := row.key ++ row.value

/-- Specification of the bytes accumulated for a block. -/
def encodePayload : List Entry → ByteArray
  | [] => ByteArray.empty
  | row :: rest => encodeRow row ++ encodePayload rest

def readRow (layout : Layout) (payload : ByteArray) (row : Nat) : Entry :=
  let start := row * layout.rowWidth
  ⟨payload.extract start (start + layout.keyWidth),
   payload.extract (start + layout.keyWidth) (start + layout.rowWidth)⟩

private def blockDomain : ByteArray := "ALVBLK04".toUTF8

/-- Bind the payload to its named table and ordinal. The caller chooses the table
identifier. FNV-1a can collide and provides no authentication. -/
def blockChecksum (layout : Layout) (block : Nat) (payload : ByteArray) : UInt64 :=
  let context := Alvoki.pushWordFast (Alvoki.pushWordFast blockDomain layout.tableId) block.toUInt64
  payload.foldl (fun hash byte => (hash ^^^ byte.toUInt64) * 1099511628211) (checksum context)

def encodeBlock (layout : Layout) (block : Nat) (payload : ByteArray) : ByteArray :=
  Alvoki.pushWordFast payload (blockChecksum layout block payload)

def decodeBlock (layout : Layout) (block rows : Nat) (bytes : ByteArray) : Except String ByteArray := do
  let payloadSize := rows * layout.rowWidth
  unless bytes.size = payloadSize + 8 do throw "invalid SSTable block size"
  let payload := bytes.extract 0 payloadSize
  unless Alvoki.word bytes payloadSize = blockChecksum layout block payload do
    throw "invalid SSTable block checksum"
  return payload

private def footerMetadata (layout : Layout) (rowCount : Nat) : ByteArray :=
  let bytes := Alvoki.pushWordFast magic rowCount.toUInt64
  let bytes := Alvoki.pushWordFast bytes layout.keyWidth.toUInt64
  let bytes := Alvoki.pushWordFast bytes layout.valueWidth.toUInt64
  let bytes := Alvoki.pushWordFast bytes layout.rowsPerBlock.toUInt64
  Alvoki.pushWordFast bytes layout.tableId

def encodeFooter (layout : Layout) (rowCount : Nat) : ByteArray :=
  let metadata := footerMetadata layout rowCount
  Alvoki.pushWordFast metadata (checksum metadata)

def decodeFooter (bytes : ByteArray) : Except String (Layout × Nat) := do
  unless bytes.size = footerSize do throw "invalid SSTable fixed footer size"
  unless bytes.extract 0 8 == magic do throw "invalid SSTable fixed format"
  unless Alvoki.word bytes 48 = checksum (bytes.extract 0 48) do
    throw "invalid SSTable fixed footer checksum"
  let layout : Layout :=
    ⟨(Alvoki.word bytes 16).toNat, (Alvoki.word bytes 24).toNat,
      (Alvoki.word bytes 32).toNat, Alvoki.word bytes 40⟩
  let rowCount := (Alvoki.word bytes 8).toNat
  unless layout.Fits rowCount do throw "invalid SSTable fixed layout"
  return (layout, rowCount)

end ImmutableSSTable.Fixed
