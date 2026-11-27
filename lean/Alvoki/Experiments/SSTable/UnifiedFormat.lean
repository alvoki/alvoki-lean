import Alvoki.Experiments.SSTable.Core

namespace ImmutableSSTable.Unified

structure Layout where
  keyWidth : Option Nat
  valueWidth : Option Nat
  tableId : UInt64
  deriving DecidableEq, Repr

def Layout.Valid (layout : Layout) : Prop :=
  layout.keyWidth.getD 0 + layout.valueWidth.getD 0 ≤ maxRowSize

instance (layout : Layout) : Decidable layout.Valid := by
  unfold Layout.Valid
  infer_instance

def Layout.hasOffsets (layout : Layout) : Bool :=
  layout.keyWidth.isNone || layout.valueWidth.isNone

def Layout.keyLengthSize (layout : Layout) : Nat :=
  if layout.keyWidth.isNone && layout.valueWidth.isNone then 8 else 0

def rowFits (layout : Layout) (row : Entry) : Bool :=
  layout.keyWidth.all (· == row.key.size) && layout.valueWidth.all (· == row.value.size)

def entrySize (layout : Layout) (row : Entry) : Nat :=
  layout.keyLengthSize + row.key.size + row.value.size

def appendEntry (layout : Layout) (output : ByteArray) (row : Entry) : ByteArray :=
  let output :=
    if layout.keyLengthSize = 0 then output
    else Alvoki.pushWordFast output row.key.size.toUInt64
  output ++ row.key ++ row.value

def entryBytes (layout : Layout) (row : Entry) : ByteArray :=
  appendEntry layout ByteArray.empty row

/-- Offsets, when needed, are relative to the start of the payload. The final
offset is the payload extent. Empty row spans are allowed. -/
def encodeData (layout : Layout) (rows : Array Entry) : ByteArray := Id.run do
  let hasOffsets := layout.hasOffsets
  let mut payload := ByteArray.empty
  let mut offsets := ByteArray.empty
  for row in rows do
    if hasOffsets then
      offsets := Alvoki.pushWordFast offsets payload.size.toUInt64
    payload := appendEntry layout payload row
  if hasOffsets then
    return payload ++ Alvoki.pushWordFast offsets payload.size.toUInt64
  return payload

structure Data where private mk ::
  private layout : Layout
  count : Nat
  private payloadSize : Nat
  private bytes : ByteArray

/-- Check the data extent and offset endpoints. Indexed reads validate the
specific pair of adjacent offsets they consume. -/
def openData (layout : Layout) (count : Nat) (bytes : ByteArray) : Except String Data := do
  unless layout.Valid ∧ 0 < count ∧ count ≤ maxFileSize ∧ bytes.size ≤ maxRowSize do
    throw "invalid SSTable data layout"
  if layout.hasOffsets then
    let offsetsSize := 8 * (count + 1)
    unless offsetsSize ≤ bytes.size do throw "invalid SSTable data offset extent"
    let payloadSize := bytes.size - offsetsSize
    unless Alvoki.word bytes payloadSize = 0 ∧
        (Alvoki.word bytes (bytes.size - 8)).toNat = payloadSize do
      throw "invalid SSTable data offset endpoints"
    return ⟨layout, count, payloadSize, bytes⟩
  else
    let rowSize := layout.keyWidth.getD 0 + layout.valueWidth.getD 0
    unless bytes.size = count * rowSize do throw "invalid SSTable fixed data extent"
    return ⟨layout, count, bytes.size, bytes⟩

def Data.rowSpan (data : Data) (i : Nat) : Except String (Nat × Nat) := do
  unless i < data.count do throw "SSTable block cursor out of bounds"
  if data.layout.hasOffsets then
    let left := data.payloadSize + 8 * i
    let start := (Alvoki.word data.bytes left).toNat
    let stop := (Alvoki.word data.bytes (left + 8)).toNat
    unless start ≤ stop ∧ stop ≤ data.payloadSize do throw "invalid SSTable data row span"
    return (start, stop)
  else
    let rowSize := data.layout.keyWidth.getD 0 + data.layout.valueWidth.getD 0
    return (i * rowSize, (i + 1) * rowSize)

/-- Split the fields within a previously checked row span. -/
@[inline] def readRowInSpan (layout : Layout) (bytes : ByteArray) (start stop : Nat) :
    Except String Entry := do
  let (keyStart, keyStop) ← match layout.keyWidth, layout.valueWidth with
    | some width, _ => do
      unless width ≤ stop - start do throw "invalid SSTable data key width"
      pure (start, start + width)
    | none, some width => do
      unless width ≤ stop - start do throw "invalid SSTable data value width"
      pure (start, stop - width)
    | none, none => do
      let keyStart := start + 8
      unless keyStart ≤ stop do throw "invalid SSTable data key length field"
      let width := (Alvoki.word bytes start).toNat
      unless width ≤ stop - keyStart do throw "invalid SSTable data key length"
      pure (keyStart, keyStart + width)
  return ⟨bytes.extract keyStart keyStop, bytes.extract keyStop stop⟩

/-- Read a row from the data region at its layout-dependent boundaries. -/
def Data.readRow (data : Data) (i : Nat) : Except String Entry := do
  let (start, stop) ← data.rowSpan i
  readRowInSpan data.layout data.bytes start stop

structure Ref where
  lastKey : ByteArray
  offset : Nat
  size : Nat
  firstRow : Nat
  count : Nat
  deriving DecidableEq

def refPrefixSize : Nat := 40

def indexEntrySize (lastKey : ByteArray) : Nat := refPrefixSize + lastKey.size

def appendRef (output : ByteArray) (ref : Ref) : ByteArray :=
  let output := Alvoki.pushWordFast output ref.offset.toUInt64
  let output := Alvoki.pushWordFast output ref.size.toUInt64
  let output := Alvoki.pushWordFast output ref.firstRow.toUInt64
  let output := Alvoki.pushWordFast output ref.count.toUInt64
  let output := Alvoki.pushWordFast output ref.lastKey.size.toUInt64
  output ++ ref.lastKey

def encodeIndex (refs : Array Ref) : ByteArray :=
  refs.foldl appendRef ByteArray.empty

/-- Decode the remaining references from the byte position, extending `refs`. -/
def decodeRefs (bytes : ByteArray) (atByte : Nat) (refs : Array Ref) :
    Nat → Except String (Array Ref)
  | 0 =>
    if atByte = bytes.size then .ok refs else .error "short SSTable index reference"
  | fuel + 1 => do
    if atByte = bytes.size then return refs
    let keyStart := atByte + refPrefixSize
    unless keyStart ≤ bytes.size do throw "short SSTable index reference"
    let offset := (Alvoki.word bytes atByte).toNat
    let size := (Alvoki.word bytes (atByte + 8)).toNat
    let firstRow := (Alvoki.word bytes (atByte + 16)).toNat
    let count := (Alvoki.word bytes (atByte + 24)).toNat
    let keySize := (Alvoki.word bytes (atByte + 32)).toNat
    unless 0 < size ∧ offset + size ≤ maxFileSize ∧
        0 < count ∧ firstRow + count ≤ maxFileSize ∧ keySize ≤ bytes.size - keyStart do
      throw "invalid SSTable index reference"
    let keyEnd := keyStart + keySize
    let lastKey := bytes.extract keyStart keyEnd
    if let some prev := refs.back? then
      unless prev.lastKey < lastKey ∧ prev.firstRow + prev.count = firstRow ∧
          prev.offset + prev.size ≤ offset do
        throw "invalid SSTable index reference order"
    decodeRefs bytes keyEnd (refs.push ⟨lastKey, offset, size, firstRow, count⟩) fuel

/-- Validate reference framing, row coverage and ordering within one index.
The reader checks that each child is contained in the corresponding file section. -/
def decodeIndex (bytes : ByteArray) : Except String (Array Ref) := do
  unless refPrefixSize ≤ bytes.size ∧ bytes.size ≤ maxRowSize do
    throw "invalid SSTable index size"
  decodeRefs bytes 0 #[] (bytes.size / refPrefixSize)

structure Footer where
  layout : Layout
  count : Nat
  rootOffset : Nat
  rootSize : Nat
  deriving DecidableEq, Repr

def magic : ByteArray := "ALVSST05".toUTF8

def footerBodySize : Nat := 56

def variableWidth : UInt64 := 0xffffffffffffffff

def encodeWidth (width : Option Nat) : UInt64 :=
  width.map Nat.toUInt64 |>.getD variableWidth

def decodeWidth (width : UInt64) : Option Nat :=
  if width = variableWidth then none else some width.toNat

def encodeFooterBody (footer : Footer) : ByteArray :=
  let bytes := Alvoki.pushWordFast magic (encodeWidth footer.layout.keyWidth)
  let bytes := Alvoki.pushWordFast bytes (encodeWidth footer.layout.valueWidth)
  let bytes := Alvoki.pushWordFast bytes footer.layout.tableId
  let bytes := Alvoki.pushWordFast bytes footer.count.toUInt64
  let bytes := Alvoki.pushWordFast bytes footer.rootOffset.toUInt64
  Alvoki.pushWordFast bytes footer.rootSize.toUInt64

/-- The empty table consists of the framed footer alone. Root extents are
checked against the actual file by the reader. -/
def decodeFooterBody (bytes : ByteArray) : Except String Footer := do
  unless bytes.size = footerBodySize do throw "invalid SSTable footer body size"
  unless bytes.extract 0 8 == magic do throw "invalid SSTable format"
  let layout := ⟨decodeWidth (Alvoki.word bytes 8), decodeWidth (Alvoki.word bytes 16),
    Alvoki.word bytes 24⟩
  let count := (Alvoki.word bytes 32).toNat
  let rootOffset := (Alvoki.word bytes 40).toNat
  let rootSize := (Alvoki.word bytes 48).toNat
  unless layout.Valid ∧ count ≤ maxFileSize ∧ rootOffset + rootSize + footerBodySize ≤ maxFileSize do
    throw "invalid SSTable footer bounds"
  if count = 0 then
    unless rootOffset = 0 ∧ rootSize = 0 do throw "invalid SSTable empty root"
  else
    unless 0 < rootSize do throw "invalid SSTable root size"
  return ⟨layout, count, rootOffset, rootSize⟩

end ImmutableSSTable.Unified
