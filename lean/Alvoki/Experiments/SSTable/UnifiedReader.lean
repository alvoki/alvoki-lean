import Alvoki.Experiments.SSTable.UnifiedFormat
import Alvoki.Experiments.SSTable.UnifiedIntegrity

namespace ImmutableSSTable.Unified

/-- The root is loaded and verified once at open; other packets are read only
when needed. The source must remain immutable while the handle is live. -/
structure Handle (m : Type → Type) where private mk ::
  rowCount : Nat
  private source : Source m
  private crc : Checksum
  private layout : Layout
  private root : Array Ref

private def readPacket [Monad m] [MonadExceptOf String m] (source : Source m)
    (crc : Checksum) (tableId kind : UInt64) (offset size endAt : Nat) : m ByteArray := do
  unless checksumSize ≤ size ∧ size ≤ maxRowSize ∧ offset + size ≤ endAt do
    throw "invalid SSTable packet extent"
  let bytes ← source.readAt offset size
  unless bytes.size = size do throw "short SSTable packet read"
  liftDecode (decodePacket crc tableId kind offset bytes)

private def checkChildren (refs : Array Ref) (first count endAt : Nat) : Except String Unit := do
  let mut expected := first
  for ref in refs do
    unless ref.firstRow = expected ∧ ref.offset + ref.size ≤ endAt do
      throw "invalid SSTable child extent"
    expected := expected + ref.count
  unless expected = first + count do throw "invalid SSTable child row count"

def openChecked [Monad m] [MonadExceptOf String m] (source : Source m)
    (crc : Checksum) (expectedId : UInt64) : m (Handle m) := do
  let size ← source.size
  let footerSize := footerBodySize + checksumSize
  unless footerSize ≤ size ∧ size ≤ maxFileSize do throw "invalid SSTable extent"
  let endAt := size - footerSize
  let bytes ← source.readAt endAt footerSize
  unless bytes.size = footerSize do throw "short SSTable footer read"
  let body ← liftDecode (decodePacket crc 0 4 0 bytes)
  let footer ← liftDecode (decodeFooterBody body)
  unless footer.layout.tableId = expectedId do throw "SSTable table ID mismatch"
  if footer.count = 0 then
    unless endAt = 0 do throw "invalid empty SSTable extent"
    return ⟨0, source, crc, footer.layout, #[]⟩
  unless footer.rootOffset + footer.rootSize = endAt do throw "invalid SSTable root extent"
  let raw ← readPacket source crc expectedId 3 footer.rootOffset footer.rootSize endAt
  let root ← liftDecode (decodeIndex raw)
  liftDecode (checkChildren root 0 footer.count footer.rootOffset)
  return ⟨footer.count, source, crc, footer.layout, root⟩

private def findRef (refs : Array Ref) (before : Ref → Bool) : Option Ref :=
  refs[Alvoki.lowerBound (fun i => (refs[i]?).elim false before) 0 refs.size]?

private def Handle.readLeaf [Monad m] [MonadExceptOf String m] (handle : Handle m)
    (parent : Ref) : m (Array Ref) := do
  let raw ← readPacket handle.source handle.crc handle.layout.tableId 2
    parent.offset parent.size maxFileSize
  let refs ← liftDecode (decodeIndex raw)
  liftDecode (checkChildren refs parent.firstRow parent.count parent.offset)
  unless (refs.back?).map Ref.lastKey = some parent.lastKey do
    throw "SSTable index fence mismatch"
  return refs

private def Handle.readData [Monad m] [MonadExceptOf String m] (handle : Handle m)
    (ref : Ref) : m Data := do
  let raw ← readPacket handle.source handle.crc handle.layout.tableId 1
    ref.offset ref.size maxFileSize
  let data ← liftDecode (openData handle.layout ref.count raw)
  let last ← liftDecode (data.readRow (ref.count - 1))
  unless last.key = ref.lastKey do throw "SSTable data fence mismatch"
  return data

private def Handle.locate [Monad m] [MonadExceptOf String m] (handle : Handle m)
    (key : ByteArray) : m (Option (Ref × Data × Nat)) := do
  let before := fun (ref : Ref) => decide (ref.lastKey < key)
  let some parent := findRef handle.root before | return none
  let children ← handle.readLeaf parent
  let some ref := findRef children before | throw "invalid SSTable index fence"
  let data ← handle.readData ref
  let localIndex ← seekBetween (fun i => liftDecode (data.readRow i)) key 0 ref.count
  unless localIndex < ref.count do throw "invalid SSTable data fence"
  return some (ref, data, localIndex)

def Handle.seek [Monad m] [MonadExceptOf String m] (handle : Handle m) (key : ByteArray) : m Nat := do
  match ← handle.locate key with
  | none => return handle.rowCount
  | some (ref, _, index) => return ref.firstRow + index

def Handle.lookup [Monad m] [MonadExceptOf String m] (handle : Handle m)
    (key : ByteArray) : m (Option ByteArray) := do
  let some (_, data, index) ← handle.locate key | return none
  let row ← liftDecode (data.readRow index)
  return if row.key = key then some row.value else none

def Handle.next [Monad m] [MonadExceptOf String m] (handle : Handle m)
    (index : Nat) : m (Option (Entry × Nat)) := do
  if index ≥ handle.rowCount then return none
  let before := fun (ref : Ref) => decide (ref.firstRow + ref.count ≤ index)
  let some parent := findRef handle.root before | throw "invalid SSTable root row range"
  let children ← handle.readLeaf parent
  let some ref := findRef children before | throw "invalid SSTable leaf row range"
  let data ← handle.readData ref
  let row ← liftDecode (data.readRow (index - ref.firstRow))
  return some (row, index + 1)

end ImmutableSSTable.Unified
