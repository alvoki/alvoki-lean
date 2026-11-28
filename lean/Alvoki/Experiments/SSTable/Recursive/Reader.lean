import Alvoki.Experiments.SSTable.Recursive.Format
import Alvoki.Experiments.SSTable.UnifiedReader

namespace ImmutableSSTable.Recursive

open Unified (Layout Ref Data Checksum checksumSize decodePacket checkChildren findRef openData)

structure Handle (m : Type → Type) where private mk ::
  rowCount : Nat
  source : Source m
  crc : Checksum
  layout : Layout
  rootOffset : Nat
  height : Nat
  root : Array Ref
  filtered : Bool

def readExact [Monad m] [MonadExceptOf String m] (source : Source m)
    (offset size : Nat) : m ByteArray := do
  let bytes ← source.readAt offset size
  unless bytes.size = size do throw "short SSTable packet read"
  return bytes

def readIndexBytes [Monad m] [MonadExceptOf String m] (source : Source m)
    (ref : Ref) : m ByteArray := do
  if ref.size ≤ maxRowSize then
    readExact source ref.offset ref.size
  else
    let first ← readExact source ref.offset maxRowSize
    let second ← readExact source (ref.offset + maxRowSize) (ref.size - maxRowSize)
    return first ++ second

def readIndexPacket [Monad m] [MonadExceptOf String m] (source : Source m)
    (crc : Checksum) (tableId : UInt64) (height : Nat) (ref : Ref) (endAt : Nat) : m ByteArray := do
  liftDecode (checkedChild ref endAt maxIndexSize)
  let bytes ← readIndexBytes source ref
  liftDecode (decodePacket crc tableId (indexKind height) ref.offset bytes)

def readFooter [Monad m] [MonadExceptOf String m] (source : Source m)
    (crc : Checksum) : m (Footer × Nat) := do
  let size ← source.size
  unless footerPacketSize ≤ size ∧ size ≤ maxFileSize do throw "invalid SSTable extent"
  let endAt := size - footerPacketSize
  let bytes ← readExact source endAt footerPacketSize
  let raw ← liftDecode (decodePacket crc 0 footerKind 0 bytes)
  let footer ← liftDecode (decodeFooter raw)
  return (footer, endAt)

def pageChildren (raw : ByteArray) (parent : Ref) (checkFence : Bool) :
    Except String (Array Ref) := do
  let refs ← decodePage raw
  checkChildren refs parent.firstRow parent.count parent.offset
  if checkFence then
    unless refs.back?.map Ref.lastKey = some parent.lastKey do
      throw "SSTable index fence mismatch"
  return refs

def openChecked [Monad m] [MonadExceptOf String m] (source : Source m)
    (crc : Checksum) (expectedId : UInt64) : m (Handle m) := do
  let (footer, endAt) ← readFooter source crc
  let base := footer.base
  unless base.layout.tableId = expectedId do throw "SSTable table ID mismatch"
  if base.count = 0 then
    unless endAt = 0 do throw "invalid empty SSTable extent"
    return ⟨0, source, crc, base.layout, 0, 0, #[], footer.filtered⟩
  unless base.rootOffset + base.rootSize = endAt do throw "invalid SSTable root extent"
  let ref := footer.rootRef
  let raw ← readIndexPacket source crc expectedId footer.height ref endAt
  let root ← liftDecode (pageChildren raw ref false)
  return ⟨base.count, source, crc, base.layout, ref.offset, footer.height, root, footer.filtered⟩

/-- Follow the selected reference at each level. A successful result retains
the offset of the parent so the data edge can use the same extent check. -/
def descend [Monad m] [MonadExceptOf String m] (source : Source m)
    (crc : Checksum) (tableId : UInt64) (before : Ref → Bool)
    (ref : Ref) (parentOffset : Nat) : Nat → m (Ref × Nat)
  | 0 => return (ref, parentOffset)
  | height + 1 => do
    let raw ← readIndexPacket source crc tableId (height + 1) ref parentOffset
    let children ← liftDecode (pageChildren raw ref true)
    let some child := findRef children before | throw "invalid SSTable child range"
    descend source crc tableId before child ref.offset height

def Handle.readData [Monad m] [MonadExceptOf String m] (handle : Handle m)
    (ref : Ref) (parentOffset : Nat) : m Data := do
  let raw ← Unified.readPacket handle.source handle.crc handle.layout.tableId dataKind
    ref.offset ref.size parentOffset
  let data ← liftDecode (openData handle.layout ref.count raw)
  let last ← liftDecode (data.readRow (ref.count - 1))
  unless last.key = ref.lastKey do throw "SSTable data fence mismatch"
  return data

def Handle.select [Monad m] [MonadExceptOf String m] (handle : Handle m) (before : Ref → Bool)
    (rootChild : Ref) : m (Ref × Data) := do
  let (ref, parentOffset) ← descend handle.source handle.crc handle.layout.tableId before
    rootChild handle.rootOffset (handle.height - 1)
  let data ← handle.readData ref parentOffset
  return (ref, data)

def Handle.locate [Monad m] [MonadExceptOf String m] (handle : Handle m)
    (key : ByteArray) : m (Option (Ref × Data × Nat)) := do
  let before := fun (ref : Ref) => decide (ref.lastKey < key)
  let some rootChild := findRef handle.root before | return none
  let (ref, data) ← handle.select before rootChild
  let index ← seekBetween (fun i => liftDecode (data.readRow i)) key 0 ref.count
  unless index < ref.count do throw "invalid SSTable data fence"
  return some (ref, data, index)

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
  let some rootChild := findRef handle.root before | throw "invalid SSTable root row range"
  let (ref, data) ← handle.select before rootChild
  let row ← liftDecode (data.readRow (index - ref.firstRow))
  return some (row, index + 1)

def Handle.table [Monad m] [MonadExceptOf String m] (handle : Handle m) : Table m :=
  ⟨handle.rowCount, handle.lookup, handle.seek, handle.next⟩

end ImmutableSSTable.Recursive
