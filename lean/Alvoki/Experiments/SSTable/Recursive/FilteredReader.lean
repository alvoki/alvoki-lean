import Alvoki.Experiments.SSTable.Recursive.Native

namespace ImmutableSSTable.Recursive

open Unified (Ref Checksum findRef)

/-- In a filtered image each qualifying data reference has a mask immediately
before it. Its extent is derived from the count in the checked reference. -/
def readFilter [Monad m] [MonadExceptOf String m] (source : Source m)
    (crc : Checksum) (tableId : UInt64) (ref : Ref) : m ByteArray := do
  let size := filterPacketSize ref.count
  unless size ≤ ref.offset do throw "invalid SSTable filter extent"
  Unified.readPacket source crc tableId filterKind (ref.offset - size) size ref.offset

def Handle.lookupInData [Monad m] [MonadExceptOf String m] (handle : Handle m)
    (ref : Ref) (parentOffset : Nat) (key : ByteArray) : m (Option ByteArray) := do
  let data ← handle.readData ref parentOffset
  let index ← seekBetween (fun i => liftDecode (data.readRow i)) key 0 ref.count
  unless index < ref.count do throw "invalid SSTable data fence"
  let row ← liftDecode (data.readRow index)
  return if row.key = key then some row.value else none

def Handle.checkFilter [Monad m] [MonadExceptOf String m] (handle : Handle m)
    (ref : Ref) (key : ByteArray) : m Bool := do
  if useFilter ref.count then
    return Bloom.mayContain (← readFilter handle.source handle.crc handle.layout.tableId ref) key
  else
    return true

def Handle.filteredLookup [Monad m] [MonadExceptOf String m] (handle : Handle m)
    (key : ByteArray) : m (Option ByteArray) := do
  if !handle.filtered then return ← handle.lookup key
  let before := fun (ref : Ref) => decide (ref.lastKey < key)
  let some rootChild := findRef handle.root before | return none
  let (ref, parentOffset) ← descend handle.source handle.crc handle.layout.tableId before
    rootChild handle.rootOffset (handle.height - 1)
  if ← handle.checkFilter ref key then
    handle.lookupInData ref parentOffset key
  else
    return none

def Handle.filteredTable [Monad m] [MonadExceptOf String m] (handle : Handle m) : Table m :=
  { handle.table with lookup := handle.filteredLookup }

def openNativeFiltered (path : System.FilePath) (expectedId : UInt64) :
    EIO String (Table (EIO String)) := do
  return (← openCheckedWith nativeReadPrimitives Alvoki.CRC32C.extend path expectedId).filteredTable

end ImmutableSSTable.Recursive
