import Alvoki.Experiments.Packed.Optimizations
import Alvoki.Codec.PackedRun

namespace Alvoki.Packed
open Alvoki.Opt

/-- Replace the sixteen bytes at offset by two little-endian words.
    Preserve the buffer and its length on an out-of-bounds request. -/
def writePair (bytes : ByteArray) (offset : USize) (key value : UInt64) : ByteArray := Id.run do
  let start := offset.toNat
  if start + 16 > bytes.size then return bytes
  let mut out := bytes
  for i in [0:8] do out := out.set! (start + i) (splitByte key i)
  for i in [0:8] do out := out.set! (start + 8 + i) (splitByte value i)
  return out

/-- C implementation of the writePair contract. The runtime is trusted to honor copy-on-write. -/
@[extern "alvoki_write_pair"] def writePairC (bytes : ByteArray) (offset : USize)
    (key value : UInt64) : ByteArray :=
  writePair bytes offset key value

@[extern "alvoki_zero_bytes"] def zeroBytesC (size : USize) : ByteArray :=
  zeroedBytes size.toNat

@[specialize] def fill (write : ByteArray → USize → UInt64 → UInt64 → ByteArray)
    (records : @& Array ScalarRecord) (into : ByteArray) : ByteArray := Id.run do
  let mut out := write into 0 records.size.toUInt64 1
  let mut offset : USize := 16
  for record in records do
    out := write out offset record.key record.value
    offset := offset + 16
  return out

/-- Fill exactly one version-1 buffer in a single call. A wrong-sized buffer is unchanged. -/
@[extern "alvoki_fill_batch"] def fillBatchC (into : ByteArray) (records : @& Array ScalarRecord) :
    ByteArray :=
  if into.size == 16 + 16 * records.size then fill writePair records into else into

@[extern "alvoki_encode_batch"] def encodeBatchC (records : @& Array ScalarRecord) : ByteArray :=
  encodeScalar records

structure Chunks where
  private mk ::
  parts : Array ByteArray
  count : Nat

/-- 256 records per chunk, or 4 KiB. The final chunk may be short. -/
def chunked (run : @& Run) : Chunks := Id.run do
  let view := run.view
  let count := view.count.toNat
  let mut parts := Array.emptyWithCapacity ((count + 255) / 256)
  for base in [0:count:256] do
    parts := parts.push (view.bytes.extract (16 + base * 16) (16 + min (base + 256) count * 16))
  return ⟨parts, count⟩

@[inline] def Chunks.key (chunks : @& Chunks) (index : Nat) : UInt64 :=
  wordMachine chunks.parts[index / 256]! ((index % 256 * 16).toUSize)

@[inline] def Chunks.value (chunks : @& Chunks) (index : Nat) : UInt64 :=
  wordMachine chunks.parts[index / 256]! ((index % 256 * 16 + 8).toUSize)

def Chunks.lookup (chunks : @& Chunks) (key : UInt64) : Option UInt64 :=
  let i := searchMachine (fun i => chunks.key i.toNat) key chunks.count.toUSize
  if i.toNat < chunks.count && chunks.key i.toNat == key then some (chunks.value i.toNat)
  else none

/-- Find the last chunk whose first key is at most the target, then search within that chunk. -/
def Chunks.lookupWithin (chunks : @& Chunks) (key : UInt64) : Option UInt64 := do
  let count := chunks.parts.size.toUSize
  if count == 0 then none else
    let boundary := searchMachine
      (fun i => wordMachine chunks.parts[i.toNat]! 0) key count
    let index := if boundary < count &&
        wordMachine chunks.parts[boundary.toNat]! 0 == key then boundary
      else if boundary == 0 then 0 else boundary - 1
    let part := chunks.parts[index.toNat]!
    let limit := part.usize / 16
    let position := searchMachine (fun i => wordMachine part (16 * i)) key limit
    if position < limit && wordMachine part (16 * position) == key then
      some (wordMachine part (16 * position + 8))
    else none

private def scanPart (bytes : @& ByteArray) (offset count : USize) (sum : UInt64) : UInt64 :=
  if _h : offset < count then
    scanPart bytes (offset + 1) count
      (sum + (wordMachine bytes (offset * 16) ^^^ wordMachine bytes (offset * 16 + 8)))
  else sum
termination_by count.toNat - offset.toNat
decreasing_by
  have order := USize.lt_iff_toNat_lt.mp _h
  have next := addOne offset count order
  omega

def foldInterleaved (bytes : @& ByteArray) (start count : USize) : UInt64 :=
  scanPart bytes start count 0

def Chunks.fold (chunks : @& Chunks) : UInt64 := Id.run do
  let mut sum := 0
  for bytes in chunks.parts do
    sum := scanPart bytes 0 (bytes.usize / 16) sum
  return sum

end Alvoki.Packed
