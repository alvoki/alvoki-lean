import Std

namespace Alvoki

abbrev Record := UInt64 × UInt64

@[inline] def joinBytes (byte : Nat → UInt64) : UInt64 :=
  byte 0 ||| (byte 1 <<< 8) ||| (byte 2 <<< 16) ||| (byte 3 <<< 24) |||
    (byte 4 <<< 32) ||| (byte 5 <<< 40) ||| (byte 6 <<< 48) ||| (byte 7 <<< 56)

@[inline] def word (bytes : ByteArray) (offset : Nat) : UInt64 :=
  joinBytes fun i => (bytes.get! (offset + i)).toUInt64

@[inline] def wordFast (bytes : ByteArray) (offset : Nat) : UInt64 :=
  if h : offset + 7 < bytes.size then
    let byte := fun (i : Nat) =>
      if hi : i ≤ 7 then (bytes.get (offset + i) (by omega)).toUInt64 else 0
    joinBytes byte
  else word bytes offset

@[inline] def splitByte (value : UInt64) (i : Nat) : UInt8 :=
  (value >>> (8 * i).toUInt64).toUInt8

@[inline] def pushWord (bytes : ByteArray) (value : UInt64) : ByteArray := Id.run do
  let mut out := bytes
  for i in [0:8] do
    out := out.push (splitByte value i)
  return out

@[inline] def pushWordFast (bytes : ByteArray) (value : UInt64) : ByteArray :=
  (bytes.push (splitByte value 0)).push (splitByte value 1)
    |>.push (splitByte value 2) |>.push (splitByte value 3)
    |>.push (splitByte value 4) |>.push (splitByte value 5)
    |>.push (splitByte value 6) |>.push (splitByte value 7)

structure Block where
  private mk ::
  bytes : ByteArray
  count : Nat
  fast : Bool

@[inline] def Block.read (block : Block) (offset : Nat) : UInt64 :=
  if block.fast then wordFast block.bytes offset else word block.bytes offset

@[inline] def Block.key (block : Block) (index : Nat) : UInt64 :=
  block.read (16 + index * 16)

@[inline] def Block.record (block : Block) (index : Nat) : Record :=
  (block.key index, block.read (24 + index * 16))

def parse (bytes : ByteArray) (fast : Bool := false) : Except String Block := do
  if bytes.size < 16 || word bytes 8 != 1 then
    throw "invalid header"
  let payload := bytes.size - 16
  let count := payload / 16
  if payload % 16 != 0 || (word bytes 0).toNat != count then
    throw "invalid length"
  let block := Block.mk bytes count fast
  for index in [1:count] do
    if block.key (index - 1) >= block.key index then
      throw "keys must increase"
  return block

def lowerBound (isLess : Nat → Bool) (lo hi : Nat) : Nat :=
  if lo < hi then
    let mid := lo + (hi - lo) / 2
    if isLess mid then lowerBound isLess (mid + 1) hi
    else lowerBound isLess lo mid
  else lo
termination_by hi - lo
decreasing_by all_goals omega

@[inline] def Block.lowerBound (block : Block) (key : UInt64) : Nat :=
  Alvoki.lowerBound (fun i => block.key i < key) 0 block.count

@[inline] def Block.lookup (block : Block) (key : UInt64) : Option UInt64 :=
  let index := block.lowerBound key
  if index < block.count && block.key index == key then
    some (block.read (24 + index * 16))
  else none

@[inline] def Block.rangeIndices (block : Block) (start stop : UInt64) : Nat × Nat :=
  (block.lowerBound start, block.lowerBound stop)

@[inline] def Block.foldIndices (block : Block) (lo hi : Nat) (init : α)
    (f : α → Record → α) : α := Id.run do
  let mut acc := init
  for i in [lo:min hi block.count] do
    acc := f acc (block.record i)
  return acc

def Block.decode (block : Block) : Array Record := Id.run do
  let mut records := Array.emptyWithCapacity block.count
  for index in [0:block.count] do
    records := records.push (block.record index)
  return records

/-- Encode records whose keys are already strictly increasing. -/
def encode (records : Array Record) (fast : Bool := false) : ByteArray := Id.run do
  let put := if fast then pushWordFast else pushWord
  let mut out := ByteArray.emptyWithCapacity (16 + records.size * 16)
  out := put (put out records.size.toUInt64) 1
  for (key, value) in records do
    out := put (put out key) value
  return out

end Alvoki
