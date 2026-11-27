import Alvoki.Experiments.SSTable.Core

namespace ImmutableSSTable.Unified

abbrev Checksum := UInt32 → ByteArray → UInt32

private def crcByte (state : UInt32) (byte : UInt8) : UInt32 :=
  (List.range 8).foldl (fun state _ =>
    (state >>> 1) ^^^ (if state &&& 1 == 1 then 0x82f63b78 else 0))
    (state ^^^ byte.toUInt32)

/-- Portable CRC32C (Castagnoli), with the same incremental convention as
Google crc32c_extend. The incoming and outgoing CRC are complemented. -/
def crc32c (previous : UInt32) (bytes : ByteArray) : UInt32 :=
  (bytes.foldl crcByte (previous ^^^ 0xffffffff)) ^^^ 0xffffffff

def checksumSize : Nat := 4

private def packetCRC (crc : Checksum) (tableId kind : UInt64) (offset : Nat)
    (bytes : ByteArray) : UInt32 :=
  let context := Alvoki.pushWordFast (Alvoki.pushWordFast
    (Alvoki.pushWordFast "ALVCRC05".toUTF8 kind) tableId) offset.toUInt64
  crc (crc 0 context) bytes

def encodePacket (crc : Checksum) (tableId kind : UInt64) (offset : Nat) (bytes : ByteArray) : ByteArray :=
  let word := encodeOffset (packetCRC crc tableId kind offset bytes).toNat
  bytes ++ word.extract 0 checksumSize

def decodePacket (crc : Checksum) (tableId kind : UInt64) (offset : Nat) (bytes : ByteArray) :
    Except String ByteArray := do
  unless checksumSize ≤ bytes.size do throw "short SSTable packet"
  let stop := bytes.size - checksumSize
  let payload := bytes.extract 0 stop
  let word := encodeOffset (packetCRC crc tableId kind offset payload).toNat
  unless bytes.extract stop bytes.size == word.extract 0 checksumSize do
    throw "SSTable CRC32C mismatch"
  return payload

end ImmutableSSTable.Unified
