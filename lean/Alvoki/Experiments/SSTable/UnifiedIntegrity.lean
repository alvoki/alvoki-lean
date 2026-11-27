import Alvoki.Experiments.SSTable.Core
import Alvoki.Codec.CRC32C

namespace ImmutableSSTable.Unified

abbrev Checksum := UInt32 → ByteArray → UInt32

abbrev crc32c := Alvoki.CRC32C.crc32c

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
