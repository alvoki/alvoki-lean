import Init.Data.Array.Lemmas
import Init.Data.UInt.Lemmas

namespace Alvoki.CRC32C

private def crcByte (state : UInt32) (byte : UInt8) : UInt32 :=
  (List.range 8).foldl (fun state _ =>
    (state >>> 1) ^^^ (if state &&& 1 == 1 then 0x82f63b78 else 0))
    (state ^^^ byte.toUInt32)

/-- Portable CRC32C (Castagnoli), with the same incremental convention as
Google crc32c_extend. The incoming and outgoing CRC are complemented. -/
def crc32c (previous : UInt32) (bytes : ByteArray) : UInt32 :=
  (bytes.data.foldl crcByte (previous ^^^ 0xffffffff)) ^^^ 0xffffffff

/-- Native calls borrow the array. The linked implementation must agree with `crc32c`. -/
@[extern "alvoki_crc32c_extend"]
def extend (previous : UInt32) (bytes : @& ByteArray) : UInt32 :=
  crc32c previous bytes

@[simp] theorem extend_empty (seed : UInt32) : extend seed ByteArray.empty = seed := by
  change (#[] : Array UInt8).foldl crcByte (seed ^^^ 0xffffffff) ^^^ 0xffffffff = seed
  simp [UInt32.xor_assoc]

theorem extend_append (seed : UInt32) (a b : ByteArray) :
    extend (extend seed a) b = extend seed (a ++ b) := by
  simp [extend, crc32c, ByteArray.data_append, UInt32.xor_assoc]

end Alvoki.CRC32C
