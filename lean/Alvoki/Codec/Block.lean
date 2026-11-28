import Std

namespace Alvoki

@[inline] def joinBytes (byte : Nat → UInt64) : UInt64 :=
  byte 0 ||| (byte 1 <<< 8) ||| (byte 2 <<< 16) ||| (byte 3 <<< 24) |||
    (byte 4 <<< 32) ||| (byte 5 <<< 40) ||| (byte 6 <<< 48) ||| (byte 7 <<< 56)

@[inline] def word (bytes : ByteArray) (offset : Nat) : UInt64 :=
  joinBytes fun i => (bytes.get! (offset + i)).toUInt64

@[inline] def splitByte (value : UInt64) (i : Nat) : UInt8 :=
  (value >>> (8 * i).toUInt64).toUInt8

@[inline] def pushWordFast (bytes : ByteArray) (value : UInt64) : ByteArray :=
  (bytes.push (splitByte value 0)).push (splitByte value 1)
    |>.push (splitByte value 2) |>.push (splitByte value 3)
    |>.push (splitByte value 4) |>.push (splitByte value 5)
    |>.push (splitByte value 6) |>.push (splitByte value 7)

def lowerBound (isLess : Nat → Bool) (lo hi : Nat) : Nat :=
  if lo < hi then
    let mid := lo + (hi - lo) / 2
    if isLess mid then lowerBound isLess (mid + 1) hi
    else lowerBound isLess lo mid
  else lo
termination_by hi - lo
decreasing_by all_goals omega

end Alvoki
