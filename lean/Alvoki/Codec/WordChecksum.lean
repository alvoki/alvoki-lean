import Alvoki.Codec.Block

namespace Alvoki.ByteWords

/-- FNV-1a over the little-endian encoding of consecutive words. -/
def checksumWords (words : List UInt64) : UInt64 :=
  words.foldl (fun hash field =>
    (List.range 8).foldl (fun state lane =>
      (state ^^^ (splitByte field lane).toUInt64) * 1099511628211) hash) 14695981039346656037

end Alvoki.ByteWords
