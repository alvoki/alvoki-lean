import BlockCodec

open Alvoki Alvoki.Packed

def main : IO Unit := do
  let .ok run := parseRun (encode #[(10, 100), (20, 200)] true)
    | throw (IO.userError "could not parse version-1 index fixture")
  unless run.record? 0 == some (10, 100) && run.record? run.count.toNat == none &&
      run.record? (USize.size / 16) == none && run.record? USize.size == none &&
      run.lookup 20 == some 200 &&
      run.lookup 11 == none && run.rangeChecksum 10 20 == (10 ^^^ 100) &&
      run.rangeChecksum 20 10 == 0 do
    throw (IO.userError "packed run API returned an incorrect record or range")
  IO.println "Passed packed run API checks, including out-of-range and wrapping indices."
  let maxWord := UInt64.ofNat (2^64 - 1)
  let fixtures : Array (Array Record) := #[#[], #[(0, 0)], #[(0, 1), (10, 100), (maxWord, maxWord)]]
  for rows in fixtures do
    let bytes := encodeV1 rows
    let .ok run := parseRun bytes | throw (IO.userError "v1 codec rejected its output")
    unless bytes == Alvoki.encode rows true && run.decodeV1 == rows do
      throw (IO.userError "v1 codec round trip changed the records")
  let wrappingIndex := USize.ofNat (USize.size / 16)
  unless run.view.keyOrZero wrappingIndex == 0 && run.view.valueOrZero wrappingIndex == 0 do
    throw (IO.userError "packed kernel accessor wrapped an invalid index")
  IO.println "Passed exact v1 codec and bounded kernel accessor checks."
