import PackedRun

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
