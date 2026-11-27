import Alvoki.Compaction.Core

open Alvoki Alvoki.Compaction

private def checked (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let [mode, leftPath, rightPath, floorText, snapshotText, output, trialsText] := args
    | throw (IO.userError "expected mode left right floor snapshot output trials")
  let some floor := floorText.toNat? | throw (IO.userError "invalid floor")
  let some snapshot := snapshotText.toNat? | throw (IO.userError "invalid snapshot")
  let some trials := trialsText.toNat? | throw (IO.userError "invalid trial count")
  if snapshot < floor || snapshot >= 2^64 then throw (IO.userError "invalid snapshot bounds")
  let left ← checked (Compaction.parse (← IO.FS.readBinFile leftPath))
  let right ← checked (Compaction.parse (← IO.FS.readBinFile rightPath))
  let inputs ← IO.mkRef (left, right, floor.toUInt64, snapshot.toUInt64)
  for _ in [0:trials] do
    let (left, right, floor, snapshot) ← inputs.get
    let start ← IO.monoNanosNow
    let (bytes, sum) ← match mode with
      | "rows" | "check-rows" => pure (compact left right floor, 0)
      | "spans" | "check-spans" => pure (compactSpans left right floor, 0)
      | "direct" => pure (ByteArray.empty, Compaction.scan left right snapshot)
      | "pipeline" =>
        let parsed ← checked (Compaction.parse (compactSpans left right floor))
        pure (ByteArray.empty, parsed.scan snapshot)
      | "pipeline-rows" =>
        let parsed ← checked (Compaction.parse (compact left right floor))
        pure (ByteArray.empty, parsed.scan snapshot)
      | _ => throw (IO.userError "invalid compaction mode")
    let elapsed := (← IO.monoNanosNow) - start
    if mode.startsWith "check-" then IO.FS.writeBinFile output bytes
    else
      let tag := if bytes.size >= 16 then
        word bytes 0 ^^^ word bytes (bytes.size - 8) ^^^ bytes.size.toUInt64 else sum
      IO.println s!"{elapsed} {tag}"
