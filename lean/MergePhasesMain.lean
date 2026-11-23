import MergePhases

open Alvoki Alvoki.Opt Alvoki.Packed Alvoki.MergePhases

def loadRun (path : String) : IO Run := do
  match parseRun (← IO.FS.readBinFile path) with
  | .ok run => pure run
  | .error message => throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let [mode, leftPath, rightPath, tracePath, output, repetitions] := args
    | throw (IO.userError "expected mode left right trace output repetitions")
  let left ← loadRun leftPath
  let right ← loadRun rightPath
  let trace ← IO.FS.readBinFile tracePath
  if !validateTrace trace left.view.count.toNat right.view.count.toNat then
    throw (IO.userError "invalid replay trace")
  let input ← IO.mkRef (left, right, trace)
  for _ in [0:repetitions.toNat?.getD 1] do
    let (a, b, ops) ← input.get
    let start ← IO.monoNanosNow
    let (bytes, sum) ← match mode with
      | "select" => pure (ByteArray.empty, select a b)
      | "replay-checksum" => pure (ByteArray.empty, replayChecksum a b ops)
      | "replay-write" | "check-replay-write" => pure (replayWrite a b ops, 0)
      | "merge" | "check-merge" => pure (merge a b, 0)
      | _ => throw (IO.userError "unknown mode")
    let elapsed := (← IO.monoNanosNow) - start
    if mode.startsWith "check-" then
      IO.FS.writeBinFile output bytes
    else
      let tag := if bytes.size ≥ 16 then
        word bytes 0 ^^^ word bytes (bytes.size - 8) ^^^ bytes.size.toUInt64 else sum
      IO.println s!"{elapsed} {tag}"
