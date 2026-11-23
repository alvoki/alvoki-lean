import MergePhases
import NativeTune

open Alvoki Alvoki.Opt Alvoki.Packed Alvoki.MergePhases

def loadRun (path : String) : IO Run := do
  match parseRun (← IO.FS.readBinFile path) with
  | .ok run => pure run
  | .error message => throw (IO.userError message)

def pipeline (left right targets : @& Run) : IO UInt64 := do
  let bytes := merge left right
  let output ← match parseRun bytes with
    | .ok run => pure run
    | .error message => throw (IO.userError message)
  let mut total := Alvoki.NativeTune.scanScalar output
  for i in [0:targets.view.count.toNat] do
    let key := targets.view.valueUnchecked i.toUSize
    let index := output.view.lowerBound key
    if index < output.view.count && output.view.keyUnchecked index == key then
      total := total + output.view.valueUnchecked index
  return total

def buildSlices (plan : @& ReplayPlan) : IO PreparedReplay :=
  match plan.prepare with
  | .ok slices => pure slices
  | .error message => throw (IO.userError message)

def main (args : List String) : IO Unit := do
  if args == ["copy-contract"] then
    checkCopyContract
    return
  let [mode, leftPath, rightPath, tracePath, output, repetitions] := args
    | throw (IO.userError "expected mode left right trace output repetitions")
  let left ← loadRun leftPath
  let right ← loadRun rightPath
  let operation := if mode.startsWith "check-" then String.ofList (mode.toList.drop 6) else mode
  let width : Nat := match operation with
    | "copy16" => 16
    | "copy32" => 32
    | "copy64" => 64
    | "copy4096" => 4096
    | _ => 0
  let preparedMode := operation == "replay-prepared"
  let needsTrace := operation.startsWith "replay-"
  let trace ← if needsTrace || width != 0 then IO.FS.readBinFile tracePath else pure ByteArray.empty
  let plan ← if needsTrace then
    match checkReplayPlan left right trace with
    | .ok checked => pure (some checked)
    | .error message => throw (IO.userError message)
  else pure none
  let replayInput ← IO.mkRef plan
  let preparedSlices ← if preparedMode then
    let some checked := plan | throw (IO.userError "expected checked trace")
    some <$> buildSlices checked
  else pure none
  let preparedInput ← IO.mkRef preparedSlices
  let targets ← if mode == "pipeline" then some <$> loadRun tracePath else pure none
  let total := left.view.count.toNat + right.view.count.toNat
  if width != 0 && !validateGroups trace left.count.toNat right.count.toNat (width / 16) then
    throw (IO.userError "invalid replay trace")
  let input ← IO.mkRef (left, right, trace)
  for _ in [0:repetitions.toNat?.getD 1] do
    let (a, b, ops) ← input.get
    let prepared ← IO.mkRef (if width == 0 then ByteArray.empty else zeroedBytes (16 + total * 16))
    let destination ← prepared.swap ByteArray.empty
    let start ← IO.monoNanosNow
    let (bytes, sum) ← match mode with
      | "pipeline" =>
        let some query := targets | throw (IO.userError "expected query block")
        pure (ByteArray.empty, ← pipeline a b query)
      | "select" => pure (ByteArray.empty, select a b)
      | "replay-checksum" => pure (ByteArray.empty, replayChecksum a b ops)
      | "replay-write" | "check-replay-write" =>
        let some checked ← replayInput.get | throw (IO.userError "expected checked trace")
        pure (checked.write, 0)
      | "replay-prepared" | "check-replay-prepared" =>
        let some ready ← preparedInput.get | throw (IO.userError "expected prepared replay")
        pure (ready.write, 0)
      | "replay-spans" | "check-replay-spans" =>
        let some checked ← replayInput.get | throw (IO.userError "expected checked trace")
        pure (checked.writeSpans, 0)
      | "replay-prepare-and-write" | "check-replay-prepare-and-write" =>
        let some checked ← replayInput.get | throw (IO.userError "expected checked trace")
        pure ((← buildSlices checked).write, 0)
      | "dense" | "check-dense" => pure (denseRewrite a, 0)
      | "merge" | "check-merge" => pure (merge a b, 0)
      | _ =>
        if width == 0 then throw (IO.userError "unknown mode")
        else pure (copyGroups a b ops width.toUSize destination, 0)
    let elapsed := (← IO.monoNanosNow) - start
    if mode.startsWith "check-" then
      IO.FS.writeBinFile output bytes
    else
      let tag := if bytes.size ≥ 16 then
        word bytes 0 ^^^ word bytes (bytes.size - 8) ^^^ bytes.size.toUInt64 else sum
      IO.println s!"{elapsed} {tag}"
