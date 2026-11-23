import FusedMerge

open Alvoki Alvoki.Opt Alvoki.Packed

def parse (bytes : ByteArray) : IO Run :=
  match parseRun bytes with
  | .ok run => pure run
  | .error message => throw (IO.userError message)

def readPacked (bytes : ByteArray) (targets : @& Option Run) : IO UInt64 := do
  let run ← parse bytes
  let mut total := Alvoki.NativeTune.scanScalar run
  if let some query := targets then
    for i in [0:query.view.count.toNat] do
      let key := query.view.value i.toUSize
      let index := run.view.lowerBound key
      if index < run.view.count && run.view.key index == key then
        total := total + run.view.value index
  return total

def main (args : List String) : IO Unit := do
  let [mode, leftPath, rightPath, targetsPath, output, repetitions] := args
    | throw (IO.userError "expected mode left right targets output repetitions")
  let left ← parse (← IO.FS.readBinFile leftPath)
  let right ← parse (← IO.FS.readBinFile rightPath)
  let targets ← if mode.endsWith "-pipeline" then
    some <$> (parse (← IO.FS.readBinFile targetsPath))
  else pure none
  let input ← IO.mkRef (left, right)
  for _ in [0:repetitions.toNat?.getD 1] do
    let (a, b) ← input.get
    let start ← IO.monoNanosNow
    let (bytes, sum) ← match mode with
      | "plain-merge" | "check-plain-merge" => pure (Alvoki.Packed.merge a b, 0)
      | "adaptive-merge" | "check-adaptive-merge" => pure (Alvoki.NativeTune.mergeCached a b 1, 0)
      | "fused-merge" | "check-fused-merge" => pure (Alvoki.FusedMerge.merge a b, 0)
      | "plain-scan" => pure (ByteArray.empty, ← readPacked (Alvoki.Packed.merge a b) none)
      | "adaptive-scan" | "adaptive-pipeline" =>
        pure (ByteArray.empty, ← readPacked (Alvoki.NativeTune.mergeCached a b 1) targets)
      | "fused-scan" | "fused-pipeline" =>
        pure (ByteArray.empty, ← readPacked (Alvoki.FusedMerge.merge a b) targets)
      | "direct-scan" => pure (ByteArray.empty, Alvoki.FusedMerge.scan a b)
      | "selected-scan" => pure (ByteArray.empty, Alvoki.FusedMerge.scanSelected a b)
      | _ => throw (IO.userError "unknown fused merge experiment")
    let elapsed := (← IO.monoNanosNow) - start
    if mode.startsWith "check-" then
      IO.FS.writeBinFile output bytes
    else
      let tag := if bytes.size ≥ 16 then
        word bytes 0 ^^^ word bytes (bytes.size - 8) ^^^ bytes.size.toUInt64 else sum
      IO.println s!"{elapsed} {tag}"
  if (← IO.getEnv "ALVOKI_RSS").isSome then
    let status ← IO.FS.readFile "/proc/self/status"
    let some line := (status.splitOn "\n").find? (·.startsWith "VmHWM:")
      | throw (IO.userError "missing VmHWM")
    IO.println line
