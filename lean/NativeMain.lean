import NativeTune

open Alvoki Alvoki.Opt Alvoki.Packed Alvoki.NativeTune

def loadRun (path : String) : IO Run := do
  match parseRun (← IO.FS.readBinFile path) with
  | .ok run => pure run
  | .error message => throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let [mode, input, auxiliary, output, repeats] := args
    | throw (IO.userError "expected mode input auxiliary output repetitions")
  let run ← loadRun input
  let other ← if mode.startsWith "merge" || mode.startsWith "check-merge" then
    loadRun auxiliary else pure run
  let source ← IO.mkRef run
  let second ← IO.mkRef other
  for _ in [0:repeats.toNat?.getD 1] do
    let left ← source.get
    let right ← second.get
    let start ← IO.monoNanosNow
    let (bytes, sum) ← match mode with
      | "scan-original" => pure (ByteArray.empty, left.view.scan 0 left.view.count)
      | "scan-bounded" => pure (ByteArray.empty, scanScalar left)
      | "scan-unrolled" => pure (ByteArray.empty, scanUnrolled left)
      | "merge" | "check-merge" => pure (merge left right, 0)
      | "merge-spans" | "check-merge-spans" => pure (mergeSpans left right, 0)
      | "merge-indexed" | "check-merge-indexed" => pure (mergeIndexed left right, 0)
      | "merge-copy-into" | "check-merge-copy-into" => pure (mergeCopyInto left right, 0)
      | "merge-cached" | "check-merge-cached" => pure (mergeCached left right 0, 0)
      | "merge-adaptive-early" | "check-merge-adaptive-early" => pure (mergeCached left right 1, 0)
      | "merge-adaptive" | "check-merge-adaptive" => pure (mergeCached left right 7, 0)
      | "encode-copy-low" | "check-copy-low" => pure (encodeCopyLow left, 0)
      | "encode-copy-word" | "check-copy-word" => pure (encodeCopyWords left 1, 0)
      | "encode-pair-dense" | "check-pair-dense" => pure (encodePair left 0xfedcba9876543210, 0)
      | "encode-copy-dense" | "check-copy-dense" => pure (encodeCopyWords left 0xfedcba9876543210, 0)
      | "encode-pair" | "check-pair" => pure (encodePair left, 0)
      | "encode-direct" | "check-direct" => pure (encodeDirect left, 0)
      | "encode-staged" | "check-staged" => pure (encodeStaged left, 0)
      | _ => throw (IO.userError "unknown experiment")
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
