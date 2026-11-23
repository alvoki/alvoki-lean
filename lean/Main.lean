import Block

open Alvoki

def load (bytes : ByteArray) (fast : Bool) : IO Block :=
  match parse bytes fast with
  | .ok block => pure block
  | .error message => throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let [mode, input, query, param, reps] := args
    | throw (IO.userError "expected mode input queries parameter repetitions")
  let fast := (← IO.getEnv "ALVOKI_FAST") == some "1"
  let bytes ← IO.FS.readBinFile input
  let block ← load bytes fast
  if mode == "check" then
    IO.FS.writeBinFile param (encode block.decode fast)
  let queries := (← load (← IO.FS.readBinFile query) fast).decode
  let records := if mode == "encode" then block.decode else #[]
  let width := param.toNat?.getD 8 |>.toUInt64
  for _ in [0:reps.toNat?.getD 1] do
    let start ← IO.monoNanosNow
    let mut sum : UInt64 := 0
    match mode with
    | "encode" => sum := (encode records fast).size.toUInt64
    | "decode" => sum := block.decode.size.toUInt64
    | "load" => sum := (← load (← IO.FS.readBinFile input) fast).count.toUInt64
    | "validate" => sum := (← load bytes fast).count.toUInt64
    | "point" =>
      for (_, key) in queries do
        sum := sum + (block.lookup key).getD 0
    | "range" | "check" =>
      for (_, key) in queries do
        let stop := if key > UInt64.ofNat (2^64 - 1) - width then UInt64.ofNat (2^64 - 1) else key + width
        let (lo, hi) := block.rangeIndices key stop
        let scan := block.foldIndices lo hi (0 : UInt64) fun acc (k, v) => acc + (k ^^^ v)
        if mode == "check" then
          let value := (block.lookup key).map toString |>.getD "-"
          IO.println s!"{value} {lo} {hi} {scan}"
        sum := sum + scan
    | _ => throw (IO.userError "unknown mode")
    let elapsed := (← IO.monoNanosNow) - start
    if mode != "check" then
      IO.println s!"{elapsed} {sum}"
  if (← IO.getEnv "ALVOKI_RSS").isSome then
    let status ← IO.FS.readFile "/proc/self/status"
    let some rss := (status.splitOn "\n").find? (·.startsWith "VmHWM:")
      | throw (IO.userError "missing VmHWM")
    IO.println rss
