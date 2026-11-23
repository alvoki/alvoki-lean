import Optimizations

open Alvoki Alvoki.Opt

def require (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

def consumePair (records : @& Array Record) : UInt64 := Id.run do
  let mut sum := 0
  for (key, value) in records do sum := sum + (key ^^^ value)
  return sum

def consumeScalar (records : @& Array ScalarRecord) : UInt64 := Id.run do
  let mut sum := 0
  for record in records do sum := sum + (record.key ^^^ record.value)
  return sum

@[specialize] def readBatch (bytes : @& ByteArray) (count : Nat)
    (reader : ByteArray → Nat → UInt64) : UInt64 := Id.run do
  let mut sum := 0
  for i in [0:count] do sum := sum + reader bytes (17 + i * 16)
  return sum

@[specialize] def pointBatch (block : @& Block) (targets : @& Array Record)
    (bound : Nat → UInt64 → Nat) : UInt64 := Id.run do
  let mut sum := 0
  for (_, target) in targets do
    let index := bound block.count target
    if index < block.count && block.key index == target then
      sum := sum + block.read (24 + index * 16)
  return sum

def main (args : List String) : IO Unit := do
  let [mode, input, query, param, reps] := args
    | throw (IO.userError "expected experiment input queries width repetitions")
  let bytes ← IO.FS.readBinFile input
  let view ← require (parseView bytes)
  let source ← IO.mkRef bytes
  let targets := (← require (parse (← IO.FS.readBinFile query))).decode
  let block ← if ["point-base", "point-nat", "point-usize", "validate-base", "validate-carry",
      "decode-pair", "decode-scalar", "decode-stream", "write-loop", "write-unrolled"].contains mode then
      some <$> require (parse bytes)
    else pure none
  let width := param.toNat?.getD 8 |>.toUInt64
  let records := if mode == "write-loop" || mode == "write-unrolled" then block.map Block.decode |>.getD #[] else #[]
  let scalars := if ["write-scalar", "write-indexed", "check-write", "check-indexed"].contains mode then view.decode else #[]
  if mode == "check-write" || mode == "check-indexed" then
    IO.FS.writeBinFile param (if mode == "check-write" then encodeScalar scalars else encodeIndexed scalars)
    return
  for _ in [0:reps.toNat?.getD 1] do
    let start ← IO.monoNanosNow
    let result ← match mode, block with
      | "point-base", some b => pure (pointBatch b targets (fun _ k => b.lowerBound k))
      | "point-nat", some b => pure (pointBatch b targets (fun n k => searchNat b k 0 n))
      | "point-usize", some b =>
        pure (pointBatch b targets (fun n k => (searchMachine (fun i => b.key i.toNat) k n.toUSize).toNat))
      | "validate-base", some _ => (·.count.toUInt64) <$> require (parse bytes)
      | "validate-carry", some b =>
        if validateCarry b then pure b.count.toUInt64 else throw (IO.userError "invalid order")
      | "validate-machine", _ => (·.count.toUInt64) <$> require (parseView (← source.get))
      | "decode-pair", some b => pure (consumePair b.decode)
      | "decode-scalar", some b => pure (consumeScalar (decodeScalar b))
      | "decode-machine", _ => pure (consumeScalar view.decode)
      | "decode-stream", some b => pure (decodeFold b)
      | "stream-machine", _ => pure (view.scan 0 view.count)
      | "point-machine", _ => do
        let mut sum : UInt64 := 0
        for (_, key) in targets do
          let index := view.lowerBound key
          if index < view.count && view.keyOrZero index == key then sum := sum + view.valueOrZero index
        pure sum
      | "range-machine", _ | "check", _ => do
        let mut sum : UInt64 := 0
        let top := UInt64.ofNat (2^64 - 1)
        for (_, key) in targets do
          let index := view.lowerBound key
          let hi := view.lowerBound (if key > top - width then top else key + width)
          let scan := view.scan index hi
          if mode == "check" then
            let hit := if index < view.count && view.keyOrZero index == key then
              toString (view.valueOrZero index) else "-"
            IO.println s!"{hit} {index.toNat} {hi.toNat} {scan}"
          sum := sum + scan
        pure sum
      | "read-checked", _ => pure (readBatch bytes view.count.toNat word)
      | "read-guarded", _ => pure (readBatch bytes view.count.toNat wordFast)
      | "read-machine", _ => pure view.readUnaligned
      | "write-indexed", _ => pure (word (encodeIndexed scalars) 8)
      | "write-scalar", _ => pure (word (encodeScalar scalars) 8)
      | "write-loop", some _ => pure (word (encode records) 8)
      | "write-unrolled", some _ => pure (word (encode records true) 8)
      | _, _ => throw (IO.userError "unknown experiment")
    let elapsed := (← IO.monoNanosNow) - start
    if mode != "check" then IO.println s!"{elapsed} {result}"
  if (← IO.getEnv "ALVOKI_RSS").isSome then
    let status ← IO.FS.readFile "/proc/self/status"
    let some rss := (status.splitOn "\n").find? (·.startsWith "VmHWM:")
      | throw (IO.userError "missing VmHWM")
    IO.println rss
