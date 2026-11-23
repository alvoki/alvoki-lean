import Packed

open Alvoki Alvoki.Opt Alvoki.Packed

def load (path : String) : IO Run := do
  match parseRun (← IO.FS.readBinFile path) with
  | .ok run => pure run
  | .error message => throw (IO.userError message)

def foldOwned (records : @& Array ScalarRecord) : UInt64 := Id.run do
  let mut sum := 0
  for record in records do sum := sum + (record.key ^^^ record.value)
  return sum

def keySum (view : @& View) (targets : @& View) : UInt64 := Id.run do
  let mut sum := 0
  for i in [0:targets.count.toNat] do
    let key := targets.valueOrZero i.toUSize
    let index := view.lowerBound key
    if index < view.count && view.keyOrZero index == key then sum := sum + view.valueOrZero index
  return sum

@[specialize] def chunkKeySum (lookup : UInt64 → Option UInt64)
    (targets : @& View) : UInt64 := Id.run do
  let mut sum := 0
  for i in [0:targets.count.toNat] do
    sum := sum + (lookup (targets.valueOrZero i.toUSize)).getD 0
  return sum

def shouldWrite (mode : String) : Bool :=
  ["check-merge", "check-fast-merge", "check-indexed", "check-c", "check-batch-c", "check-fill-batch-c", "check-fill-indexed", "check-ffi", "check-copy", "check-chunks"].contains mode

def indexedPair (bytes : ByteArray) (offset : USize) (key value : UInt64) : ByteArray :=
  storeWord (storeWord bytes offset key) (offset + 8) value

def main (args : List String) : IO Unit := do
  let [mode, input, aux, output, repetitions] := args
    | throw (IO.userError "expected mode input auxiliary output repetitions")
  let run ← load input
  let other ← if mode.endsWith "merge" || mode.startsWith "lookup" then load aux else pure run
  let size := run.view.bytes.usize
  let runRef ← IO.mkRef run
  let otherRef ← IO.mkRef other
  let sizeRef ← IO.mkRef size
  let recordsRef ← IO.mkRef (if mode.startsWith "encode" || mode.startsWith "fill" then
    run.view.decode else #[])
  let chunksRef ← IO.mkRef (if mode.startsWith "lookup-chunk" || mode == "chunk-scan" then
    some (chunked run) else none)
  for _ in [0:repetitions.toNat?.getD 1] do
    let input ← runRef.get
    let records ← recordsRef.get
    let length ← sizeRef.get
    let prepared := if mode.startsWith "fill-" then zeroBytesC length else ByteArray.empty
    let second ← otherRef.get
    let saved ← chunksRef.get
    -- A buffer allocated before the timer is consumed only once.
    let preparedRef ← IO.mkRef prepared
    let start ← IO.monoNanosNow
    let (data, checksum) ← match mode with
      | "retain-scan" => pure (ByteArray.empty, input.view.scan 0 input.view.count)
      | "copy-scan" => do
        let bytes := input.view.bytes.extract 0 input.view.bytes.size
        pure (bytes, 0)
      | "owned-scan" => pure (ByteArray.empty, foldOwned input.view.decode)
      | "chunk-build-scan" => pure (ByteArray.empty, (chunked input).fold)
      | "chunk-scan" => pure (ByteArray.empty, (saved.map Chunks.fold).getD 0)
      | "lookup-packed" => pure (ByteArray.empty, keySum input.view second.view)
      | "lookup-chunked" => pure (ByteArray.empty, (saved.map (fun chunks => chunkKeySum chunks.lookup second.view)).getD 0)
      | "lookup-chunk-within" =>
        pure (ByteArray.empty, (saved.map (fun chunks => chunkKeySum chunks.lookupWithin second.view)).getD 0)
      | "merge" | "check-merge" => pure (merge input second, 0)
      | "fast-merge" | "check-fast-merge" => pure (mergeDisjointFast input second, 0)
      | "encode-batch-c" => pure (encodeBatchC records, 0)
      | "fill-batch-c" => pure (fillBatchC (← preparedRef.swap ByteArray.empty) records, 0)
      | "encode-indexed" => pure (encodeIndexed records, 0)
      | "encode-c" => pure (fill writePairC records (zeroBytesC length), 0)
      | "fill-c" => pure (fill writePairC records (← preparedRef.swap ByteArray.empty), 0)
      | "fill-indexed" => pure (fill indexedPair records (← preparedRef.swap ByteArray.empty), 0)
      | "init-lean" => pure (zeroedBytes length.toNat, 0)
      | "init-c" => pure (zeroBytesC length, 0)
      | "check-indexed" => pure (encodeIndexed input.view.decode, 0)
      | "check-c" => pure (fill writePairC input.view.decode (zeroBytesC length), 0)
      | "check-batch-c" => pure (encodeBatchC input.view.decode, 0)
      | "check-fill-batch-c" => pure (fillBatchC (zeroBytesC length) input.view.decode, 0)
      | "check-fill-indexed" => pure (fill indexedPair input.view.decode (zeroBytesC length), 0)
      | "check-ffi" => do
        let alias := input.view.bytes
        let offset : USize := if length > 16 then 1 else 0
        let key : UInt64 := 0x0123456789abcdef
        let value : UInt64 := 0xfedcba9876543210
        let modified := writePairC alias offset key value
        let unchanged := writePairC alias (length - 15) key value
        let wrapped := writePairC alias (0 - 1) key value
        if alias != unchanged || alias != wrapped || modified != writePair alias offset key value then
          throw (IO.userError "wide writer contract mismatch")
        pure (alias, 0)
      | "check-copy" => pure (input.view.bytes.extract 0 input.view.bytes.size, 0)
      | "check-chunks" => do
        let mut out := input.view.bytes.extract 0 16
        for part in (chunked input).parts do
          out := part.copySlice 0 out out.size part.size false
        pure (out, 0)
      | _ => throw (IO.userError "unknown packed experiment")
    let checksum := if mode == "copy-scan" then
      foldInterleaved data 1 (input.view.count + 1) else checksum
    let elapsed ← IO.monoNanosNow
    if shouldWrite mode then
      IO.FS.writeBinFile output data
    else
      let tag := if mode != "copy-scan" && data.size ≥ 16 then
        word data 0 ^^^ word data (data.size - 8) ^^^ data.size.toUInt64 else checksum
      IO.println s!"{elapsed - start} {tag}"
  if (← IO.getEnv "ALVOKI_RSS").isSome then
    let status ← IO.FS.readFile "/proc/self/status"
    let some line := (status.splitOn "\n").find? (·.startsWith "VmHWM:")
      | throw (IO.userError "missing VmHWM")
    IO.println line
