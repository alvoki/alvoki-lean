import Alvoki.Bench.Storage.Support
import Alvoki.Experiments.WAL.Segmented.Native
import Alvoki.Experiments.SSTable.UnifiedNative

namespace StorageBench
open System WalRecoverySlice
open ImmutableSSTable
private abbrev Wal := Segmented.Native.Handle

private def payload (position : Nat) : Bytes :=
  (List.range 32).map fun i => ((position >>> (8 * (i % 8))) + i * 37).toUInt8

private def checkHistory (expected : Array Bytes) (handle : Wal) : IO Unit := do
  let view ← Segmented.Native.scan handle
  check (view.base == 0 && view.batches == expected.toList) "incorrect WAL history"

private def appendWal (handle : Wal) (batches : Array Bytes) (before capacity : Nat)
    (sample : Bool) : IO (Array Sample) := do
  let mut samples := Array.emptyWithCapacity (if sample then batches.size - before else 0)
  for index in [before:batches.size] do
    let rotating := index != 0 && index % capacity == 0
    let (ack, next) ← observe sample samples (if rotating then "rotate" else "in-place")
      (Segmented.Native.append handle batches[index]!)
    check (ack == index + 1) "incorrect WAL acknowledgement"
    samples := next
  return samples

private def wal (mode : String) (path : FilePath) (policy : Policy)
    (capacity count before : Nat) (sample : Bool) : IO Unit := do
  let batches := (Array.range (before + count)).map fun index => payload (index + 1)
  match mode with
  | "prepare" | "append" =>
    let handle ← Segmented.Native.create path policy capacity
    try
      if mode == "prepare" then
        discard <| appendWal handle batches 0 capacity false
      else
        discard <| appendWal handle (batches.extract 0 before) 0 capacity false
        let (samples, measurement) ← measure (appendWal handle batches before capacity sample)
        checkHistory batches handle
        let expectedSegments := (before + count - 1) / capacity + 1
        let segments := (← path.readDir).filter fun entry => entry.fileName.startsWith "segment-"
        check (segments.size == expectedSegments) "incorrect WAL segment count"
        measurement.report "append" count
        reportSamples samples
    finally Segmented.Native.close handle
  | "reopen" =>
    let (handle, measurement) ← measure (Segmented.Native.openExisting path)
    try
      checkHistory batches handle
      measurement.report "reopen" count
    finally Segmented.Native.close handle
  | "reopen-fold" | "scan" =>
    let checkBatch := fun (seen : Nat × Bool) pos batch =>
      (seen.1 + 1, seen.2 && pos == seen.1 + 1 && batches[pos - 1]? == some batch)
    let verify := fun (bounds : Segmented.Bounds) (seen : Nat × Bool) =>
      check (bounds == ⟨0, count⟩ && seen == (count, true)) "incorrect WAL fold"
    if mode == "scan" then
      let handle ← Segmented.Native.openExisting path
      try
        let ((bounds, seen), measurement) ← measure
          (Segmented.Native.scanFold handle (0, true) checkBatch)
        verify bounds seen
        measurement.report mode count
      finally Segmented.Native.close handle
    else
      let ((handle, bounds, seen), measurement) ← measure
        (Segmented.Native.openExistingFold path (0, true) checkBatch)
      try
        verify bounds seen
        measurement.report mode count
      finally Segmented.Native.close handle
  | _ => throw (IO.userError s!"unknown WAL mode: {mode}")

-- A compute-only control on exactly the same complete 32-byte frames.
private def walCodec (rounds : Nat) : IO Unit := do
  let batches := (List.range 128).map fun index => payload (index + 1)
  let bytes := (batches.zipIdx).flatMap fun (batch, index) => frame (index + 1) batch
  let limit := bytes.length
  let input ← IO.mkRef bytes
  let ((), measurement) ← measure do
    for _ in [:rounds] do
      -- Read through IO so the native compiler cannot cache a closed pure decode.
      let bytes ← input.get
      let decoded ← IO.ofExcept (WalRecoverySlice.scan bytes limit .logOnly |>.mapError IO.userError)
      check (decoded.batches == batches && decoded.cursor.endPos == limit) "incorrect decoded frames"
  measurement.report "decode" (rounds * batches.length)

private def tableId : UInt64 := 84
private def layout : Unified.Layout := ⟨some 8, some 8, tableId⟩
private def options : Unified.BuildOptions := { dataTarget := 4096, leafTarget := 1024 }

private def key (index : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.emptyWithCapacity 8
  let word := index.toUInt64
  for i in [:8] do
    bytes := bytes.push ((word >>> ((7 - i) * 8).toUInt64).toUInt8)
  return bytes

private def value (index : Nat) : ByteArray := Alvoki.pushWordFast ByteArray.empty (index + 1).toUInt64

private def provider (rows : Nat) : IO (IO (Option Entry)) := do
  let cursor ← IO.mkRef 0
  return do
    let index ← cursor.get
    if index == rows then return none
    cursor.set (index + 1)
    return some ⟨key (2 * index), value index⟩

private def scanTable (table : Table (EIO String)) (rows : Nat) : IO Unit := do
  let mut cursor ← checked (table.seek (key 0))
  for i in [:rows] do
    let some (entry, next) ← checked (table.next cursor)
      | throw (IO.userError "table ended early")
    check (cursor == i && next == i + 1 && entry.key == key (2 * i) && entry.value == value i)
      "incorrect table row"
    cursor := next
  check (← (checked (table.next cursor)).map Option.isNone) "table has extra rows"

private def lookupTable (table : Table (EIO String)) (rows queries : Nat) (sample : Bool) :
    IO (Array Sample × Measurement) := do
  let mut seed : UInt32 := 12345
  let mut workload := Array.emptyWithCapacity queries
  for i in [:queries] do
    seed := 1664525 * seed + 1013904223
    let index := (seed.toNat >>> 8) % rows
    let miss := i % 2 == 1
    workload := workload.push (key (2 * index + i % 2), if miss then none else some (value index))
  let samples := Array.emptyWithCapacity (if sample then queries else 0)
  measure do
    let mut samples := samples
    for (query, expected) in workload do
      let (result, next) ← observe sample samples (if expected.isSome then "hit" else "miss")
        (checked (table.lookup query))
      check (result == expected) "incorrect table lookup"
      samples := next
    return samples

private def sst (mode : String) (path : FilePath) (rows queries : Nat) (sample : Bool) : IO Unit := do
  match mode with
  | "prepare" | "build" | "build-sync" =>
    let next ← provider rows
    let action := if mode == "build" then Unified.buildFile path layout next options
      else Unified.buildFileSynced path layout next options
    if mode == "prepare" then
      check ((← action) == rows) "incorrect fixture build count"
    else
      let (count, measurement) ← measure (action)
      check (count == rows) "incorrect table build count"
      scanTable (← checked (Unified.openNativeChecked path tableId)) rows
      measurement.report mode rows
  | "lookup" | "scan" =>
    let table ← checked (Unified.openNativeChecked path tableId)
    if mode == "lookup" then
      let (samples, measurement) ← lookupTable table rows queries sample
      measurement.report mode queries
      reportSamples samples
    else
      let ((), measurement) ← measure (scanTable table rows)
      measurement.report mode rows
  | _ => throw (IO.userError s!"unknown SSTable mode: {mode}")

def components (args : List String) : IO Unit := do
  match args with
  | ["wal", mode, path, policy, capacity, count, before, timing] =>
    let policy ← match policy with
      | "log" => pure Policy.logOnly
      | "boundary" => pure Policy.boundary
      | _ => throw (IO.userError "unknown WAL policy")
    wal mode ⟨path⟩ policy (← number capacity) (← number count) (← number before) (timing == "latency")
  | ["sst", mode, path, rows, queries, timing] =>
    sst mode ⟨path⟩ (← number rows) (← number queries) (timing == "latency")
  | ["codec", rounds] => walCodec (← number rounds)
  | _ => throw (IO.userError "use benchmarks/storage/run.py")

end StorageBench

def main := StorageBench.components
