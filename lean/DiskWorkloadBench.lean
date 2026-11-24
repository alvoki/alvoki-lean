import Alvoki.Storage.Disk.DiskTable
import Std.Data.HashMap
import Std.Data.HashSet

open Alvoki.Storage
open System (FilePath)

private structure Sample where
  op : Nat
  kind : String
  amount : Nat

private structure HeldSnapshot where
  pin : DiskSnapshotPin
  key : UInt64
  value : Option UInt64

@[inline] private def measureSample (op : Nat) (kind : String) (action : IO α) : IO (α × Sample) := do
  let start ← IO.monoNanosNow
  let result ← action
  let stop ← IO.monoNanosNow
  return (result, ⟨op, kind, stop - start⟩)

private def traceKeys (count : Nat) (keyCount initialSeed : UInt64) : Array UInt64 := Id.run do
  let mut seed := initialSeed
  let mut keys := Array.emptyWithCapacity count
  for _ in [:count] do
    seed := seed * 6364136223846793005 + 1442695040888963407
    keys := keys.push ((seed >>> 32) % keyCount)
  return keys

/-- Prefer a key that the same trace overwrites while the snapshot is pinned. -/
private def snapshotKey (keys : Array UInt64) (interval : Nat) : UInt64 := Id.run do
  let mut written : Std.HashSet UInt64 := {}
  let mut lastWrite : UInt64 := 0
  for i in [:min interval keys.size:2] do
    lastWrite := keys[i]!
    written := written.insert lastWrite
  for i in [interval:min (3 * interval) keys.size] do
    if i % 2 == 0 && written.contains keys[i]! then
      return keys[i]!
  return lastWrite

private def regularFileBytes (path : FilePath) : IO Nat := do
  let mut total := 0
  for entry in ← path.readDir do
    let metadata ← (path / entry.fileName).symlinkMetadata
    if metadata.type == .file then
      total := total + metadata.byteSize.toNat
  return total

private def processWriteBytes : IO (Option Nat) := do
  try
    for line in (← IO.FS.readFile "/proc/self/io").splitOn "\n" do
      if let ["write_bytes", bytes] := line.splitOn ": " then
        return bytes.toNat?
    return none
  catch _ =>
    return none

private def latestLookup (db : DiskTable) (key : UInt64) : IO (Option (Option UInt64)) := do
  let pin ← db.acquire
  try db.lookup pin.handle key finally db.release pin.handle

private def verifyContents (db : DiskTable) (keyCount : UInt64)
    (expected : Std.HashMap UInt64 UInt64) : IO Unit := do
  let pin ← db.acquire
  try
    let some rows ← db.range pin.handle 0 keyCount |
      throw (IO.userError "could not read the final snapshot")
    unless rows.length == expected.size do
      throw (IO.userError "final snapshot has the wrong number of rows")
    let mut remaining := expected
    for row in rows do
      let some value := remaining[row.key]? |
        throw (IO.userError s!"final snapshot has an unexpected or duplicate key {row.key}")
      unless row.payload == some value do
        throw (IO.userError s!"final snapshot disagrees with the workload oracle at key {row.key}")
      remaining := remaining.erase row.key
  finally db.release pin.handle

private def runWorkload (db : DiskTable) (path : FilePath) (keys : Array UInt64)
    (keyCount : UInt64) (maintenance : Bool) (interval : Nat) : IO (Array Sample) := do
  let heldKey := if maintenance then snapshotKey keys interval else 0
  let mut samples := Array.emptyWithCapacity keys.size
  let mut values : Std.HashMap UInt64 UInt64 := {}
  let mut writes := 0
  let mut pendingWrites := false
  let mut runs := 0
  let mut held : Option HeldSnapshot := none
  let bytesBefore ← processWriteBytes
  let start ← IO.monoNanosNow
  for i in [:keys.size] do
    let op := i + 1
    let key := keys[i]!
    if i % 2 == 0 then
      let value := op.toUInt64
      let (sequence, sample) ← measureSample op "put" (db.write key (some value))
      writes := writes + 1
      unless sequence == writes.toUInt64 do
        throw (IO.userError s!"unexpected write sequence at operation {op}")
      values := values.insert key value
      pendingWrites := true
      samples := samples.push sample
    else
      let expected := values[key]?
      let (actual, sample) ← measureSample op "get" (latestLookup db key)
      unless actual == some expected do
        throw (IO.userError s!"latest read disagrees with the workload oracle at operation {op}")
      samples := samples.push sample

    if maintenance && op % interval == 0 then
      let milestone := op / interval
      if milestone == 1 then
        let (pin, sample) ← measureSample op "snapshot_pin" db.acquire
        unless pin.sequence == writes.toUInt64 do
          throw (IO.userError "snapshot did not pin the latest write sequence")
        let some value := values[heldKey]? | throw (IO.userError "snapshot target has not been written")
        held := some ⟨pin, heldKey, some value⟩
        samples := samples.push sample

      let (_, checkpoint) ← measureSample op "checkpoint" db.checkpoint
      if pendingWrites then runs := runs + 1
      pendingWrites := false
      let (_, rotation) ← measureSample op "rotate" db.rotateWal
      let (_, walCollection) ← measureSample op "collect_wal" db.collectCoveredWal
      samples := samples.push checkpoint |>.push rotation |>.push walCollection
      if runs ≥ 2 then
        let (compacted, sample) ← measureSample op "compact" (db.compact 0)
        unless compacted do throw (IO.userError s!"expected adjacent runs at operation {op}")
        runs := runs - 1
        samples := samples.push sample
      let (_, runCollection) ← measureSample op "collect_runs" (db.collectObsoleteRuns [])
      samples := samples.push runCollection

      if let some snapshot := held then
        let (actual, sample) ← measureSample op "snapshot_get" (db.lookup snapshot.pin.handle snapshot.key)
        unless actual == some snapshot.value do
          throw (IO.userError s!"pinned read disagrees with the workload oracle at operation {op}")
        samples := samples.push sample
        if milestone == 3 then
          let (_, release) ← measureSample op "snapshot_release" (db.release snapshot.pin.handle)
          held := none
          samples := samples.push release
          let (advanced, floor) ← measureSample op "advance_floor" (db.advanceFloor writes.toUInt64)
          unless advanced do throw (IO.userError "could not advance the floor after releasing the snapshot")
          let (retained, retention) ← measureSample op "retain_versions" (db.retainRunVersions 0)
          unless retained do throw (IO.userError "could not retain versions in the compacted run")
          samples := samples.push floor |>.push retention
      samples := samples.push ⟨op, "db_bytes", ← regularFileBytes path⟩
  let elapsed := (← IO.monoNanosNow) - start
  if let (some before, some after) := (bytesBefore, ← processWriteBytes) then
    samples := samples.push ⟨keys.size, "process_write_bytes", after - before⟩
  if !maintenance then
    samples := samples.push ⟨keys.size, "db_bytes", ← regularFileBytes path⟩
  verifyContents db keyCount values
  if let some snapshot := held then
    db.release snapshot.pin.handle
  return samples.push ⟨keys.size, "total", elapsed⟩

def main (args : List String) : IO Unit := do
  let [pathArg, mode, opsArg, keysArg, intervalArg, seedArg] := args |
    throw (IO.userError "usage: alvoki-disk-workload PATH MODE OPS KEYS INTERVAL SEED")
  unless mode == "mixed" || mode == "maintenance" do
    throw (IO.userError "mode must be mixed or maintenance")
  let some ops := opsArg.toNat? | throw (IO.userError "invalid operation count")
  let some keyCount := keysArg.toNat? | throw (IO.userError "invalid key count")
  let some interval := intervalArg.toNat? | throw (IO.userError "invalid maintenance interval")
  let some seed := seedArg.toNat? | throw (IO.userError "invalid workload seed")
  unless 0 < ops && ops < UInt64.size && 0 < keyCount && keyCount < UInt64.size &&
      (mode == "mixed" || 0 < interval) && seed < UInt64.size do
    throw (IO.userError "expected positive UInt64 counts, a UInt64 seed and a positive maintenance interval")

  let path : FilePath := ⟨pathArg⟩
  unless (← path.readDir).isEmpty do
    throw (IO.userError "benchmark directory must be empty")
  let keys := traceKeys ops keyCount.toUInt64 seed.toUInt64
  let db ← DiskTable.open path
  let samples ←
    try runWorkload db path keys keyCount.toUInt64 (mode == "maintenance") interval finally db.close
  let stdout ← IO.getStdout
  stdout.putStrLn "op,kind,ns"
  for sample in samples do
    stdout.putStrLn s!"{sample.op},{sample.kind},{sample.amount}"
