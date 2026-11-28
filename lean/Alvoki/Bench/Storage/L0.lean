import Alvoki.Bench.Storage.Support
import Alvoki.Experiments.L0.Native

namespace StorageBench
open System ExperimentalL0
private abbrev DB := ExperimentalL0.Native.Handle

private def initializeRoot (root : FilePath) : IO Unit := do
  for name in ["wal", "manifest", "tables"] do
    IO.FS.createDir (root / name)
  IO.FS.withFile root .read ImmutableSSTable.syncFileHandle
  let wal ← WalRecoverySlice.Segmented.Native.create (root / "wal") .boundary 128
  WalRecoverySlice.Segmented.Native.close wal
  (DurableBlob.native (root / "manifest")).publish (L0Manifest.encode .empty)

private def fill (db : DB) (base rows : Nat) : IO Unit := do
  for i in [:rows] do
    Native.put db (base + i).toUInt64 (i + 1).toUInt64

private def verify (db : DB) (base rows : Nat) : IO Unit := do
  for i in [:rows] do
    check ((← Native.get db (base + i).toUInt64) == some (i + 1).toUInt64) "incorrect L0 value"

private def fixture (db : DB) (depth : Nat) : IO Unit := do
  for run in [:depth] do
    let base := if run + 1 == depth then 100000 else 128 * run
    fill db base 64
    Native.flush db

private def getWorkload (db : DB) (scenario : String) (count : Nat) (sample : Bool) : IO Unit := do
  let samples := Array.emptyWithCapacity (if sample then count else 0)
  let (samples, measurement) ← measure do
    let mut samples := samples
    let mut seed : UInt32 := 12345
    for _ in [:count] do
      seed := 1664525 * seed + 1013904223
      let row := (seed.toNat >>> 8) % 64
      let base := if scenario == "newest" then 100000 else if scenario == "oldest" then 0 else 200000
      let expected := if scenario == "miss" then none else some (row + 1).toUInt64
      let (seen, next) ← observe sample samples scenario (Native.get db (base + row).toUInt64)
      check (seen == expected) "incorrect L0 lookup"
      samples := next
    return samples
  measurement.report scenario count
  reportSamples samples

-- Every 20 operations, write three deterministic keys, delete the third,
-- and perform 16 reads over those keys and the oldest table.
private def mixed (db : DB) (rounds : Nat) (sample : Bool) : IO Unit := do
  let samples := Array.emptyWithCapacity (if sample then 21 * rounds else 0)
  let (samples, measurement) ← measure do
    let mut samples := samples
    for round in [:rounds] do
      let base := 300000 + 3 * round
      for i in [:3] do
        let ((), next) ← observe sample samples "put" (Native.put db (base + i).toUInt64 (i + 1).toUInt64)
        samples := next
      let ((), next) ← observe sample samples "delete" (Native.delete db (base + 2).toUInt64)
      samples := next
      for i in [:16] do
        let (key, expected) := match i % 4 with
          | 0 => (base, some 1)
          | 1 => (base + 1, some 2)
          | 2 => (base + 2, none)
          | _ => (i, some (i + 1).toUInt64)
        let (seen, next) ← observe sample samples "get" (Native.get db key.toUInt64)
        check (seen == expected) "incorrect L0 mixed read"
        samples := next
      if (round + 1) % 8 == 0 then
        let ((), next) ← observe sample samples "flush" (Native.flush db)
        samples := next
    return samples
  measurement.report "mixed" (20 * rounds + rounds / 8)
  reportSamples samples

def l0 (args : List String) : IO Unit := do
  let [mode, path, depth, count, timing] := args
    | throw (IO.userError "use benchmarks/storage/run.py --suite l0")
  let root : FilePath := ⟨path⟩
  let depth ← number depth
  let count ← number count
  let sample := timing == "latency"
  initializeRoot root
  Native.withOpen root fun db => do
    match mode with
    | "flush" =>
      fill db 0 count
      let ((), measurement) ← measure (Native.flush db)
      measurement.report "flush" count
    | "mixed" =>
      fixture db depth
      mixed db count sample
    | "oldest" | "newest" | "miss" =>
      fixture db depth
      getWorkload db mode count sample
    | _ => throw (IO.userError "unknown L0 workload")
  if mode == "flush" then
    Native.withOpen root fun db => verify db 0 count
  if mode == "mixed" then
    Native.withOpen root fun db => do
      for round in [:count] do
        let base := 300000 + 3 * round
        verify db base 2
        check ((← Native.get db (base + 2).toUInt64).isNone) "L0 tombstone lost on reopen"

end StorageBench

def main := StorageBench.l0
