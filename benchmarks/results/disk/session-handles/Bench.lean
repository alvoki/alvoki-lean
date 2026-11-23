import Alvoki.Storage.Disk.DiskTable

open Alvoki.Storage

private def setup (directory : System.FilePath) : IO Unit := do
  IO.FS.createDir directory
  let db ← DiskTable.open directory
  try
    for key in [:256] do
      let sequence ← db.write key.toUInt64 (some (key.toUInt64 + 100))
      unless sequence.toNat == key + 1 do throw (IO.userError "fixture write returned wrong sequence")
    db.checkpoint
  finally db.close

private def measureReads (directory : System.FilePath) : IO Unit := do
  let db ← DiskTable.open directory
  try
    let pin ← db.acquire
    unless pin.sequence == 256 do throw (IO.userError "fixture reopened at wrong sequence")
    let countPoints := fun (count : Nat) => do
      let mut sum := 0
      for index in [:count] do
        let key := (index.toUInt64 * 17) &&& 255
        let some (some value) ← db.lookup pin.handle key
          | throw (IO.userError "benchmark lookup missed a live value")
        sum := sum + value
      return sum
    let countRanges := fun (count : Nat) => do
      let mut sum := 0
      for index in [:count] do
        let start := ((index.toUInt64 * 13) &&& 31) * 8
        let some rows ← db.range pin.handle start (start + 8)
          | throw (IO.userError "benchmark range rejected a live handle")
        sum := rows.foldl (fun acc row => acc + row.payload.getD 0) sum
      return sum
    let fixtureSum : UInt64 := (255 * 256) / 2 + 100 * 256
    unless (← countPoints 8192) == fixtureSum * 32 && (← countRanges 1024) == fixtureSum * 32 do
      throw (IO.userError "warmup checksum mismatch")
    let pointStart ← IO.monoNanosNow
    let pointSum ← countPoints (256 * 4096)
    let pointNanos := (← IO.monoNanosNow) - pointStart
    let rangeStart ← IO.monoNanosNow
    let rangeSum ← countRanges (32 * 4096)
    let rangeNanos := (← IO.monoNanosNow) - rangeStart
    unless pointSum == fixtureSum * 4096 && rangeSum == fixtureSum * 4096 do
      throw (IO.userError "timed read checksum mismatch")
    IO.println s!"{pointNanos},{rangeNanos}"
  finally db.close

def main (args : List String) : IO Unit :=
  match args with
  | ["setup", directory] => setup ⟨directory⟩
  | ["measure", directory] => measureReads ⟨directory⟩
  | _ => throw (IO.userError "expected setup/measure DIRECTORY")
