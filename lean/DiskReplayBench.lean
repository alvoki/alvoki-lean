import Alvoki.Storage.Disk.DiskTable

open Alvoki.Storage

private def checkContents (db : DiskTable) (handle : DiskSnapshotHandle)
    (size : UInt64) : IO Unit := do
  let some rows ← db.range handle 0 size
    | throw (IO.userError "replay benchmark could not scan the recovered snapshot")
  let mut expected := (0 : UInt64)
  for row in rows do
    unless row.key == expected && row.payload == some (expected ^^^ 0xfedcba9876543210) do
      throw (IO.userError s!"unexpected recovered row for key {expected}")
    expected := expected + 1
  unless expected == size do
    throw (IO.userError s!"recovered {expected} rows, expected {size}")

def main (args : List String) : IO Unit := do
  let (dir, sizeArg, trialsArg, repair) ← match args with
    | [dir, size, trials] => pure (dir, size, trials, false)
    | [dir, size, trials, "--repair-tail"] => pure (dir, size, trials, true)
    | _ => throw (IO.userError "usage: alvoki-disk-replay DIR RECORDS TRIALS [--repair-tail]")
  let some size := sizeArg.toNat? | throw (IO.userError "invalid record count")
  let some trials := trialsArg.toNat? | throw (IO.userError "invalid trial count")
  unless size > 0 && size < UInt64.size && trials > 0 do
    throw (IO.userError "expected positive trial count and positive UInt64 record count")
  let wal : System.FilePath := (⟨dir⟩ : System.FilePath) / "WAL"
  let fixture ← if repair then some <$> IO.FS.readBinFile wal else pure none
  for trial in [:trials + 1] do
    if let some bytes := fixture then IO.FS.writeBinFile wal bytes
    let start ← IO.monoNanosNow
    let db ← DiskTable.open ⟨dir⟩
    try
      let elapsed := (← IO.monoNanosNow) - start
      let pin ← db.acquire
      unless pin.sequence.toNat == size do throw (IO.userError "unexpected recovered watermark")
      if repair then
        let repaired ← IO.FS.readBinFile wal
        unless repaired.size == size * Alvoki.WAL.frameSize do
          throw (IO.userError "benchmark WAL was not repaired")
      if trial == 0 then
        checkContents db pin.handle size.toUInt64
      else
        IO.println elapsed
    finally db.close
