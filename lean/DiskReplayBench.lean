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
  let (dir, sizeArg, trialsArg, keeperArg) ← match args with
    | [dir, size, trials] => pure (dir, size, trials, none)
    | [dir, size, trials, "--repair-tail"] => pure (dir, size, trials, some "0")
    | [dir, size, trials, "--repair-tail", keeper] => pure (dir, size, trials, some keeper)
    | _ => throw (IO.userError "usage: alvoki-disk-replay DIR RECORDS TRIALS [--repair-tail [KEEPER]]")
  let some size := sizeArg.toNat? | throw (IO.userError "invalid record count")
  let some trials := trialsArg.toNat? | throw (IO.userError "invalid trial count")
  unless size > 0 && size < UInt64.size && trials > 0 do
    throw (IO.userError "expected positive trial count and positive UInt64 record count")
  let fixture ← keeperArg.mapM fun arg => do
    let some first := arg.toNat? | throw (IO.userError "invalid keeper frame offset")
    unless first ≤ size do throw (IO.userError "keeper frame offset exceeds the committed record count")
    let keeper := (⟨dir⟩ : System.FilePath) / renderWalSegmentName first
    let bytes ← IO.FS.readBinFile keeper
    let keep := (size - first) * Alvoki.WAL.frameSize
    unless keep < bytes.size do throw (IO.userError "expected a tail after the keeper's committed bytes")
    pure (keeper, bytes, bytes.extract 0 keep)
  for trial in [:trials + 1] do
    if let some (keeper, bytes, _) := fixture then IO.FS.writeBinFile keeper bytes
    let start ← IO.monoNanosNow
    let db ← DiskTable.open ⟨dir⟩
    try
      let elapsed := (← IO.monoNanosNow) - start
      let pin ← db.acquire
      unless pin.sequence.toNat == size do throw (IO.userError "unexpected recovered watermark")
      if let some (keeper, _, expected) := fixture then
        let repaired ← IO.FS.readBinFile keeper
        unless decide (repaired = expected) do
          throw (IO.userError "benchmark keeper did not preserve the exact committed prefix")
      if trial == 0 then
        checkContents db pin.handle size.toUInt64
      else
        IO.println elapsed
    finally db.close
