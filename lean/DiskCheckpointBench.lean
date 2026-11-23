import DiskTable

open System Alvoki Alvoki.Compaction Alvoki.Storage

private def seedCheckpoint (dir : FilePath) (runs rows : Nat) : IO Unit := do
  for index in [:runs] do
    let records : List RawEntry := (List.range rows).map fun offset =>
      let key := index * rows + offset
      ⟨key.toUInt64, (key + 1).toUInt64, (0, key.toUInt64)⟩
    IO.FS.writeBinFile (dir / s!"run-1-{index}.v3") (encodeV3 records)
  let total := runs * rows
  let events : List WAL.Write := (List.range total).map fun key =>
    ⟨(key + 1).toUInt64, key.toUInt64, some key.toUInt64⟩
  let wal := WAL.encode events
  IO.FS.writeBinFile (dir / "WAL") wal
  IO.FS.writeBinFile (dir / "WAL.commit") (WAL.Boundary.encode wal.size.toUInt64)
  IO.FS.writeBinFile (dir / "MANIFEST") (Manifest.encode ⟨1, total.toUInt64, 0, runs.toUInt64⟩)

def main (args : List String) : IO Unit := do
  let [runsArg, rowsArg, trialsArg] := args
    | throw (IO.userError "usage: alvoki-disk-checkpoint RUNS ROWS-PER-RUN TRIALS")
  let some runs := runsArg.toNat? | throw (IO.userError "invalid run count")
  let some rows := rowsArg.toNat? | throw (IO.userError "invalid row count")
  let some trials := trialsArg.toNat? | throw (IO.userError "invalid trial count")
  let total := runs * rows
  unless runs > 0 && rows > 0 && total * WAL.frameSize < UInt64.size && trials > 0 do
    throw (IO.userError "expected positive run, row and trial counts within the WAL size limit")
  IO.println "runs,rows_per_run,trial,ns"
  for trial in [:trials + 1] do
    IO.FS.withTempDir fun dir => do
      seedCheckpoint dir runs rows
      let db ← DiskTable.open dir
      let elapsed ← try
        let start ← IO.monoNanosNow
        db.checkpoint
        pure ((← IO.monoNanosNow) - start)
      finally db.close
      let .ok manifest := Manifest.decode (← IO.FS.readBinFile (dir / "MANIFEST"))
        | throw (IO.userError "checkpoint benchmark did not install a valid manifest")
      unless manifest.generation == 2 && manifest.runCount == runs.toUInt64 do
        throw (IO.userError "checkpoint benchmark installed the wrong run set")
      let reopened ← DiskTable.open dir
      try
        let pin ← reopened.acquire
        let lastKey := (total - 1).toUInt64
        unless pin.sequence == total.toUInt64 && (← reopened.lookup pin.handle lastKey) == some (some lastKey) do
          throw (IO.userError "checkpoint benchmark changed recovered data")
      finally reopened.close
      if trial > 0 then IO.println s!"{runs},{rows},{trial},{elapsed}"
