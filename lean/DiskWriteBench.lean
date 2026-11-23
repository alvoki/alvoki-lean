import Alvoki.Storage.Disk.DiskTable

open Alvoki.Storage

def main (args : List String) : IO Unit := do
  let [countArg, trialsArg] := args | throw (IO.userError "usage: alvoki-disk-write WRITES TRIALS")
  let some count := countArg.toNat? | throw (IO.userError "invalid write count")
  let some trials := trialsArg.toNat? | throw (IO.userError "invalid trial count")
  unless count > 0 && count < UInt64.size && trials > 0 do
    throw (IO.userError "expected positive write and trial counts")
  IO.println "writes,trial,ns"
  for trial in [:trials + 1] do
    IO.FS.withTempDir fun dir => do
      let db ← DiskTable.open dir
      try
        let start ← IO.monoNanosNow
        for key in [:count] do
          let _ ← db.write key.toUInt64 (some key.toUInt64)
        let elapsed := (← IO.monoNanosNow) - start
        let pin ← db.acquire
        let finalKey := (count - 1).toUInt64
        unless pin.sequence == count.toUInt64 && (← db.lookup pin.handle finalKey) == some (some finalKey) do
          throw (IO.userError "unexpected final write benchmark state")
        if trial > 0 then IO.println s!"{count},{trial},{elapsed}"
      finally db.close
