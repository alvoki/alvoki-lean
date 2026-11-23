import DiskTable

open Alvoki.Storage
def main (args : List String) : IO Unit := do
  let [mode, dir] := args | throw (IO.userError "usage: latency-fixture MODE DIR")
  let db ← DiskTable.open ⟨dir⟩
  try
    if mode == "seed" then
      let n ← db.write 7 (some 60)
      unless n == 1 do throw (IO.userError "wrong sequence for seed")
    else if mode == "fail" then
      let written ← try
        let _ ← db.write 7 (some 99)
        pure true
      catch _ => pure false
      if written then throw (IO.userError "unexpected write acknowledgment")
      let acquired ← try
        let _ ← db.acquire
        pure true
      catch _ => pure false
      if acquired then throw (IO.userError "failed write did not poison")
    else if mode == "append" then
      let n ← db.write 7 (some 99)
      unless n == 2 do throw (IO.userError "wrong sequence for append")
    else
      let pin ← db.acquire
      let value ← db.lookup pin.handle 7
      IO.println s!"{pin.sequence} {repr value}"
  finally db.close
