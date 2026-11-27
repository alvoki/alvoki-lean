import Alvoki.Storage.Disk.DiskTable

open Alvoki.Storage

private def valueFor (key : UInt64) : UInt64 := key ^^^ 0xfedcba9876543210

private def writeKeys (db : DiskTable) (first stop : Nat) : IO Unit := do
  for key in [first:stop] do
    let acknowledged ← db.write key.toUInt64 (some (valueFor key.toUInt64))
    unless acknowledged.toNat == key + 1 do
      throw (IO.userError "unexpected durable write acknowledgement")

private def populate (path : System.FilePath) (checkpointed suffix : Nat) : IO Unit := do
  let db ← DiskTable.open path
  try
    writeKeys db 0 checkpointed
    db.checkpoint
    db.rotateWal
    writeKeys db checkpointed (checkpointed + suffix)
    let stdout ← IO.getStdout
    stdout.putStrLn s!"acknowledged {checkpointed + suffix}"
    stdout.flush
    let stdin ← IO.getStdin
    let _ ← stdin.getLine
    throw (IO.userError "writer's stdin closed before SIGKILL")
  finally db.close

private def peakRssLine : IO String := do
  try
    let status ← IO.FS.readFile "/proc/self/status"
    return ((status.splitOn "\n").find? (·.startsWith "VmHWM:")).getD "-"
  catch _ =>
    return "-"

private def recover (path : System.FilePath) (size : UInt64) : IO Unit := do
  let key := size - 1
  let limit := UInt64.ofNat (UInt64.size - 1)
  let start ← IO.monoNanosNow
  let db ← DiskTable.open path
  try
    let pin ← db.acquire
    let value ← db.lookup pin.handle key
    let elapsed := (← IO.monoNanosNow) - start
    unless value == some (some (valueFor key)) && pin.sequence == size do
      throw (IO.userError "first read or recovered sequence differed")
    let rss ← peakRssLine
    let some rows ← db.range pin.handle 0 limit
      | throw (IO.userError "could not scan recovered snapshot")
    let mut expected := (0 : UInt64)
    for row in rows do
      unless row.key == expected && row.payload == some (valueFor expected) do
        throw (IO.userError s!"unexpected recovered row at key {expected}")
      expected := expected + 1
    unless expected == size && (← db.lookup pin.handle limit) == some none do
      throw (IO.userError s!"recovered {expected} rows, expected {size}")
    IO.println elapsed
    IO.println rss
  finally db.close

def main (args : List String) : IO Unit := do
  let [mode, path, prefixArg, suffixArg] := args
    | throw (IO.userError "usage: alvoki-disk-crash (write|read) DIR PREFIX SUFFIX")
  let some checkpointed := prefixArg.toNat? | throw (IO.userError "invalid prefix count")
  let some suffix := suffixArg.toNat? | throw (IO.userError "invalid suffix count")
  let size := checkpointed + suffix
  unless 0 < checkpointed && 0 < suffix && size < UInt64.size do
    throw (IO.userError "expected positive counts with a UInt64 total")
  match mode with
  | "write" => populate ⟨path⟩ checkpointed suffix
  | "read" => recover ⟨path⟩ size.toUInt64
  | _ => throw (IO.userError "expected write or read mode")
