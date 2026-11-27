import Alvoki.Storage.Disk.DiskTable

open Alvoki.Storage
open System (FilePath)

private def payload (key : UInt64) : UInt64 :=
  key ^^^ 0xfedcba9876543210

private def runBatches (db : DiskTable) (count batchSize : Nat) : IO (Array Nat × Nat) := do
  let batchCount := count / batchSize
  let mut samples := Array.emptyWithCapacity batchCount
  let started ← IO.monoNanosNow
  for batch in [:batchCount] do
    let offset := batch * batchSize
    let rows := (List.range' offset batchSize).map fun index =>
      let key := index.toUInt64
      (key, some (payload key))
    let before ← IO.monoNanosNow
    let sequence ← db.writeBatch rows
    let after ← IO.monoNanosNow
    unless sequence == (offset + batchSize).toUInt64 do
      throw (IO.userError s!"unexpected batch sequence at row {offset + batchSize}")
    samples := samples.push (after - before)
  let elapsed := (← IO.monoNanosNow) - started
  return (samples, elapsed)

private def verifyReopen (path : FilePath) (count : Nat) : IO Unit := do
  let db ← DiskTable.open path
  try
    let pin ← db.acquire
    unless pin.sequence == count.toUInt64 do
      throw (IO.userError "reopen returned the wrong committed sequence")
    let maxKey := (UInt64.size - 1).toUInt64
    let some rows ← db.range pin.handle 0 maxKey
      | throw (IO.userError "reopened range rejected its snapshot")
    let mut key : UInt64 := 0
    for row in rows do
      unless row.key == key && row.payload == some (payload key) do
        throw (IO.userError s!"unexpected reopened row for key {key}")
      key := key + 1
    unless key == count.toUInt64 && (← db.lookup pin.handle maxKey) == some none do
      throw (IO.userError "reopen returned the wrong set of keys")
  finally db.close

def main (args : List String) : IO Unit := do
  let [path, countArg, batchArg] := args
    | throw (IO.userError "usage: alvoki-disk-batch PATH ROWS BATCH_SIZE")
  let some count := countArg.toNat? | throw (IO.userError "invalid row count")
  let some batchSize := batchArg.toNat? | throw (IO.userError "invalid batch size")
  unless 0 < count && count < UInt64.size && 0 < batchSize && count % batchSize == 0 do
    throw (IO.userError "expected a positive UInt64 row count divisible by the positive batch size")
  let dir : FilePath := ⟨path⟩
  unless (← dir.readDir).isEmpty do
    throw (IO.userError "benchmark directory must be empty")
  let db ← DiskTable.open dir
  let (samples, total) ← try runBatches db count batchSize finally db.close
  verifyReopen dir count
  let stdout ← IO.getStdout
  stdout.putStrLn "rows,kind,ns"
  for (ns, index) in samples.toList.zipIdx do
    stdout.putStrLn s!"{(index + 1) * batchSize},batch,{ns}"
  stdout.putStrLn s!"{count},total,{total}"
