import Alvoki.Experiments.WAL.SingleFile
open WalRecoverySlice System

def main (args : List String) : IO Unit := do
  let dir : FilePath := args.head!
  let start ← IO.monoNanosNow
  for _ in [:250] do
    let h ← SingleFile.openExisting dir
    unless (← SingleFile.scan h) == [[7]] do throw (IO.userError "wrong history")
    SingleFile.close h
  IO.println ((← IO.monoNanosNow) - start)
