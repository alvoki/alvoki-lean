import Alvoki.Experiments.WAL.SingleFile
open WalRecoverySlice System

def main (args : List String) : IO Unit := do
  let dir : FilePath := args[1]!
  let path := dir / "segment"
  if args.head! == "create" then
    let h ← SingleFile.create dir .boundary
    SingleFile.append h [7]
    SingleFile.close h
    let bytes ← IO.FS.readBinFile path
    IO.FS.writeBinFile path (bytes ++ ⟨Array.replicate 2000 0⟩)
  else
    match ← (SingleFile.openExisting dir).toBaseIO with
    | .error e => IO.println s!"reopen error {e}"
    | .ok h =>
      IO.println s!"reopen success {← SingleFile.scan h}"
      SingleFile.close h
