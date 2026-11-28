import Alvoki.Experiments.WAL.SingleFile

import CheckedLeaf

def checkedLoop (h : IO.FS.Handle) (acc : ByteArray) : IO ByteArray := do
  let bytes ← checked h 1024
  if bytes.isEmpty then return acc
  checkedLoop h (acc ++ bytes)
partial_fixpoint

def main : IO Unit := do
  for (label, action) in [("candidate", WalRecoverySlice.SingleFile.Internal.readChunks), ("checked", checkedLoop)] do
    let h ← IO.FS.Handle.mk "/workspace/work/cookie-input" .read
    match ← (action h .empty).toBaseIO with
    | .ok bytes => IO.println s!"{label}: success {bytes.size}"
    | .error e => IO.println s!"{label}: {e}"
