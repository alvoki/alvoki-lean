import Alvoki.Experiments.DurableBlob.Native
import Alvoki.Experiments.Manifest.Basic

open System L0Manifest

private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def fails (action : IO α) : IO Bool := do
  try
    let _ ← action
    return false
  catch _ => return true

def main : IO Unit := IO.FS.withTempDir fun dir => do
  let blob := DurableBlob.native dir
  let manifest := backend IO.userError blob
  check (← fails manifest.reopen) "missing manifest must fail"
  -- Set up the fixture's initial durable value using the replacement path.
  blob.publish (encode Version.empty)
  check (decide ((← manifest.reopen) = Version.empty)) "initial manifest"
  let proposal : Version := ⟨[41, 7], UInt64.ofNat (2^64 - 1)⟩
  manifest.publish proposal
  check (decide ((← manifest.reopen) = proposal)) "manifest round trip"
  check (← fails (manifest.publish ⟨[7, 7], 0⟩)) "duplicate IDs must be rejected"
  IO.FS.writeBinFile (dir / "BLOB.next") (encode Version.empty)
  check (decide ((← manifest.reopen) = proposal)) "unpublished staging file must be ignored"
  manifest.publish Version.empty
  check (decide ((← manifest.reopen) = Version.empty)) "replacement after stale staging file"
  blob.publish (ByteArray.mk #[65])
  check (← fails manifest.reopen) "malformed manifest must fail"
