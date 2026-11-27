import Alvoki.Experiments.WAL.Recovery
import Alvoki.Storage.Disk.StagingFile

/-! Linux fixture for the single-writer protocol, using a private temporary directory.
The fixture creates versioned policy metadata in a private directory. -/
namespace WalRecoveryFiles
open WalRecoverySlice System

@[extern "alvoki_fsync"]
private opaque syncHandle (h : @& IO.FS.Handle) : IO Unit

private abbrev FileTest := ExceptT String IO

private def encodeBytes (xs : Bytes) : ByteArray :=
  ⟨xs.toArray⟩

private def writeAndSync (file : FilePath) (data : ByteArray) : IO Unit := do
  IO.FS.withFile file .writeNew fun h => do
    h.write data
    h.flush
    syncHandle h

private def fileOps (dir : FilePath) (writer reader : IO.FS.Handle) : Ops FileTest where
  append xs := do
    writer.write (encodeBytes xs)
    writer.flush
  syncData := syncHandle writer
  replaceMarker endPos seq := do
    let staged := dir / "commit.next"
    let h ← Alvoki.Storage.writeFreshStagedHandle staged s!"1 {endPos} {seq}".toUTF8
    syncHandle h
    IO.FS.rename staged (dir / "commit")
  syncDirectory := liftM (m := IO) (IO.FS.withFile dir .read syncHandle)
  readData := do
    reader.rewind
    let bytes ← reader.readBinToEnd
    return bytes.data.toList
  readMarker := do
    let fields := (← IO.FS.readFile (dir / "commit")).splitOn " "
    let ["1", offset, seq] := fields | throw "invalid marker"
    let some n := offset.toNat? | throw "invalid offset"
    let some s := seq.toNat? | throw "invalid sequence"
    return (n, s)
  truncate n := do
    reader.rewind
    let prefixBytes ← reader.read n.toUSize
    unless prefixBytes.size == n do throw "short prefix read"
    reader.truncate

private def checked (x : FileTest α) : IO α := do
  match ← x.run with
  | .ok v => return v
  | .error e => throw <| IO.userError e

private def withOps (dir : FilePath) (f : Policy → Ops FileTest → IO α) : IO α := do
  let policy ← match ← IO.FS.readFile (dir / "policy") with
    | "v1 log" => pure Policy.logOnly
    | "v1 boundary" => pure Policy.boundary
    | _ => throw <| IO.userError "unrecognized WAL policy"
  -- Opening the existing segment first also rejects a missing segment.
  IO.FS.withFile (dir / "segment") .readWrite fun reader =>
    IO.FS.withFile (dir / "segment") .append fun writer =>
      f policy (fileOps dir writer reader)

private def fixture (dir : FilePath) (policy : Policy) : IO Unit := do
  let path := dir / "segment"
  writeAndSync (dir / "policy") (if policy == .boundary then "v1 boundary" else "v1 log").toUTF8
  writeAndSync path ByteArray.empty
  if policy == .boundary then writeAndSync (dir / "commit") "1 0 0".toUTF8
  IO.FS.withFile dir .read syncHandle
  let a := [11, 12]
  let b := [21, 22]
  let c := [31]
  let afterA ← withOps dir fun policy ops => checked (appendBatch ops policy {} a)
  -- Materialize a truncated B without pretending a process kill is power loss.
  IO.FS.withFile path .append fun h => do
    h.write (encodeBytes ((frame 2 b).take 3))
    h.flush
  if policy == .boundary then writeAndSync (dir / "commit.next") "stale".toUTF8
  withOps dir fun policy ops => do
    let opened ← checked (reopen ops policy)
    unless opened.batches == [a] && opened.cursor == afterA do
      throw <| IO.userError "failed to recover A"
    let _ ← checked (appendBatch ops policy opened.cursor c)
    pure ()
  let reopened ← withOps dir fun policy ops => checked (reopen ops policy)
  unless reopened.batches == [a, c] do throw <| IO.userError "lost A or C"
  if policy == .boundary then
    let bytes ← IO.FS.readBinFile path
    let damaged := bytes.set! (bytes.size - 1) ((bytes.get! (bytes.size - 1)) ^^^ 1)
    IO.FS.writeBinFile path damaged
    let r ← withOps dir fun policy ops => (reopen ops policy).run
    if r.isOk then throw <| IO.userError "opened with damaged published bytes"
    unless (← IO.FS.readBinFile path) == damaged do throw <| IO.userError "destructive failed open"

end WalRecoveryFiles

def main : IO Unit := do
  for policy in [WalRecoverySlice.Policy.logOnly, .boundary] do
    IO.FS.withTempDir fun dir => WalRecoveryFiles.fixture dir policy
  IO.println "WAL recovery file fixtures passed"
