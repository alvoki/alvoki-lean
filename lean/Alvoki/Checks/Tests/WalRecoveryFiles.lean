import Alvoki.Experiments.WAL.SingleFile

/-! Linux fixture for the single-writer protocol, using a private temporary directory.
The fixture creates versioned policy metadata in a private directory. -/
namespace WalRecoveryFiles
open WalRecoverySlice System

@[extern "alvoki_fsync"]
private opaque syncHandle (h : @& IO.FS.Handle) : IO Unit

private def encodeBytes (xs : Bytes) : ByteArray :=
  ⟨xs.toArray⟩

private def fixture (dir : FilePath) (policy : Policy) : IO Unit := do
  let path := dir / "segment"
  let a : Bytes := [11, 12]
  let b : Bytes := [21, 22]
  let c : Bytes := [31]
  let h ← SingleFile.create dir policy
  SingleFile.append h a
  let duplicate ← (SingleFile.openExisting dir).toBaseIO
  unless duplicate matches .error _ do throw <| IO.userError "duplicate handle admitted"
  SingleFile.close h
  let stale ← (SingleFile.append h b).toBaseIO
  unless stale matches .error _ do throw <| IO.userError "closed handle accepted append"
  let afterA : Cursor := ⟨(frame 1 a).length, 2⟩
  -- Materialize a truncated B without pretending a process kill is power loss.
  IO.FS.withFile path .append fun h => do
    h.write (encodeBytes ((frame 2 b).take 3))
    h.flush
  if policy == .boundary then
    -- Break the inactive file's checksum in place; A is still held by commit.1.
    IO.FS.withFile (dir / "commit.0") .readWrite fun h => do
      h.write ⟨#[255]⟩
      h.flush
      syncHandle h
  let h ← SingleFile.openExisting dir
  unless (← SingleFile.scan h) == [a] do throw <| IO.userError "failed to recover A"
  SingleFile.append h c
  SingleFile.close h
  let h ← SingleFile.openExisting dir
  let entries ← SingleFile.scan h
  unless entries == [a, c] do throw <| IO.userError "lost A or C"
  SingleFile.close h
  let reopenedCursor : Cursor := ⟨(frame 1 a).length + (frame 2 c).length, 3⟩
  if policy == .boundary then
    let slotA ← IO.FS.readBinFile (dir / "commit.1")
    let slotC ← IO.FS.readBinFile (dir / "commit.0")
    unless slotA == encodeBytes (encodeMarker afterA.endPos 1) &&
        slotC == encodeBytes (encodeMarker reopenedCursor.endPos 2) do
      throw <| IO.userError "expected alternating fixed marker files"
    -- An oversized inactive file cannot be repaired by a fixed-width overwrite.
    IO.FS.withFile (dir / "commit.1") .append fun h => do
      h.write ⟨#[0]⟩
      h.flush
      syncHandle h
    let oversized ← (SingleFile.openExisting dir).toBaseIO
    unless oversized matches .error (.userError "oversized marker file") do
      throw <| IO.userError "opened with oversized inactive marker"
    IO.FS.withFile (dir / "commit.1") .readWrite fun h => do
      let _ ← h.read markerSize.toUSize
      h.truncate
      syncHandle h
    let bytes ← IO.FS.readBinFile path
    let damaged := bytes.set! (bytes.size - 1) ((bytes.get! (bytes.size - 1)) ^^^ 1)
    IO.FS.writeBinFile path damaged
    let r ← (SingleFile.openExisting dir).toBaseIO
    unless r matches .error (.userError "damaged batch") do throw <| IO.userError "opened with damaged published bytes"
    unless (← IO.FS.readBinFile path) == damaged do throw <| IO.userError "destructive failed open"

private def handleRegressions (dir : FilePath) (policy : Policy) : IO Unit := do
  let h ← SingleFile.create dir policy
  let failed ← (SingleFile.append h (List.replicate 33 42)).toBaseIO
  unless failed matches .error _ do throw <| IO.userError "oversized append accepted"
  let poisoned ← (SingleFile.append h [1]).toBaseIO
  unless poisoned matches .error _ do throw <| IO.userError "poisoned handle accepted append"
  let poisonedScan ← (SingleFile.scan h).toBaseIO
  unless poisonedScan matches .error _ do throw <| IO.userError "poisoned handle allowed scan"
  SingleFile.close h
  let h2 ← SingleFile.openExisting dir
  unless (← SingleFile.scan h2) == [] do throw <| IO.userError "invalid append changed history"
  let stale ← (SingleFile.append h [2]).toBaseIO
  unless stale matches .error _ do throw <| IO.userError "stale handle accepted append after reopen"
  SingleFile.append h2 [3]
  SingleFile.close h2
  let h3 ← SingleFile.openExisting dir
  unless (← SingleFile.scan h3) == [[3]] do throw <| IO.userError "reopened history mismatch"
  SingleFile.close h3

private def refuseNonempty (dir : FilePath) : IO Unit := do
  IO.FS.writeBinFile (dir / "segment") ⟨#[17, 18]⟩
  let result ← (SingleFile.create dir .boundary).toBaseIO
  unless result matches .error _ do throw <| IO.userError "initialized nonempty directory"
  unless (← IO.FS.readBinFile (dir / "segment")) == ⟨#[17, 18]⟩ do
    throw <| IO.userError "initialization changed existing segment"
  if ← (dir / "policy").pathExists then throw <| IO.userError "created policy in nonempty directory"

/-- The runner limits regular files to 1024 bytes and ignores SIGXFSZ. The
27th frame can write only its first 36 bytes before the OS rejects the rest. -/
private def partialWrite (dir : FilePath) (policy : Policy) : IO Unit := do
  let h ← SingleFile.create dir policy
  let batches := (List.range 26).map fun i => List.replicate 32 i.toUInt8
  for batch in batches do SingleFile.append h batch
  let uncertain ← (SingleFile.append h (List.replicate 32 99)).toBaseIO
  unless uncertain matches .error _ do throw <| IO.userError "expected a write error"
  unless (← IO.FS.readBinFile (dir / "segment")).size == 1024 do
    throw <| IO.userError "expected a partial frame on disk"
  SingleFile.close h
  let recovered ← SingleFile.openExisting dir
  unless (← SingleFile.scan recovered) == batches do throw <| IO.userError "lost ACK after partial write"
  SingleFile.append recovered [100]
  let stale ← (SingleFile.append h [101]).toBaseIO
  unless stale matches .error _ do throw <| IO.userError "closed handle still active"
  SingleFile.close recovered
  let reopened ← SingleFile.openExisting dir
  unless (← SingleFile.scan reopened) == batches ++ [[100]] do throw <| IO.userError "unexpected suffix"
  SingleFile.close reopened

end WalRecoveryFiles

def main (args : List String) : IO Unit := do
  if args == ["--partial-write"] then
    for policy in [WalRecoverySlice.Policy.logOnly, .boundary] do
      IO.FS.withTempDir fun dir => WalRecoveryFiles.partialWrite dir policy
    IO.println "WAL partial-write recovery passed"
    return
  for policy in [WalRecoverySlice.Policy.logOnly, .boundary] do
    IO.FS.withTempDir fun dir => WalRecoveryFiles.fixture dir policy
    IO.FS.withTempDir fun dir => WalRecoveryFiles.handleRegressions dir policy
  IO.FS.withTempDir WalRecoveryFiles.refuseNonempty
  IO.println "WAL recovery file fixtures passed"
