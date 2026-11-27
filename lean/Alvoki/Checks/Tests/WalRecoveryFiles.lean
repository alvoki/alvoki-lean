import Alvoki.Experiments.WAL.SingleFile

/-! Linux fixture for the single-writer protocol, using a private temporary directory.
The fixture creates versioned policy metadata in a private directory. -/
namespace WalRecoveryFiles
open WalRecoverySlice System

@[extern "alvoki_fsync"]
private opaque syncHandle (h : @& IO.FS.Handle) : IO Unit

@[extern "alvoki_test_fail_directory_sync"]
private opaque failDirectorySync (_ : Unit) : IO Unit

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

private def truncateToZero (dir : FilePath) (policy : Policy) : IO Unit := do
  let empty ← SingleFile.create dir policy
  SingleFile.close empty
  let path := dir / "segment"
  IO.FS.writeBinFile path (encodeBytes ((frame 1 [9]).take 3))
  let repaired ← SingleFile.openExisting dir
  unless (← SingleFile.scan repaired).isEmpty && (← IO.FS.readBinFile path).isEmpty do
    throw <| IO.userError "expected recovery to truncate the segment to zero"
  SingleFile.append repaired [7]
  unless (← IO.FS.readBinFile path) == encodeBytes (frame 1 [7]) do
    throw <| IO.userError "pre-opened append descriptor did not write at the repaired end"
  SingleFile.close repaired
  for _ in [:2] do
    let reopened ← SingleFile.openExisting dir
    unless (← SingleFile.scan reopened) == [[7]] do
      throw <| IO.userError "repeated reopen changed the repaired history"
    SingleFile.close reopened

private def lateOpenFailure (dir : FilePath) (policy : Policy) : IO Unit := do
  let h ← SingleFile.create dir policy
  SingleFile.append h [7]
  SingleFile.close h
  let path := dir / "segment"
  let confirmed ← IO.FS.readBinFile path
  IO.FS.writeBinFile path (confirmed ++ encodeBytes ((frame 2 [9]).take 3))
  failDirectorySync ()
  match ← (SingleFile.openExisting dir).toBaseIO with
  | .error (.userError "injected directory fsync failure") => pure ()
  | .error err => throw err
  | .ok unexpected =>
    SingleFile.close unexpected
    throw <| IO.userError "open returned a handle after the directory sync failed"
  unless (← IO.FS.readBinFile path) == confirmed do
    throw <| IO.userError "failed open did not retain the completed repair"
  let retry ← SingleFile.openExisting dir
  try
    unless (← SingleFile.scan retry) == [[7]] do
      throw <| IO.userError "retry did not recover the confirmed history"
  finally
    SingleFile.close retry

private def refuseNonempty (dir : FilePath) : IO Unit := do
  IO.FS.writeBinFile (dir / "segment") ⟨#[17, 18]⟩
  let result ← (SingleFile.create dir .boundary).toBaseIO
  unless result matches .error _ do throw <| IO.userError "initialized nonempty directory"
  unless (← IO.FS.readBinFile (dir / "segment")) == ⟨#[17, 18]⟩ do
    throw <| IO.userError "initialization changed existing segment"
  if ← (dir / "policy").pathExists then throw <| IO.userError "created policy in nonempty directory"

private def refuseOldPolicy (dir : FilePath) (policy : Policy) : IO Unit := do
  -- Reconstruct a valid old directory with one acknowledged batch [9].
  let stamp := if policy == .boundary then "v2 boundary" else "v1 log"
  IO.FS.writeFile (dir / "policy") stamp
  let segment : ByteArray := ⟨#[42, 1, 1, 1, 118, 9, 153]⟩
  IO.FS.writeBinFile (dir / "segment") segment
  if policy == .boundary then
    IO.FS.writeBinFile (dir / "commit.0") ⟨#[77, 1, 1, 0, 0, 0, 162]⟩
    IO.FS.writeBinFile (dir / "commit.1") ⟨#[77, 1, 1, 1, 0, 7, 126]⟩
  let opened ← (SingleFile.openExisting dir).toBaseIO
  unless opened matches .error (.userError "unrecognized WAL policy") do
    throw <| IO.userError s!"failed to reject old policy {stamp}"
  unless (← IO.FS.readBinFile (dir / "segment")) == segment do
    throw <| IO.userError "old segment changed during rejected open"

/-- The runner limits regular files to 1024 bytes and ignores SIGXFSZ. The
first 19 frames occupy 988 bytes. Only 36 bytes of the 20th frame fit. -/
private def partialWrite (dir : FilePath) (policy : Policy) : IO Unit := do
  let h ← SingleFile.create dir policy
  let batches := (List.range 19).map fun i => List.replicate 32 i.toUInt8
  for batch in batches do SingleFile.append h batch
  let segment := dir / "segment"
  let confirmed ← IO.FS.readBinFile segment
  unless confirmed.size == 988 do throw <| IO.userError "unexpected confirmed segment size"
  let submitted := List.replicate 32 99
  let uncertain ← (SingleFile.append h submitted).toBaseIO
  unless uncertain matches .error _ do throw <| IO.userError "expected a write error"
  unless (← IO.FS.readBinFile segment) == confirmed ++ encodeBytes ((frame 20 submitted).take 36) do
    throw <| IO.userError "expected 36 bytes of frame 20 after the confirmed prefix"
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
    IO.FS.withTempDir fun dir => WalRecoveryFiles.truncateToZero dir policy
    IO.FS.withTempDir fun dir => WalRecoveryFiles.lateOpenFailure dir policy
    IO.FS.withTempDir fun dir => WalRecoveryFiles.refuseOldPolicy dir policy
  IO.FS.withTempDir WalRecoveryFiles.refuseNonempty
  IO.println "WAL recovery file fixtures passed"
