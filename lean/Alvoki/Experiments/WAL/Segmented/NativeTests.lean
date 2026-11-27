import Alvoki.Experiments.WAL.Segmented.Native

/-! Linux regressions for the actual segmented WAL and shared schedules. -/
namespace WalRecoverySlice.Segmented.NativeTests
open System
open WalRecoverySlice.Segmented.Native

private def require (yes : Bool) (why : String) : IO Unit := do
  unless yes do throw <| IO.userError why

private def failed (action : IO α) (why : String) : IO Unit := do
  let result ← action.toBaseIO
  require (result matches .error _) why

private def check (h : Native.Handle) (base : Nat) (batches : List Bytes) : IO Unit := do
  let seen ← Native.scan h
  require (seen == ⟨base, batches⟩) s!"unexpected retained history {repr seen}"

private def lifecycle (dir : FilePath) (p : Policy) : IO Unit := do
  let h ← Native.create dir p 2
  failed (Native.openExisting dir) "admitted two handles for the same directory"
  Native.append h [1]
  Native.append h [2]
  -- An interrupted successor preparation can leave a directory with incomplete child files.
  IO.FS.createDir (dir / "segment-1")
  IO.FS.writeFile (dir / "segment-1" / "policy") "incomplete"
  Native.append h [3]
  Native.append h [4]
  Native.append h [5]
  Native.discardThrough h 1
  check h 1 [[2], [3], [4], [5]]
  require (← (dir / "segment-0").pathExists) "partially retained segment was reclaimed"
  Native.close h
  failed (Native.append h [9]) "closed alias accepted an append"
  let h ← Native.openExisting dir
  check h 1 [[2], [3], [4], [5]]
  Native.discardThrough h 4
  check h 4 [[5]]
  require (!(← (dir / "segment-0").pathExists) && !(← (dir / "segment-1").pathExists))
    "obsolete sealed segments still exist"
  Native.discardThrough h 5
  Native.discardThrough h 3
  Native.append h [6]
  check h 5 [[6]]
  Native.close h
  let h ← Native.openExisting dir
  check h 5 [[6]]
  Native.close h

private def retryRotation (dir : FilePath) (p : Policy) : IO Unit := do
  let h ← Native.create dir p 1
  Native.append h [1]
  let previous ← IO.FS.readBinFile (dir / "CONTROL")
  IO.FS.createDir (dir / "CONTROL.next")
  failed (Native.append h [2]) "rotation overwrote an invalid staging binding"
  require ((← IO.FS.readBinFile (dir / "CONTROL")) == previous) "failed staging changed control"
  require (← (dir / "segment-1").pathExists) "expected the prepared unpublished successor"
  Native.close h
  IO.FS.removeDir (dir / "CONTROL.next")
  let h ← Native.openExisting dir
  check h 0 [[1]]
  Native.append h [3]
  Native.close h
  let h ← Native.openExisting dir
  check h 0 [[1], [3]]
  Native.close h

private def retryAfterRelease (dir : FilePath) (p : Policy) : IO Unit := do
  let h ← Native.create dir p 1
  Native.append h [10]
  Native.append h [11]
  let unknown := dir / "segment-0" / "unmanaged"
  IO.FS.writeFile unknown "keep"
  failed (Native.discardThrough h 1) "unmanaged file in old segment silently unlinked"
  failed (Native.scan h) "uncertain release left a usable handle"
  Native.close h
  require ((← IO.FS.readFile unknown) == "keep") "deleted unrelated file during cleanup"
  failed (Native.openExisting dir) "ignored failed cleanup on reopen"
  -- Leave a partial retired directory after the release authority has settled.
  IO.FS.removeFile (dir / "segment-0" / "segment")
  IO.FS.removeFile unknown
  let h ← Native.openExisting dir
  check h 1 [[11]]
  require (!(← (dir / "segment-0").pathExists)) "retry failed to finish reclamation"
  Native.close h

private def invalidControl (dir : FilePath) : IO Unit := do
  let h ← Native.create dir .boundary 1
  Native.append h [7]
  Native.close h
  let path := dir / "CONTROL"
  let ok ← IO.FS.readBinFile path
  let body := "swal1 boundary 1 0 0".toUTF8
  require (ok == body ++ ⟨(checksumBytes body.data.toList).toArray⟩) "changed CONTROL wire format"
  let damaged := ok.set! (ok.size - 1) (ok[ok.size - 1]! ^^^ 1)
  IO.FS.writeBinFile path damaged
  failed (Native.openExisting dir) "opened a damaged authority record"
  require ((← IO.FS.readBinFile path) == damaged) "failed open rewrote corrupt authority"
  IO.FS.writeBinFile path ok
  IO.FS.writeFile (dir / "segment-0" / "policy") "v3 log"
  failed (Native.openExisting dir) "accepted a child using a different WAL policy"

private def freshOnly (dir : FilePath) : IO Unit := do
  IO.FS.writeFile (dir / "unrelated") "keep"
  failed (Native.create dir .logOnly 2) "create accepted a nonempty directory"
  require ((← IO.FS.readFile (dir / "unrelated")) == "keep") "create modified unrelated data"

def run : IO Unit := do
  for p in [Policy.logOnly, .boundary] do
    IO.FS.withTempDir fun dir => lifecycle dir p
    IO.FS.withTempDir fun dir => retryRotation dir p
    IO.FS.withTempDir fun dir => retryAfterRelease dir p
  IO.FS.withTempDir invalidControl
  IO.FS.withTempDir freshOnly
  IO.println "Segmented WAL native fixtures passed"

end WalRecoverySlice.Segmented.NativeTests

def main : IO Unit := WalRecoverySlice.Segmented.NativeTests.run
