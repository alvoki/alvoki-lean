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

private def appendAt (h : Native.Handle) (batch : Bytes) (expected : Nat) : IO Unit := do
  let position ← Native.append h batch
  require (position == expected) s!"expected position {expected}, got {position}"

private def lifecycle (dir : FilePath) (p : Policy) : IO Unit := do
  let h ← Native.create dir p 2
  failed (Native.openExisting dir) "admitted two handles for the same directory"
  appendAt h [1] 1
  appendAt h [2] 2
  -- An interrupted successor preparation can leave a directory with incomplete child files.
  IO.FS.createDir (dir / "segment-1")
  IO.FS.writeFile (dir / "segment-1" / "policy") "incomplete"
  appendAt h [3] 3
  appendAt h [4] 4
  appendAt h [5] 5
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
  appendAt h [6] 6
  check h 5 [[6]]
  Native.close h
  let h ← Native.openExisting dir
  check h 5 [[6]]
  Native.close h

private def retryRotation (dir : FilePath) (p : Policy) : IO Unit := do
  let h ← Native.create dir p 1
  appendAt h [1] 1
  let previous ← IO.FS.readBinFile (dir / "CONTROL")
  IO.FS.createDir (dir / "CONTROL.next")
  failed (Native.append h [2]) "rotation overwrote an invalid staging binding"
  require ((← IO.FS.readBinFile (dir / "CONTROL")) == previous) "failed staging changed control"
  require (← (dir / "segment-1").pathExists) "expected the prepared unpublished successor"
  let successor ← SingleFile.openExisting (dir / "segment-1")
  SingleFile.close successor
  Native.close h
  IO.FS.removeDir (dir / "CONTROL.next")
  let h ← Native.openExisting dir
  check h 0 [[1]]
  appendAt h [3] 2
  Native.close h
  let h ← Native.openExisting dir
  check h 0 [[1], [3]]
  Native.close h

private def retryAfterRelease (dir : FilePath) (p : Policy) : IO Unit := do
  let h ← Native.create dir p 1
  appendAt h [10] 1
  appendAt h [11] 2
  let unknown := dir / "segment-0" / "unmanaged"
  IO.FS.writeFile unknown "keep"
  failed (Native.discardThrough h 1) "unmanaged file in old segment silently unlinked"
  failed (Native.scan h) "uncertain release left a usable handle"
  Native.close h
  require ((← IO.FS.readFile unknown) == "keep") "deleted unrelated file during cleanup"
  failed (Native.openExisting dir) "ignored failed cleanup on reopen"
  let child ← SingleFile.openExisting (dir / "segment-1")
  SingleFile.close child
  -- Leave a partial retired directory after the release authority has settled.
  IO.FS.removeFile (dir / "segment-0" / "segment")
  IO.FS.removeFile unknown
  let h ← Native.openExisting dir
  check h 1 [[11]]
  require (!(← (dir / "segment-0").pathExists)) "retry failed to finish reclamation"
  Native.close h

private def activeScope : IO Unit := do
  let events ← IO.mkRef ([] : List String)
  let child := 37
  let close (reached : Nat) : IO Unit := do
    require (reached == child) "cleanup received a different child"
    events.modify (· ++ ["child close"])
    throw <| IO.userError "reported child close error"
  let action : IO Unit := withActiveChild (error := IO.Error) (pure child) close fun reached => do
    require (reached == child) "continuation received a different child"
    events.modify (· ++ ["continuation"])
    throw <| IO.userError "reported collection error"
  let result ← (releaseWith (error := IO.Error) action (do
    events.modify (· ++ ["root unlock"])
    throw <| IO.userError "reported root unlock error")).toBaseIO
  match result with
  | .error err => require (err.toString == "reported collection error") "cleanup replaced the primary error"
  | .ok () => throw <| IO.userError "failed continuation returned a handle"
  require ((← events.get) == ["continuation", "child close", "root unlock"])
    "root unlock did not follow failed child close"
  let transferred ← withActiveChild (error := IO.Error) (pure child) close pure
  require (transferred == child) "success transferred a different child"
  require ((← events.get) == ["continuation", "child close", "root unlock"])
    "successful transfer closed the active child"

@[extern "alvoki_test_fail_installed_read"]
private opaque failInstalledRead (_ : Unit) : IO Unit

private def scansAndFolds (dir : FilePath) (p : Policy) : IO Unit := do
  let h ← Native.create dir p 2
  for pos in [1:7] do appendAt h [pos.toUInt8] pos
  Native.discardThrough h 3
  require ((← Native.bounds h) == ⟨3, 6⟩) "incorrect initial bounds"
  let controlBefore ← IO.FS.readBinFile (dir / "CONTROL")
  let activePath := dir / "segment-2" / "segment"
  let dataBefore ← IO.FS.readBinFile activePath
  failInstalledRead ()
  let read ← (Native.scanFold h () (fun _ _ _ => ())).toBaseIO
  require (read matches .error (.hardwareFault _ _)) "expected late active read error"
  require ((← Native.bounds h) == ⟨3, 6⟩) "scan error changed ready bounds"
  require ((← IO.FS.readBinFile (dir / "CONTROL")) == controlBefore &&
      (← IO.FS.readBinFile activePath) == dataBefore) "scan error changed disk"
  failed (Native.openExisting dir) "scan error released root custody"
  failed (SingleFile.openExisting (dir / "segment-2")) "scan error released child custody"
  let collect := fun (acc : List (Nat × Bytes)) pos batch => (pos, batch) :: acc
  let (bounds, seen) ← Native.scanFold h [] collect
  require (bounds == ⟨3, 6⟩ && seen.reverse == [(4, [4]), (5, [5]), (6, [6])])
    "scan fold used wrong retained positions"
  appendAt h [7] 7
  Native.close h
  for _ in [:2] do
    let (reopened, bounds, folded) ← Native.openExistingFold dir [] collect
    require (bounds == ⟨3, 7⟩ && folded.reverse == [(4, [4]), (5, [5]), (6, [6]), (7, [7])])
      "recovery fold used wrong retained positions"
    check reopened 3 [[4], [5], [6], [7]]
    Native.close reopened

private def invalidControl (dir : FilePath) : IO Unit := do
  let h ← Native.create dir .boundary 1
  appendAt h [7] 1
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
  IO.FS.writeFile (dir / "segment-0" / "policy") "v3 boundary"
  let h ← Native.openExisting dir
  check h 0 [[7]]
  Native.close h

private def freshOnly (dir : FilePath) : IO Unit := do
  IO.FS.writeFile (dir / "unrelated") "keep"
  failed (Native.create dir .logOnly 2) "create accepted a nonempty directory"
  require ((← IO.FS.readFile (dir / "unrelated")) == "keep") "create modified unrelated data"

def run : IO Unit := do
  activeScope
  for p in [Policy.logOnly, .boundary] do
    IO.FS.withTempDir fun dir => lifecycle dir p
    IO.FS.withTempDir fun dir => retryRotation dir p
    IO.FS.withTempDir fun dir => retryAfterRelease dir p
    IO.FS.withTempDir fun dir => scansAndFolds dir p
  IO.FS.withTempDir invalidControl
  IO.FS.withTempDir freshOnly
  IO.println "Segmented WAL native fixtures passed"

end WalRecoverySlice.Segmented.NativeTests

def main : IO Unit := WalRecoverySlice.Segmented.NativeTests.run
