import Alvoki.Storage.Disk.CachedOpenRejection

namespace Alvoki.Storage

open System

private def keepDirectoryName (name : String) : Bool := name != "." && name != ".."

/-- Consecutive non-null results from one opened directory stream, followed
by the terminal null result and the reached close report. A successful
terminal report means that the checked read left errno zero. Errors are
the decoded errors of the reached calls. -/
structure OpenedDirectoryScan where
  names : List String
  terminal : Except IO.Error Unit
  closed : Except IO.Error Unit

def OpenedDirectoryScan.visibleNames (scan : OpenedDirectoryScan) : List String :=
  scan.names.filter keepDirectoryName

private def appendDirectoryEntry (path : FilePath) (entries : Array IO.FS.DirEntry) (name : String) :
    Array IO.FS.DirEntry :=
  if keepDirectoryName name then entries.push ⟨path, name⟩ else entries

private theorem appendDirectoryEntries_toList (path : FilePath) (names : List String)
    (entries : Array IO.FS.DirEntry) :
    (names.foldl (appendDirectoryEntry path) entries).toList =
      entries.toList ++ (names.filter keepDirectoryName).map (IO.FS.DirEntry.mk path) := by
  induction names generalizing entries with
  | nil => simp
  | cons name names ih =>
    rw [List.foldl_cons, ih]
    cases kept : keepDirectoryName name <;>
      simp [appendDirectoryEntry, kept, List.append_assoc]

def OpenedDirectoryScan.entries (scan : OpenedDirectoryScan) (path : FilePath) : Array IO.FS.DirEntry :=
  scan.names.foldl (appendDirectoryEntry path) #[]

theorem OpenedDirectoryScan.entries_toList (scan : OpenedDirectoryScan) (path : FilePath) :
    (scan.entries path).toList = scan.visibleNames.map (IO.FS.DirEntry.mk path) := by
  simpa [entries, visibleNames] using appendDirectoryEntries_toList path scan.names #[]

theorem OpenedDirectoryScan.entries_size (scan : OpenedDirectoryScan) (path : FilePath) :
    (scan.entries path).size = scan.visibleNames.length := by
  simpa using congrArg List.length (scan.entries_toList path)

/-- Outcomes at the boundary of the checked native listing. The invalid
path report means that its C string check found an embedded NUL. -/
inductive CheckedDirectoryReadReport where
  | invalidPath
  | openError (cause : IO.Error)
  | scanned (scan : OpenedDirectoryScan)

/-- Model the native return. A read error takes precedence over a close
error. In both cases the materialized prefix is dropped. -/
def CheckedDirectoryReadReport.result (report : CheckedDirectoryReadReport) (path : FilePath) :
    Except IO.Error (Array IO.FS.DirEntry) :=
  match report with
  | .invalidPath => .error (.invalidArgument (some path.toString) 22 "string contains NUL bytes")
  | .openError cause => .error cause
  | .scanned scan => do
    scan.terminal
    scan.closed
    pure (scan.entries path)

theorem CheckedDirectoryReadReport.scan_readError {scan : OpenedDirectoryScan} (path : FilePath)
    {cause : IO.Error} (readError : scan.terminal = .error cause) :
    (CheckedDirectoryReadReport.scanned scan).result path = .error cause := by
  simp [result, readError, Bind.bind, Except.bind]

theorem CheckedDirectoryReadReport.scan_closeError {scan : OpenedDirectoryScan} (path : FilePath)
    (eof : scan.terminal = .ok ()) {cause : IO.Error} (closeError : scan.closed = .error cause) :
    (CheckedDirectoryReadReport.scanned scan).result path = .error cause := by
  simp [result, eof, closeError, Bind.bind, Except.bind]

/-- The successful return contains exactly the names observed before EOF,
in stream order. A complete EOF report on the stable directory supplies
the namespace permutation. -/
theorem CheckedDirectoryReadReport.scan_complete {scan : OpenedDirectoryScan} (path : FilePath)
    {names : List String} (eof : scan.terminal = .ok ()) (closed : scan.closed = .ok ())
    (complete : scan.visibleNames.Perm names) :
    (CheckedDirectoryReadReport.scanned scan).result path = .ok (scan.entries path) ∧
      ((scan.entries path).toList.map (·.fileName)).Perm names := by
  refine ⟨by simp [result, eof, closed, Bind.bind, Except.bind, Pure.pure, Except.pure], ?_⟩
  simpa [scan.entries_toList, List.map_map, Function.comp_def] using complete

structure DirectoryReadWork where
  opendirCalls : Nat
  readdirCalls : Nat
  closedirCalls : Nat
  materializedEntries : Nat

/-- Charge the reached calls, including terminal failure and the close
attempt. Each retained name is materialized once even if the array is
later discarded. -/
def CheckedDirectoryReadReport.work : CheckedDirectoryReadReport → DirectoryReadWork
  | .invalidPath => ⟨0, 0, 0, 0⟩
  | .openError _ => ⟨1, 0, 0, 0⟩
  | .scanned scan => ⟨1, scan.names.length + 1, 1, scan.visibleNames.length⟩

theorem CheckedDirectoryReadReport.materialized_le_reads (report : CheckedDirectoryReadReport) :
    report.work.materializedEntries ≤ report.work.readdirCalls := by
  cases report with
  | invalidPath | openError => exact Nat.le_refl _
  | scanned scan =>
    exact Nat.le_trans (List.length_filter_le ..) (Nat.le_succ scan.names.length)

/-- Only materialized entries from a successful whole listing can feed
canonical WAL names to the cached worker's request budget. -/
theorem CheckedDirectoryReadReport.listedWalNames_le_materialized (report : CheckedDirectoryReadReport)
    (path : FilePath) :
    WalSegmentRepair.listedWalNames (report.result path) ≤ report.work.materializedEntries := by
  cases report with
  | invalidPath | openError => exact Nat.le_refl _
  | scanned scan =>
    cases terminal : scan.terminal <;> cases closed : scan.closed <;>
      simp [result, work, terminal, closed, Bind.bind, Except.bind, Pure.pure, Except.pure,
        WalSegmentRepair.listedWalNames, scan.entries_toList, List.map_map, Function.comp_def,
        List.length_filterMap_le]

end Alvoki.Storage

namespace Alvoki.Storage.DiskSession

open WalSegmentRepair
open WAL (frameSize)

/-- Once the cached worker reaches its checked listing, a reported scan
error preserves the file image and stops before any entry metadata or WAL
payload read. The existing rejection contract supplies the lock cleanup. -/
def CachedOpenRejection.ofDirectoryReadError {directory : DiskDirectory}
    {before : LockedFileState FileImage} (attempt : CachedOpenAttempt directory before)
    {checkpoint : Option (PackedTable × UInt64)}
    (checkpointRead : readIntegrityCheckpointSized directory (attempt.readOptional (directory.file .manifest))
      attempt.readRunSize attempt.readRunPrefix before.image = .ok checkpoint before.image)
    {marker : ByteArray} (markerRead : attempt.readOptional (directory.file .walBoundary) before.image =
      .ok (some marker) before.image)
    {length : UInt64} (decoded : WAL.Boundary.decode marker = .ok length)
    (valid : length.toNat % frameSize = 0 ∧ (checkpoint.getD (.empty, 0)).1.committed.toNat ≤ length.toNat / frameSize)
    (report : CheckedDirectoryReadReport)
    (listed : attempt.list directory.path before.image =
      (liftExcept (report.result directory.path) : EStateM IO.Error FileImage _) before.image)
    {cause : IO.Error} (failed : report.result directory.path = .error cause) :
    CachedOpenRejection directory before := by
  have listError : attempt.list directory.path before.image = .error cause before.image := by
    rw [listed, failed]
    rfl
  refine ⟨attempt, cause, ?_⟩
  simp [CachedOpenAttempt.prepare, prepareBoundedMarkedFromReaders, readSelectedWithCachedExtents,
    checkpointRead, markerRead, decoded, valid, listError, Bind.bind, EStateM.bind, liftExcept,
    Except.mapError, Pure.pure, EStateM.pure]

end Alvoki.Storage.DiskSession
