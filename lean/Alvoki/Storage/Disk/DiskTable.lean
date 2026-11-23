import Alvoki.Storage.Disk.WalBoundary
import Alvoki.Storage.Disk.Manifest
import Alvoki.Storage.Publication.CheckpointPublication

namespace Alvoki.Storage
open System Alvoki.Compaction
open Alvoki.Sequential (SnapshotHandle SnapshotPin)

/-- The files the Linux disk protocol addresses within a database directory. -/
inductive DiskFile where
  | lock | wal | stagedWal | manifest | stagedManifest
  | walBoundary | stagedWalBoundary
  | run (generation : UInt64) (index : Nat)

private def DiskFile.name : DiskFile → String
  | .lock => "LOCK"
  | .wal => "WAL"
  | .stagedWal => "WAL.next"
  | .manifest => "MANIFEST"
  | .stagedManifest => "MANIFEST.next"
  | .walBoundary => "WAL.commit"
  | .stagedWalBoundary => "WAL.commit.next"
  | .run generation index => s!"run-{generation}-{index}.v3"

/-- A fixed absolute directory path for all operations in an open session. -/
structure DiskDirectory where
  private mk ::
  path : FilePath
  absolute : path.toString.startsWith '/'

def DiskDirectory.file (dir : DiskDirectory) (file : DiskFile) : FilePath :=
  ⟨dir.path.toString ++ "/" ++ file.name⟩

theorem DiskDirectory.file_absolute (dir : DiskDirectory) (file : DiskFile) :
    (dir.file file).toString.startsWith '/' := by
  obtain ⟨rest, pathEq⟩ := String.startsWith_char_iff_exists_append.mp dir.absolute
  apply String.startsWith_char_iff_exists_append.mpr
  exact ⟨rest ++ "/" ++ file.name, by simp [DiskDirectory.file, pathEq, String.append_assoc]⟩

/-- POSIX interpretation of an argument with respect to the working directory. -/
def resolveDiskPath (cwd path : FilePath) : FilePath :=
  if path.toString.startsWith '/' then path else cwd / path

theorem DiskDirectory.paths_independent_of_cwd (dir : DiskDirectory) (cwd : FilePath) :
    resolveDiskPath cwd dir.path = dir.path ∧
      ∀ file, resolveDiskPath cwd (dir.file file) = dir.file file := by
  exact ⟨by simp [resolveDiskPath, dir.absolute],
    fun file => by simp [resolveDiskPath, dir.file_absolute file]⟩

private def openDirectory (input : FilePath) : IO DiskDirectory := do
  let path ← IO.FS.realPath input
  if absolute : path.toString.startsWith '/' then
    return ⟨path, absolute⟩
  else
    throw (IO.userError s!"database path is not absolute: {path}")

private structure Installed where
  table : PackedTable
  generation : UInt64
  walBytes : Nat

private inductive Phase where
  | ready (installed : Installed)
  | poisoned
  | closed

/-- Linux adapter for a sequential caller. The lock excludes a second open
writer. An I/O failure during publication requires reopening the directory. -/
structure DiskTable where
  private mk ::
  private dir : DiskDirectory
  private lock : IO.FS.Handle
  private phase : IO.Ref Phase

private def fromOption (result : Option α) (message : String) : IO α :=
  match result with
  | some value => pure value
  | none => throw (IO.userError message)

private def syncPaths (paths : Array FilePath) : IO Unit := do
  let arguments := paths.map FilePath.toString
  let result ← IO.Process.output { cmd := "sync", args := #["--"] ++ arguments }
  if result.exitCode ≠ 0 then
    throw (IO.userError s!"sync failed for {arguments}: {result.stderr}")

private def syncPath (path : FilePath) : IO Unit := syncPaths #[path]

private def writeFlushed (path : FilePath) (content : ByteArray) : IO Unit := do
  let file ← IO.FS.Handle.mk path .write
  file.write content
  file.flush

private def performReplacement (dir : DiskDirectory) (stagedPath : FilePath) (active : DiskFile)
    (bytes : ByteArray) (alsoSync : Array FilePath) : Publication.Step → IO Unit
  | .writeStaged => writeFlushed stagedPath bytes
  | .syncStaged => syncPaths (alsoSync.push stagedPath)
  | .renameStaged => IO.FS.rename stagedPath (dir.file active)
  | .syncDirectory => syncPath dir.path

private def atomicReplace (dir : DiskDirectory) (staged active : DiskFile) (bytes : ByteArray)
    (alsoSync : Array FilePath := #[]) : IO Unit :=
  Publication.run (performReplacement dir (dir.file staged) active bytes alsoSync)

private def publishWalBoundary (dir : DiskDirectory) (bytes : Nat) (alsoSync : Array FilePath := #[]) : IO Unit :=
  atomicReplace dir .stagedWalBoundary .walBoundary (WAL.Boundary.encode bytes.toUInt64) alsoSync

private def checkpointHeader (table : PackedTable) (generation : UInt64) : Manifest.Checkpoint :=
  ⟨generation, table.committed, table.pins.floor, table.runs.length.toUInt64⟩

private def installRuns (runs : List CheckedRun) (header : Manifest.Checkpoint) :
    Except String PackedTable :=
  match PackedTable.restore runs header.committed header.floor with
  | none => .error "installed v3 runs exceed the manifest watermark"
  | some table => .ok table

/-- Validate the ordered file contents identified by a checkpoint. -/
def loadRunSet (header : Manifest.Checkpoint) (files : List ByteArray) : Except String PackedTable := do
  if files.length ≠ header.runCount.toNat then throw "installed run count differs from the manifest"
  let runs ← files.mapM CheckedRun.openBytes
  installRuns runs header

private theorem readWrittenRuns (runs : List CheckedRun) :
    (runs.map (·.run.bytes)).mapM CheckedRun.openBytes = Except.ok runs := by
  induction runs with
  | nil => rfl
  | cons run rest ih =>
    simp only [List.map_cons, List.mapM_cons, run.openOwnBytes]
    change Except.map (run :: ·) ((rest.map (·.run.bytes)).mapM CheckedRun.openBytes) = _
    rw [ih]
    rfl

theorem loadRunSet_written (header : Manifest.Checkpoint) (runs : List CheckedRun)
    (count : runs.length = header.runCount.toNat) (floor : header.floor ≤ header.committed)
    (bounded : ∀ run ∈ runs, ∀ row ∈ run.history.rows, row.sequence ≤ header.committed) :
    ∃ table, loadRunSet header (runs.map (·.run.bytes)) = .ok table ∧
      PackedTable.restore runs header.committed header.floor = some table := by
  obtain ⟨table, restored⟩ := PackedTable.restore_complete runs header.committed header.floor floor bounded
  refine ⟨table, ?_, restored⟩
  simp only [loadRunSet, List.length_map, count, ne_eq, not_true_eq_false, ↓reduceIte,
    readWrittenRuns]
  change installRuns runs header = .ok table
  simp [installRuns, restored]

/-- Reconstruct the committed data from the file contents emitted for a
flushed checkpoint, independently of the old session's pin registry. -/
theorem recoverRunSet_written {checkpoint committed : PackedTable} (generation : UInt64)
    (fits : checkpoint.runs.length < UInt64.size)
    (flushed : checkpoint.memory = Alvoki.Sequential.History.empty)
    (floor : checkpoint.pins.floor ≤ checkpoint.committed)
    (bounded : ∀ run ∈ checkpoint.runs, ∀ row ∈ run.history.rows, row.sequence ≤ checkpoint.committed)
    (covered pending : List WAL.Write)
    (old : ∀ event ∈ covered, event.sequence ≤ checkpoint.committed)
    (new : ∀ event ∈ pending, checkpoint.committed < event.sequence)
    (applied : replay checkpoint pending = .ok committed)
    (tail : ByteArray) (incomplete : tail.size < WAL.frameSize) :
    let header := checkpointHeader checkpoint generation
    let files := checkpoint.runs.map (·.run.bytes)
    let wal := WAL.encode (covered ++ pending) ++ tail
    ∃ reopened, (do
      let manifest ← Manifest.decode (Manifest.encode header)
      let base ← loadRunSet manifest files
      recoverCheckpoint base wal) = .ok reopened ∧ reopened.SameData committed := by
  dsimp only
  let header := checkpointHeader checkpoint generation
  let files := checkpoint.runs.map (fun run => run.run.bytes)
  let wal := WAL.encode (covered ++ pending) ++ tail
  have count : checkpoint.runs.length = header.runCount.toNat :=
    (UInt64.toNat_ofNat_of_lt' fits).symm
  obtain ⟨restored, loads, physical⟩ := loadRunSet_written header checkpoint.runs count floor bounded
  have manifest : Manifest.decode (Manifest.encode header) = .ok header :=
    Manifest.decode_encode header floor
  change ∃ reopened, (do
    let manifest ← Manifest.decode (Manifest.encode header)
    let base ← loadRunSet manifest files
    recoverCheckpoint base wal) = .ok reopened ∧ reopened.SameData committed
  obtain ⟨reopened, recovered, same⟩ :=
    recoverPublished flushed physical covered pending old new applied tail incomplete
  refine ⟨reopened, ?_, same⟩
  rw [manifest]
  change (do
    let base ← loadRunSet header files
    recoverCheckpoint base wal) = .ok reopened
  change loadRunSet header files = .ok restored at loads
  rw [loads]
  exact recovered

/-- The exact checkpoint and durable WAL bytes pass the native loader and
frame-count guard. Bytes beyond the durable marker do not affect either. -/
theorem recoverRunSet_committedBoundary {checkpoint committed : PackedTable} (generation : UInt64)
    (fits : checkpoint.runs.length < UInt64.size)
    (flushed : checkpoint.memory = Alvoki.Sequential.History.empty)
    (floor : checkpoint.pins.floor ≤ checkpoint.committed)
    (bounded : ∀ run ∈ checkpoint.runs, ∀ row ∈ run.history.rows, row.sequence ≤ checkpoint.committed)
    (covered pending : List WAL.Write)
    (ordinals : WAL.OrdinalsFrom 1 (covered ++ pending))
    (count : covered.length = checkpoint.committed.toNat)
    (applied : replay checkpoint pending = .ok committed) (tail : ByteArray)
    (walFits : (WAL.encode (covered ++ pending)).size < UInt64.size) :
    let header := checkpointHeader checkpoint generation
    let files := checkpoint.runs.map (·.run.bytes)
    let wal := WAL.encode (covered ++ pending)
    ∃ restored reopened,
      loadRunSet header files = .ok restored ∧
      WAL.Boundary.select wal.size.toUInt64 (wal ++ tail) = .ok wal ∧
      recoverSelected restored wal = .ok reopened ∧
      reopened.SameData committed := by
  let header := checkpointHeader checkpoint generation
  have runCount : checkpoint.runs.length = header.runCount.toNat :=
    (UInt64.toNat_ofNat_of_lt' fits).symm
  obtain ⟨restored, loads, physical⟩ := loadRunSet_written header checkpoint.runs runCount floor bounded
  have same := PackedTable.restore_sameData flushed physical
  obtain ⟨reopened, replayed, reference⟩ := replay_sameData same pending applied
  have accepted := recoverSelected_encoded restored covered pending ordinals
    (by simpa only [same.committed] using count)
  exact ⟨restored, reopened, loads, WAL.Boundary.select_encoded (covered ++ pending) tail walFits,
    accepted.trans replayed, reference⟩

private def readOptionalFile (path : FilePath) : IO (Option ByteArray) := do
  match ← path.symlinkMetadata.toBaseIO with
  | .ok metadata =>
    unless metadata.type == .file do
      throw (IO.userError s!"expected a regular database file: '{path}'")
    return some (← IO.FS.readBinFile path)
  | .error error@(.noFileOrDirectory _ osCode _) =>
    -- Linux ENOENT identifies a missing directory entry.
    if osCode == 2 then return none else throw error
  | .error error => throw error

private def openCheckpoint (dir : DiskDirectory) : IO (Option (PackedTable × UInt64)) := do
  let manifestPath := dir.file .manifest
  let some header ← readOptionalFile manifestPath | return none
  let manifest ← IO.ofExcept (Manifest.decode header)
  let mut files : Array ByteArray := #[]
  for index in [:manifest.runCount.toNat] do
    files := files.push (← IO.FS.readBinFile (dir.file (.run manifest.generation index)))
  let table ← IO.ofExcept (loadRunSet manifest files.toList)
  return some (table, manifest.generation)

private def openLocked (dir : DiskDirectory) (lock : IO.FS.Handle) : IO DiskTable := do
  let checkpoint ← openCheckpoint dir
  let (checkpointTable, checkpointGeneration) := checkpoint.getD (.empty, 0)
  let walPath := dir.file .wal
  let boundary ← (← readOptionalFile (dir.file .walBoundary)).mapM fun bytes =>
    IO.ofExcept (WAL.Boundary.decode bytes)
  let bytes ← match ← readOptionalFile walPath with
    | some bytes => pure bytes
    | none =>
      if checkpoint.isSome || boundary.isSome then
        throw (IO.userError "installed checkpoint or boundary is missing its WAL")
      writeFlushed walPath ByteArray.empty
      pure ByteArray.empty
  let selected ← match boundary with
    | some count => IO.ofExcept (WAL.Boundary.select count bytes)
    | none => pure ((WAL.repairPrefix bytes).getD bytes)
  let table ← IO.ofExcept (recoverSelected checkpointTable selected)
  -- Both paths sync the directory to settle the visible checkpoint and WAL marker,
  -- including any rename reached by a prior process before its directory sync.
  if selected.size < bytes.size then
    atomicReplace dir .stagedWal .wal selected
  else
    syncPaths #[walPath, dir.path]
  -- Bootstrap an empty or legacy WAL only after its selected prefix is durable.
  if boundary.isNone then
    unless selected.size < UInt64.size do throw (IO.userError "WAL byte count is too large")
    publishWalBoundary dir selected.size
  let installed : Installed := { table, generation := checkpointGeneration, walBytes := selected.size }
  return ⟨dir, lock, ← IO.mkRef (.ready installed)⟩

/-- Open a database in an existing directory and replay its durable WAL. -/
def DiskTable.open (path : FilePath) : IO DiskTable := do
  let dir ← openDirectory path
  let lock ← IO.FS.Handle.mk (dir.file .lock) .append
  unless ← lock.tryLock do throw (IO.userError s!"database already open: {dir.path}")
  try openLocked dir lock catch error =>
    lock.unlock
    throw error

def DiskTable.close (db : DiskTable) : IO Unit := do
  match ← db.phase.get with
  | .closed => pure ()
  | _ =>
    db.lock.unlock
    db.phase.set .closed

private def DiskTable.installed (db : DiskTable) : IO Installed := do
  match ← db.phase.get with
  | .ready value => pure value
  | .poisoned => throw (IO.userError "publication failed; reopen the database")
  | .closed => throw (IO.userError "database is closed")

/-- Acknowledgement follows the WAL sync and durable publication of the byte boundary. -/
def DiskTable.write (db : DiskTable) (key : UInt64) (value : Option UInt64) : IO UInt64 := do
  let state ← db.installed
  let (event, table) ← fromOption (prepareWrite state.table key value) "write sequence space exhausted"
  let walBytes := state.walBytes + WAL.frameSize
  unless walBytes < UInt64.size do throw (IO.userError "WAL byte count is too large")
  db.phase.set .poisoned
  let walPath := db.dir.file .wal
  WAL.Boundary.commit (do
    let wal ← IO.FS.Handle.mk walPath .append
    wal.write (WAL.encodeFrame event)
    wal.flush) (publishWalBoundary db.dir walBytes #[walPath])
  db.phase.set (.ready { state with table, walBytes })
  return event.sequence

def DiskTable.acquireAt (db : DiskTable) (snapshot : UInt64) : IO (Option SnapshotPin) := do
  let state ← db.installed
  match state.table.acquireAt snapshot with
  | none => return none
  | some (pin, table) =>
    db.phase.set (.ready { state with table })
    return some pin

def DiskTable.acquire (db : DiskTable) : IO SnapshotPin := do
  let state ← db.installed
  fromOption (← db.acquireAt state.table.committed) "cannot acquire the latest snapshot"

def DiskTable.release (db : DiskTable) (handle : SnapshotHandle) : IO Unit := do
  let state ← db.installed
  db.phase.set (.ready { state with table := state.table.release handle })

def DiskTable.lookup (db : DiskTable) (handle : SnapshotHandle) (key : UInt64) :
    IO (Option (Option UInt64)) := do
  return (← db.installed).table.lookup handle key

def DiskTable.range (db : DiskTable) (handle : SnapshotHandle) (lo hi : UInt64) :
    IO (Option (List (Alvoki.Compaction.Model.Entry (Option UInt64)))) := do
  return (← db.installed).table.range handle lo hi

def DiskTable.advanceFloor (db : DiskTable) (floor : UInt64) : IO Bool := do
  let state ← db.installed
  let some table := state.table.advanceFloor floor | return false
  db.phase.set (.ready { state with table })
  return true

def DiskTable.compact (db : DiskTable) (index : Nat) : IO Bool := do
  let state ← db.installed
  let some table := state.table.compact index | return false
  db.phase.set (.ready { state with table })
  return true

/-- Flush pending writes and publish a fresh generation. All previous run
files and WAL frames remain available through interrupted publication. -/
def DiskTable.checkpoint (db : DiskTable) : IO Unit := do
  let state ← db.installed
  let table ← if state.table.memory.rows.isEmpty then pure state.table else IO.ofExcept state.table.flush
  let count := table.runs.length
  let next := state.generation.toNat + 1
  unless next < UInt64.size ∧ count < UInt64.size do
    throw (IO.userError "checkpoint generation or run count is too large")
  let generation := UInt64.ofNat next
  let runs := table.runs.toArray
  let manifestBytes := Manifest.encode (checkpointHeader table generation)
  let stagedManifest := db.dir.file .stagedManifest
  db.phase.set .poisoned
  CheckpointPublication.run runs.size fun
    | .writeRun index => do
      let run ← fromOption runs[index]? "checkpoint run index is out of bounds"
      writeFlushed (db.dir.file (.run generation index)) run.run.bytes
    | .syncRun index => syncPath (db.dir.file (.run generation index))
    | .syncRunsDirectory => syncPath db.dir.path
    | .manifest step => performReplacement db.dir stagedManifest .manifest manifestBytes #[] step
  db.phase.set (.ready { state with table, generation })

end Alvoki.Storage
