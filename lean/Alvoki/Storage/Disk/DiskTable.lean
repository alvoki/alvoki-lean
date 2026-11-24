import Alvoki.Storage.Disk.WalBoundary
import Alvoki.Storage.Disk.Manifest
import Alvoki.Storage.Disk.DiskSession
import Alvoki.Storage.Publication.CheckpointPublication

namespace Alvoki.Storage
open System Alvoki.Compaction
open Alvoki.Sequential (SnapshotHandle)

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

private abbrev Phase := DiskSession.Phase Installed

/-- An opaque snapshot handle tied to the open disk session that issued it. -/
structure DiskSnapshotHandle where
  private mk ::
  private session : IO.Ref Unit
  private localHandle : SnapshotHandle

structure DiskSnapshotPin where
  private mk ::
  handle : DiskSnapshotHandle
  sequence : UInt64

/-- Linux adapter for a sequential caller. The lock excludes a second open
writer. An I/O failure during publication requires reopening the directory. -/
structure DiskTable where
  private mk ::
  private dir : DiskDirectory
  private lock : IO.FS.Handle
  private phase : IO.Ref Phase
  private session : IO.Ref Unit

private def fromOption (result : Option α) (message : String) : IO α :=
  match result with
  | some value => pure value
  | none => throw (IO.userError message)

private def syncPaths (paths : Array FilePath) : IO Unit := do
  let arguments := paths.map FilePath.toString
  let result ← IO.Process.output { cmd := "sync", args := #["--"] ++ arguments }
  if result.exitCode ≠ 0 then
    throw (IO.userError s!"sync failed for {arguments}: {result.stderr}")

private def writeFlushed (path : FilePath) (content : ByteArray) : IO Unit := do
  let file ← IO.FS.Handle.mk path .write
  file.write content
  file.flush

private def performReplacement (dir : DiskDirectory) (stagedPath : FilePath) (active : DiskFile)
    (bytes : ByteArray) (alsoSync : Array FilePath) (step : Publication.Step) : IO Unit :=
  Publication.performReplacement (writeFlushed · bytes) syncPaths IO.FS.rename
    stagedPath dir.path (fun _ => dir.file active) alsoSync step

private def atomicReplace (dir : DiskDirectory) (staged active : DiskFile) (bytes : ByteArray)
    (alsoSync : Array FilePath := #[]) : IO Unit :=
  Publication.run (performReplacement dir (dir.file staged) active bytes alsoSync)

private def publishWalBoundary (dir : DiskDirectory) (bytes : Nat) (alsoSync : Array FilePath := #[]) : IO Unit :=
  atomicReplace dir .stagedWalBoundary .walBoundary (WAL.Boundary.encode bytes.toUInt64) alsoSync

/-- The manifest fields for the exact run order published by a checkpoint. -/
def checkpointHeader (table : PackedTable) (generation : UInt64) : Manifest.Checkpoint :=
  ⟨generation, table.committed, table.pins.floor, table.runs.length.toUInt64⟩

/-- Flush pending rows when preparing a checkpoint, keeping an already
flushed table's run order and avoiding an extra empty run. -/
@[macro_inline] def flushForCheckpoint [Monad m] (table : PackedTable)
    (validate : Except String PackedTable → m PackedTable) : m PackedTable :=
  if table.memory.rows.isEmpty then pure table else validate table.flush

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

/-- A loaded checkpoint starts a new session with no active snapshot pins. -/
theorem loadRunSet_clearsPins {header : Manifest.Checkpoint} {files : List ByteArray}
    {table : PackedTable} (loaded : loadRunSet header files = .ok table) :
    table.pins.active = [] := by
  unfold loadRunSet at loaded
  split at loaded
  · contradiction
  · cases decoded : files.mapM CheckedRun.openBytes with
    | error => rw [decoded] at loaded; contradiction
    | ok runs =>
      rw [decoded] at loaded
      change installRuns runs header = Except.ok table at loaded
      unfold installRuns at loaded
      split at loaded
      · contradiction
      · rename_i restored restoredEq
        cases loaded
        exact (PackedTable.restore_spec restoredEq).2.2.2.2

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

/-- Look up a directory entry before reading it. Only a missing entry
reported by the lookup can supply an absent database file. -/
@[macro_inline] def readOptionalDatabaseFile [Monad m]
    (lookup : m (Except IO.Error IO.FS.Metadata)) (read : Unit → m ByteArray)
    (notRegular : Unit → IO.Error) (fail : IO.Error → m (Option ByteArray)) :
    m (Option ByteArray) := do
  match ← lookup with
  | .ok metadata =>
    unless metadata.type == .file do
      return ← fail (notRegular ())
    return some (← read ())
  | .error error@(.noFileOrDirectory _ osCode _) =>
    -- Linux ENOENT identifies a missing directory entry.
    if osCode == 2 then return none else fail error
  | .error error => fail error

private def readOptionalFile (path : FilePath) : IO (Option ByteArray) :=
  readOptionalDatabaseFile path.symlinkMetadata.toBaseIO (fun _ => IO.FS.readBinFile path)
    (fun _ => IO.userError s!"expected a regular database file: '{path}'") throw

/-- Read the manifest's run files in increasing index order. Grow the array
as reads succeed since the run count comes from on-disk input. -/
@[inline] def readCheckpointRunBytes [Monad m] (read : UInt64 → Nat → m ByteArray)
    (manifest : Manifest.Checkpoint) : m (List ByteArray) := do
  let mut files : Array ByteArray := #[]
  for index in [:manifest.runCount.toNat] do
    files := files.push (← read manifest.generation index)
  return files.toList

/-- Read and validate the selected checkpoint before inspecting the WAL. -/
@[inline] def readCheckpoint [Monad m] (readManifest : m (Option ByteArray))
    (readRun : UInt64 → Nat → m ByteArray) (validate : {α : Type} → Except String α → m α) :
    m (Option (PackedTable × UInt64)) := do
  let some header ← readManifest | return none
  let manifest ← validate (Manifest.decode header)
  let files ← readCheckpointRunBytes readRun manifest
  let table ← validate (loadRunSet manifest files)
  return some (table, manifest.generation)

private def openCheckpoint (dir : DiskDirectory) : IO (Option (PackedTable × UInt64)) :=
  readCheckpoint (readOptionalFile (dir.file .manifest))
    (fun generation index => IO.FS.readBinFile (dir.file (.run generation index))) IO.ofExcept

/-- After loading the checkpoint, read and validate the WAL, settle its
selected prefix, and publish a missing marker before installing the session.
Keep the file operations and the final installation in their callers. -/
@[macro_inline] def withRecoveredOpen [Monad m] {α : Type}
    (checkpoint : Option (PackedTable × UInt64)) (readMarker readWal : m (Option ByteArray))
    (validate : {β : Type} → Except String β → m β) (fail : {β : Type} → String → m β)
    (createWal : Unit → m Unit)
    (repairWal : ByteArray → m Unit) (syncWal : Unit → m Unit) (publishMarker : Nat → m Unit)
    (install : PackedTable → UInt64 → Nat → m α) : m α := do
  let (base, generation) := checkpoint.getD (.empty, 0)
  WAL.Boundary.withOpenWal readMarker readWal validate (fun boundary => do
    if checkpoint.isSome || boundary.isSome then
      fail WAL.Boundary.missingOpenWal
    else
      createWal ()
      pure ByteArray.empty) fun boundary bytes => do
    let (selected, table) ← validate <| match boundary with
      | some count => WAL.Boundary.recoverMarked base count bytes
      | none => recoverLegacy base bytes
    -- Both paths settle the visible checkpoint and marker before installation.
    let table ← Publication.finishReopen bytes.size selected.size
      (fun _ => repairWal selected) syncWal table
    if boundary.isNone then
      unless selected.size < UInt64.size do fail "WAL byte count is too large"
      publishMarker selected.size
    install table generation selected.size

private def openLocked (dir : DiskDirectory) (lock : IO.FS.Handle) : IO DiskTable := do
  let checkpoint ← openCheckpoint dir
  let walPath := dir.file .wal
  withRecoveredOpen checkpoint (readOptionalFile (dir.file .walBoundary)) (readOptionalFile walPath)
    IO.ofExcept (fun message => throw (IO.userError message)) (fun _ => writeFlushed walPath ByteArray.empty)
    (fun selected => atomicReplace dir .stagedWal .wal selected) (fun _ => syncPaths #[walPath, dir.path])
    (fun length => publishWalBoundary dir length) fun table generation walBytes => do
    let installed : Installed := { table, generation, walBytes }
    -- ST.Ref.ptrEq distinguishes allocations. Keeping a separate cell lets a
    -- stale handle retain its identity without retaining the database state.
    return ⟨dir, lock, ← IO.mkRef (.ready installed), ← IO.mkRef ()⟩

/-- Open a database in an existing directory and replay its durable WAL. -/
def DiskTable.open (path : FilePath) : IO DiskTable := do
  let dir ← openDirectory path
  let lock ← IO.FS.Handle.mk (dir.file .lock) .append
  DiskSession.openWithLock lock.tryLock (fun _ => IO.userError s!"database already open: {dir.path}")
    (fun _ => lock.unlock) (fun _ => openLocked dir lock)

def DiskTable.close (db : DiskTable) : IO Unit := do
  (← db.phase.get).close (fun _ => db.lock.unlock) (fun _ => db.phase.set .closed)

private def DiskTable.installed (db : DiskTable) : IO Installed := do
  (← db.phase.get).installed

/-- The outcome of a failed write at the WAL mutation boundary. -/
inductive DiskWriteError where
  /-- This submission was rejected before attempting to append a WAL frame. -/
  | rejected (cause : IO.Error)
  /-- WAL mutation was attempted. The write may be recovered after reopening. -/
  | commitUnknown (cause : IO.Error)

/-- Commit the prepared frame to the WAL and publish the new byte count. -/
@[macro_inline] def commitWalWrite (dir : DiskDirectory) (event : WAL.Write)
    (walBytes : Nat) : IO Unit :=
  let walPath := dir.file .wal
  WAL.Boundary.commit (do
    let wal ← IO.FS.Handle.mk walPath .append
    wal.write (WAL.encodeFrame event)
    wal.flush) (publishWalBoundary dir walBytes #[walPath])

/-- The native commit uses the same append-first schedule and marker steps as
the write-effects model. The sync callback covers the WAL and staged marker
in one call. Filesystem reports determine which of those effects persisted. -/
theorem commitWalWrite_fileEffects (dir : DiskDirectory) (event : WAL.Write) (walBytes : Nat) :
    commitWalWrite dir event walBytes =
    WAL.Boundary.commit (do
      let wal ← IO.FS.Handle.mk (dir.file .wal) .append
      wal.write (WAL.encodeFrame event)
      wal.flush) (do
      let stagedPath := dir.file .stagedWalBoundary
      (do
        let staged ← IO.FS.Handle.mk stagedPath .write
        staged.write (WAL.Boundary.encode walBytes.toUInt64)
        staged.flush)
      syncPaths #[dir.file .wal, stagedPath]
      IO.FS.rename stagedPath (dir.file .walBoundary)
      syncPaths #[dir.path]
      pure ()) := rfl

@[inline] private def DiskTable.writeWith (db : DiskTable) (key : UInt64) (value : Option UInt64)
    (onRejected onCommitUnknown : IO.Error → ε) : EIO ε UInt64 := do
  let state ← db.installed.adapt onRejected
  let (event, table) ← (fromOption (prepareWrite state.table key value)
    "write sequence space exhausted").adapt onRejected
  let walBytes := state.walBytes + WAL.frameSize
  unless walBytes < UInt64.size do throw (onRejected (IO.userError "WAL byte count is too large"))
  db.phase.set .poisoned
  (commitWalWrite db.dir event walBytes).adapt onCommitUnknown
  db.phase.set (.ready { state with table, walBytes })
  return event.sequence

/-- Acknowledgement follows the WAL sync and durable publication of the byte boundary. -/
def DiskTable.write (db : DiskTable) (key : UInt64) (value : Option UInt64) : IO UInt64 :=
  db.writeWith key value id id

/-- Submit a write and report its sequence after durable publication. If the
commit outcome is unknown, close and reopen the database before further use. -/
def DiskTable.writeWithOutcome (db : DiskTable) (key : UInt64) (value : Option UInt64) :
    EIO DiskWriteError UInt64 :=
  db.writeWith key value .rejected .commitUnknown

def DiskTable.acquireAt (db : DiskTable) (snapshot : UInt64) : IO (Option DiskSnapshotPin) := do
  let state ← db.installed
  match state.table.acquireAt snapshot with
  | none => return none
  | some (pin, table) =>
    db.phase.set (.ready { state with table })
    return some ⟨⟨db.session, pin.handle⟩, pin.sequence⟩

def DiskTable.acquire (db : DiskTable) : IO DiskSnapshotPin := do
  let state ← db.installed
  fromOption (← db.acquireAt state.table.committed) "cannot acquire the latest snapshot"

def DiskTable.release (db : DiskTable) (handle : DiskSnapshotHandle) : IO Unit :=
  DiskSession.withLocalHandle db.installed (handle.session.ptrEq db.session) () fun state =>
    db.phase.set (.ready { state with table := state.table.release handle.localHandle })

def DiskTable.lookup (db : DiskTable) (handle : DiskSnapshotHandle) (key : UInt64) :
    IO (Option (Option UInt64)) :=
  DiskSession.withLocalHandle db.installed (handle.session.ptrEq db.session) none fun state =>
    pure (state.table.lookup handle.localHandle key)

def DiskTable.range (db : DiskTable) (handle : DiskSnapshotHandle) (lo hi : UInt64) :
    IO (Option (List (Alvoki.Compaction.Model.Entry (Option UInt64)))) :=
  DiskSession.withLocalHandle db.installed (handle.session.ptrEq db.session) none fun state =>
    pure (state.table.range handle.localHandle lo hi)

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

/-- Dispatch the checkpoint schedule to the exact run and manifest file
operations. The native caller caches the run array and encoded manifest. -/
@[macro_inline] def performCheckpointFileStep [Monad m] (dir : DiskDirectory)
    (generation : UInt64) (runs : Array CheckedRun) (stagedManifest : FilePath)
    (manifestBytes : ByteArray) (checkRun : Option CheckedRun → m CheckedRun)
    (write : FilePath → ByteArray → m Unit) (sync : Array FilePath → m Unit)
    (renameFile : FilePath → FilePath → m Unit) : CheckpointPublication.Step → m Unit
  | .writeRun index => do
    let run ← checkRun runs[index]?
    write (dir.file (.run generation index)) run.run.bytes
  | .syncRun index => sync #[dir.file (.run generation index)]
  | .syncRunsDirectory => sync #[dir.path]
  | .manifest step =>
    Publication.performReplacement (write · manifestBytes) sync renameFile
      stagedManifest dir.path (fun _ => dir.file .manifest) #[] step

/-- Flush pending writes and publish a fresh generation. All previous run
files and WAL frames remain available through interrupted publication. -/
def DiskTable.checkpoint (db : DiskTable) : IO Unit := do
  let state ← db.installed
  let table ← flushForCheckpoint state.table IO.ofExcept
  let count := table.runs.length
  let next := state.generation.toNat + 1
  unless next < UInt64.size ∧ count < UInt64.size do
    throw (IO.userError "checkpoint generation or run count is too large")
  let generation := UInt64.ofNat next
  let runs := table.runs.toArray
  let manifestBytes := Manifest.encode (checkpointHeader table generation)
  let stagedManifest := db.dir.file .stagedManifest
  db.phase.set .poisoned
  CheckpointPublication.run runs.size
    (performCheckpointFileStep db.dir generation runs stagedManifest manifestBytes
      (fromOption · "checkpoint run index is out of bounds") writeFlushed syncPaths IO.FS.rename)
  db.phase.set (.ready { state with table, generation })

end Alvoki.Storage
