import Alvoki.Storage.Disk.DiskPaths
import Alvoki.Storage.Disk.WalBoundary
import Alvoki.Storage.Disk.CheckpointRead
import Alvoki.Storage.Disk.IntegrityCheckpointRead
import Alvoki.Storage.Disk.DiskSession
import Alvoki.Storage.Disk.RunFileSelection
import Alvoki.Storage.Publication.CheckpointPublication
import Alvoki.Storage.Publication.RunCollection

namespace Alvoki.Storage
open System Alvoki.Compaction
open Alvoki.Sequential (SnapshotHandle)

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

private def openCheckpoint (dir : DiskDirectory) : IO (Option (PackedTable × UInt64)) :=
  readIntegrityCheckpoint (readOptionalFile (dir.file .manifest))
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
  let dir ← DiskDirectory.open path
  let lock ← IO.FS.Handle.mk (dir.file .lock) .append
  DiskSession.openWithLock lock.tryLock (fun _ => IO.userError s!"database already open: {dir.path}")
    (fun _ => lock.unlock) (fun _ => openLocked dir lock)

/-- The native lock and every recovery read use names from the same resolved
directory. Optional reads use lstat and the subsequent read of that same path.
The checkpoint decoder selects the exact generation and run indices. -/
theorem DiskTable.open_fileTargets (path : FilePath) : DiskTable.open path = (do
    let dir ← DiskDirectory.open path
    let lock ← IO.FS.Handle.mk (dir.file .lock) .append
    DiskSession.openWithLock (lock.tryLock (exclusive := true))
      (fun _ => IO.userError s!"database already open: {dir.path}") (fun _ => lock.unlock) fun _ => do
        let readOptional : FilePath → IO (Option ByteArray) := fun target =>
          readOptionalDatabaseFile target.symlinkMetadata.toBaseIO (fun _ => IO.FS.readBinFile target)
            (fun _ => IO.userError s!"expected a regular database file: '{target}'") throw
        let checkpoint ← readIntegrityCheckpoint (readOptional (dir.file .manifest))
          (fun generation index => IO.FS.readBinFile (dir.file (.run generation index))) IO.ofExcept
        withRecoveredOpen checkpoint (readOptional (dir.file .walBoundary)) (readOptional (dir.file .wal))
          IO.ofExcept (fun message => throw (IO.userError message))
          (fun _ => writeFlushed (dir.file .wal) ByteArray.empty)
          (fun selected => atomicReplace dir .stagedWal .wal selected)
          (fun _ => syncPaths #[dir.file .wal, dir.path]) (fun length => publishWalBoundary dir length)
          fun table generation walBytes => do
            let installed : Installed := { table, generation, walBytes }
            return ⟨dir, lock, ← IO.mkRef (.ready installed), ← IO.mkRef ()⟩) := rfl

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

/-- Commit the prepared frame and publish its new byte count from the locked write path. -/
@[macro_inline] private def commitWalWrite (dir : DiskDirectory) (event : WAL.Write)
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

/-- Encode lengths and checksums for the exact run payloads the writer uses. -/
def encodeCheckpointIntegrityManifest (table : PackedTable) (generation : UInt64) : Except String ByteArray := do
  let files := table.runs.map (·.run.bytes)
  unless files.all (fun bytes => decide (bytes.size < UInt64.size)) do
    throw "checkpoint run byte count is too large"
  return (Manifest.IntegrityCheckpoint.fromRuns (checkpointHeader table generation) files).encode

theorem encodeCheckpointIntegrityManifest_exact {table : PackedTable} (generation : UInt64)
    (fits : ∀ bytes ∈ table.runs.map (·.run.bytes), bytes.size < UInt64.size) :
    encodeCheckpointIntegrityManifest table generation = .ok
      (Manifest.IntegrityCheckpoint.fromRuns (checkpointHeader table generation) (table.runs.map (·.run.bytes))).encode := by
  have bounded : (table.runs.map (·.run.bytes)).all (fun bytes => decide (bytes.size < UInt64.size)) = true :=
    List.all_eq_true.mpr (fun bytes member => decide_eq_true (fits bytes member))
  simp [encodeCheckpointIntegrityManifest, bounded, pure, Except.pure]

/-- Flush pending writes and publish a fresh generation with run integrity
metadata. Previous run files and WAL frames support interrupted publication. -/
def DiskTable.checkpoint (db : DiskTable) : IO Unit := do
  let state ← db.installed
  let table ← flushForCheckpoint state.table IO.ofExcept
  let count := table.runs.length
  let next := state.generation.toNat + 1
  unless next < UInt64.size ∧ count < UInt64.size do
    throw (IO.userError "checkpoint generation or run count is too large")
  let generation := UInt64.ofNat next
  let runs := table.runs.toArray
  let manifestBytes ← IO.ofExcept (encodeCheckpointIntegrityManifest table generation)
  let stagedManifest := db.dir.file .stagedManifest
  db.phase.set .poisoned
  CheckpointPublication.run runs.size
    (performCheckpointFileStep db.dir generation runs stagedManifest manifestBytes
      (fromOption · "checkpoint run index is out of bounds") writeFlushed syncPaths IO.FS.rename)
  db.phase.set (.ready { state with table, generation })

/-- The native writer publishes the computed v2 manifest and the exact run
array via the shared schedule before installing the ready state. -/
theorem DiskTable.checkpoint_fileEffects (db : DiskTable) : db.checkpoint = (do
      let state ← db.installed
      let table ← flushForCheckpoint state.table IO.ofExcept
      let next := state.generation.toNat + 1
      unless next < UInt64.size ∧ table.runs.length < UInt64.size do
        throw (IO.userError "checkpoint generation or run count is too large")
      let generation := UInt64.ofNat next
      let manifestBytes ← IO.ofExcept (encodeCheckpointIntegrityManifest table generation)
      db.phase.set .poisoned
      CheckpointPublication.run table.runs.length
        (performCheckpointFileStep db.dir generation table.runs.toArray (db.dir.file .stagedManifest)
          manifestBytes (fromOption · "checkpoint run index is out of bounds") writeFlushed syncPaths IO.FS.rename)
      db.phase.set (.ready { state with table, generation })) := by
  simp only [checkpoint, List.size_toArray]

/-- Inspect the final component without following symlinks. A missing entry
in the owned parent is ineligible. Other lookup errors stop the pass. -/
private def runCollectionKindAt (path : FilePath) : IO (Except String IO.FS.FileType) := do
  match ← path.symlinkMetadata.toBaseIO with
  | .ok metadata => return .ok metadata.type
  | .error (.noFileOrDirectory _ 2 _) => return .error "run file is absent"
  | .error error => throw error

/-- Reclaim strictly older, unheld run generations in a ready writer session.
Open and checkpoint settle the selected manifest before the writer becomes
ready. Under the same lock, check that the observed v2 generation still
matches before inspecting run paths. Callers must keep external file holds
stable and pass their generations. Snapshot pins use runs in memory.

An I/O error can leave a partial pass. The session can retry by listing
again. Even an empty retry syncs the directory to settle earlier unlinks. -/
def DiskTable.collectObsoleteRuns (db : DiskTable) (heldGenerations : List UInt64 := []) : IO Unit := do
  let state ← db.installed
  let manifest ← readOptionalFile (db.dir.file .manifest)
  let current ← IO.ofExcept (validateIntegrityRunCollectionGeneration state.generation manifest)
  let entries ← db.dir.path.readDir
  let names := entries.toList.map (·.fileName)
  let selected ← selectRunFilesWith db.dir current (retainRunGeneration state.generation heldGenerations)
    runCollectionKindAt names
  RunCollection.run selected (RunCollection.performPaths (fun path => (IO.FS.removeFile path).toBaseIO)
    (fun path => syncPaths #[path]) throw (fun (generation, index) => db.dir.file (.run generation index))
    db.dir.path)

/-- The native maintenance entry point validates the ready session and its
manifest before executing the shared selector and unlink schedule. Both
lookup and unlink reconstruct each run's path in the same locked directory. -/
theorem DiskTable.collectObsoleteRuns_fileEffects (db : DiskTable) (heldGenerations : List UInt64) :
    db.collectObsoleteRuns heldGenerations = (do
      let state ← (← db.phase.get).installed
      let manifestPath := db.dir.file .manifest
      let manifest ← readOptionalDatabaseFile manifestPath.symlinkMetadata.toBaseIO
        (fun _ => IO.FS.readBinFile manifestPath)
        (fun _ => IO.userError s!"expected a regular database file: '{manifestPath}'") throw
      let current ← IO.ofExcept (validateIntegrityRunCollectionGeneration state.generation manifest)
      let entries ← db.dir.path.readDir
      let selected ← selectRunFilesWith db.dir current (retainRunGeneration state.generation heldGenerations)
        (fun path => do
          match ← path.symlinkMetadata.toBaseIO with
          | .ok metadata => return .ok metadata.type
          | .error (.noFileOrDirectory _ 2 _) => return .error "run file is absent"
          | .error error => throw error) (entries.toList.map (·.fileName))
      RunCollection.run selected (RunCollection.performPaths (fun path => (IO.FS.removeFile path).toBaseIO)
        (fun path => syncPaths #[path]) throw (fun (generation, index) => db.dir.file (.run generation index))
        db.dir.path)) := rfl

end Alvoki.Storage
