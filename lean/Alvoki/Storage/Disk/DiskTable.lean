import Alvoki.Storage.Disk.DiskPaths
import Alvoki.Storage.Disk.WalBoundary
import Alvoki.Storage.Disk.CheckpointRead
import Alvoki.Storage.Disk.IntegrityCheckpointRead
import Alvoki.Storage.Disk.DiskSession
import Alvoki.Storage.Disk.RunFileSelection
import Alvoki.Storage.Disk.StagingFile
import Alvoki.Storage.Disk.WalSegmentCommit
import Alvoki.Storage.Disk.WalGroupSyncSchedule
import Alvoki.Storage.Disk.WalSegmentBootstrapIO
import Alvoki.Storage.Disk.WalSegmentBoundedOpen
import Alvoki.Storage.Disk.WalSegmentCollectionPlan
import Alvoki.Storage.Disk.WalSegmentRotationIO
import Alvoki.Storage.Publication.CheckpointPublication
import Alvoki.Storage.Publication.RunCollection

namespace Alvoki.Storage
open System Alvoki.Compaction
open Alvoki.Sequential (SnapshotHandle)

structure DiskSession.Installed where
  table : PackedTable
  generation : UInt64
  walBytes : Nat
  activeFirst : Nat

private abbrev Installed := DiskSession.Installed

private abbrev Phase := DiskSession.Phase Installed

@[inline] def WalSegmentRepair.Reopened.installed (opened : WalSegmentRepair.Reopened) :
    DiskSession.Installed :=
  ⟨opened.table, opened.generation, opened.walBytes.toNat, opened.keeper⟩

/-- An opaque snapshot handle tied to the open disk session that issued it. -/
structure DiskSnapshotHandle where
  private mk ::
  private session : IO.Ref Unit
  private localHandle : SnapshotHandle

structure DiskSnapshotPin where
  private mk ::
  handle : DiskSnapshotHandle
  sequence : UInt64

@[extern "alvoki_fsync"]
private opaque fsyncHandle : @& IO.FS.Handle → @& String → IO Unit

/-- Keep the directory and current append handle for the session. A pending
handle belongs to a file opened by the current publication or recovery step
and is consumed at its durability barrier, before any rename can rebind it. -/
private structure SyncFiles where
  dir : FilePath
  directory : IO.Ref (Option IO.FS.Handle)
  active : IO.Ref (Option (FilePath × IO.FS.Handle))
  pending : IO.Ref (List (FilePath × IO.FS.Handle))

private def SyncFiles.open (dir : FilePath) : IO SyncFiles := do
  let directory ← IO.FS.Handle.mk dir .read
  return ⟨dir, ← IO.mkRef (some directory), ← IO.mkRef none, ← IO.mkRef []⟩

private def SyncFiles.remember (files : SyncFiles) (path : FilePath)
    (handle : IO.FS.Handle) : IO Unit :=
  files.pending.modify ((path, handle) :: ·)

private def SyncFiles.stage (files : SyncFiles) (path : FilePath) (bytes : ByteArray) : IO Unit := do
  files.remember path (← writeFreshStagedHandle path bytes)

private def SyncFiles.create (files : SyncFiles) (path : FilePath) : IO Unit := do
  files.remember path (← IO.FS.Handle.mk path .writeNew)

private def SyncFiles.append (files : SyncFiles) (path : FilePath) (bytes : ByteArray) : IO Unit := do
  let current ← files.active.get
  let wal ← match current with
    | some (active, handle) =>
      if path == active then pure handle else IO.FS.Handle.mk path .append
    | none => IO.FS.Handle.mk path .append
  try
    wal.write bytes
    wal.flush
  catch error =>
    -- Close a potentially dirty stream while this session still holds the lock.
    files.active.set none
    throw error
  files.active.set (some (path, wal))

private def SyncFiles.sync (files : SyncFiles) (path : FilePath) : IO Unit := do
  let file ← if path == files.dir then do
    let some handle ← files.directory.get | throw (IO.userError "database is closed")
    pure handle
  else do
    let pending ← files.pending.get
    if let some (_, handle) := pending.find? (fun entry => entry.1 == path) then
      files.pending.set (pending.filter (fun entry => entry.1 != path))
      pure handle
    else if let some (active, handle) ← files.active.get then
      if active == path then pure handle else IO.FS.Handle.mk path .read
    else IO.FS.Handle.mk path .read
  fsyncHandle file path.toString

/-- A failed member of a grouped barrier does not prevent attempts on the
remaining members. Rename is allowed only if the entire barrier succeeds. -/
private def SyncFiles.syncPaths (files : SyncFiles) (paths : Array FilePath) : IO Unit :=
  SyncPathGroup.run files.sync paths

/-- Linux adapter for a sequential caller. The lock excludes a second open
writer. An I/O failure during publication requires reopening the directory. -/
structure DiskTable where
  private mk ::
  private dir : DiskDirectory
  private lock : IO.FS.Handle
  private files : SyncFiles
  private phase : IO.Ref Phase
  private session : IO.Ref Unit

private def fromOption (result : Option α) (message : String) : IO α :=
  match result with
  | some value => pure value
  | none => throw (IO.userError message)

/-- The manifest fields for the exact run order published by a checkpoint. -/
def checkpointHeader (table : PackedTable) (generation : UInt64) : Manifest.Checkpoint :=
  ⟨generation, table.committed, table.pins.floor, table.runs.length.toUInt64⟩

/-- Flush pending rows when preparing a checkpoint, keeping an already
flushed table's run order and avoiding an extra empty run. -/
@[macro_inline] def flushForCheckpoint [Monad m] (table : PackedTable)
    (validate : Except String PackedTable → m PackedTable) : m PackedTable :=
  if table.memoryIsEmpty then pure table else validate table.flush

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

private def optionalMetadata (path : FilePath) : IO (Option IO.FS.Metadata) := do
  match ← path.symlinkMetadata.toBaseIO with
  | .ok metadata => pure (some metadata)
  | .error (.noFileOrDirectory _ 2 _) => pure none
  | .error error => throw error

private def checkPrivateRegular (path : FilePath) (metadata : IO.FS.Metadata) : IO Unit := do
  unless metadata.type == .file && metadata.numLinks == 1 do
    throw (IO.userError s!"expected a regular database file with one link: '{path}'")

private def writeRunFlushed (files : SyncFiles) (path : FilePath) (content : ByteArray) : IO Unit := do
  if let some metadata ← optionalMetadata path then checkPrivateRegular path metadata
  let file ← IO.FS.Handle.mk path .write
  file.write content
  file.flush
  files.remember path file

private def readRequiredFile (path : FilePath) : IO ByteArray := do
  let metadata ← path.symlinkMetadata
  unless metadata.type == .file do
    throw (IO.userError s!"expected a regular database file: '{path}'")
  IO.FS.readBinFile path

private def readExactPrefix (file : IO.FS.Handle) (remaining : Nat) (bytes : ByteArray) : IO ByteArray := do
  if remaining = 0 then return bytes
  let chunk ← file.read remaining.toUSize
  if _valid : 0 < chunk.size ∧ chunk.size ≤ remaining then
    let bytes := if bytes.isEmpty then chunk else bytes ++ chunk
    readExactPrefix file (remaining - chunk.size) bytes
  else throw (IO.userError "short or oversized WAL keeper read")
termination_by remaining

/-- Under the held lock, use the stable keeper's no-follow physical size
only to select repair. Read just the byte interval selected by the marker. -/
private def readKeeperPrefix (files : SyncFiles) (path : FilePath) (count : Nat) : IO WalSegmentRepair.KeeperPrefix := do
  let metadata ← path.symlinkMetadata
  checkPrivateRegular path metadata
  unless count ≤ metadata.byteSize.toNat ∧ count < USize.size do
    throw (IO.userError s!"WAL keeper does not cover its selected prefix: '{path}'")
  let file ← IO.FS.Handle.mk path .read
  let bytes ← readExactPrefix file count ByteArray.empty
  if count == metadata.byteSize.toNat then files.remember path file
  return ⟨bytes, metadata.byteSize.toNat⟩

private def inspectWalSegment (path : FilePath) : IO (Except IO.Error IO.FS.Metadata) := do
  let report ← path.symlinkMetadata.toBaseIO
  if let .ok metadata := report then checkPrivateRegular path metadata
  pure report

private def readEmptyWalSegment (path : FilePath) (nonempty : String) : IO (Option ByteArray) := do
  let some metadata ← optionalMetadata path | return none
  checkPrivateRegular path metadata
  unless metadata.byteSize == 0 do throw (IO.userError nonempty)
  return some ByteArray.empty

private def rejectFlatWal (dir : DiskDirectory) : IO Unit := do
  if (← optionalMetadata (dir.file .wal)).isSome then
    throw (IO.userError s!"unsupported flat WAL binding: '{dir.file .wal}'")

/-- Recover the historical whole-file layout in the publication models. -/
@[macro_inline] def withRecoveredOpen [Monad m] {α : Type}
    (checkpoint : Option (PackedTable × UInt64)) (readMarker readWal : m (Option ByteArray))
    (validate : {β : Type} → Except String β → m β) (fail : {β : Type} → String → m β)
    (createWal : Unit → m Unit)
    (repairWal : ByteArray → m Unit) (syncWal : Unit → m Unit) (publishMarker : Nat → m Unit)
    (install : PackedTable → UInt64 → Nat → m α) : m α := do
  let (base, generation) := checkpoint.getD (.empty, 0)
  WAL.Boundary.withOpenWal readMarker readWal validate (fun boundary => do
    if boundary.isSome then
      fail WAL.Boundary.missingOpenWal
    else if checkpoint.isSome then
      fail WAL.Boundary.missingOpenMarker
    else
      createWal ()
      pure ByteArray.empty) fun boundary bytes => do
    match boundary with
    | some count =>
      let (selected, table) ← validate (WAL.Boundary.recoverMarked base count bytes)
      let table ← Publication.finishReopen bytes.size selected.size
        (fun _ => repairWal selected) syncWal table
      install table generation selected.size
    | none =>
      if checkpoint.isSome || !bytes.isEmpty then
        fail WAL.Boundary.missingOpenMarker
      else
        syncWal ()
        publishMarker 0
        install .empty 0 0

private def bootstrapSegmented (dir : DiskDirectory) (files : SyncFiles) : IO WalSegmentRepair.Reopened :=
  WalSegmentRepair.bootstrapSegmentedWith dir FilePath.readDir
    (readEmptyWalSegment · WAL.Boundary.missingOpenMarker) optionalMetadata
    files.create files.stage files.syncPaths IO.FS.rename

/-- Check the markerless layout before creating or syncing segment zero,
then publish the zero marker through the staged replacement schedule. -/
theorem bootstrapSegmented_fileEffects (dir : DiskDirectory) : bootstrapSegmented dir files = (do
    let empty ← (do
      let entries ← dir.path.readDir
      if entries.any (fun entry => WalSegmentRepair.conflictsWithBootstrap entry.fileName) then
        throw (IO.userError WAL.Boundary.missingOpenMarker)
      let empty ← readEmptyWalSegment (dir.file (.walSegment 0)) WAL.Boundary.missingOpenMarker
      if let some staged ← optionalMetadata (dir.file .stagedWalBoundary) then
        unless staged.type == .file && empty.isSome do
          throw (IO.userError WAL.Boundary.missingOpenMarker)
      pure empty : IO (Option ByteArray))
    WalSegmentRotation.runAt dir 0 (fun _ => pure empty)
      files.create (fun path => files.syncPaths #[path])
    Publication.run (Publication.performReplacement (files.stage · (WAL.Boundary.encode 0))
      files.syncPaths IO.FS.rename (dir.file .stagedWalBoundary) dir.path (fun _ => dir.file .walBoundary) #[])
    return ⟨.empty, 0, 0, 0⟩) := rfl

private def recoverSegmentedWal (dir : DiskDirectory) (files : SyncFiles) : IO WalSegmentRepair.Reopened := do
  rejectFlatWal dir
  if (← optionalMetadata (dir.file .walBoundary)).isSome then
    WalSegmentRepair.reopenMarkedBoundedWith dir readOptionalFile FilePath.readDir inspectWalSegment
      readRequiredFile (readKeeperPrefix files)
      (fun path => (IO.FS.removeFile path).toBaseIO) files.stage files.syncPaths IO.FS.rename
  else
    bootstrapSegmented dir files

private def installReopened (dir : DiskDirectory) (lock : IO.FS.Handle)
    (files : SyncFiles) (opened : WalSegmentRepair.Reopened) : IO DiskTable :=
  -- ST.Ref.ptrEq distinguishes allocations. Keeping a separate cell lets a
  -- stale handle retain its identity without retaining the database state.
  DiskSession.installReady opened.installed (fun phase => IO.mkRef phase) (fun _ => IO.mkRef ()) fun phase session =>
    pure ⟨dir, lock, files, phase, session⟩

/-- Open a database in an existing directory and replay its durable WAL. -/
def DiskTable.open (path : FilePath) : IO DiskTable := do
  let dir ← DiskDirectory.open path
  rejectFlatWal dir
  if let some metadata ← optionalMetadata (dir.file .lock) then checkPrivateRegular (dir.file .lock) metadata
  let lock ← IO.FS.Handle.mk (dir.file .lock) .append
  DiskSession.openWithLock lock.tryLock (fun _ => IO.userError s!"database already open: {dir.path}")
    (fun _ => lock.unlock) fun _ => do
      let files ← SyncFiles.open dir.path
      installReopened dir lock files (← recoverSegmentedWal dir files)

/-- The native lock, strict checkpoint, and segment recovery worker use
the same resolved directory. Reopen installs the returned keeper only
after the repair or initial publication has settled. -/
theorem DiskTable.open_fileTargets (path : FilePath) : DiskTable.open path = (do
    let dir ← DiskDirectory.open path
    rejectFlatWal dir
    if let some metadata ← optionalMetadata (dir.file .lock) then checkPrivateRegular (dir.file .lock) metadata
    let lock ← IO.FS.Handle.mk (dir.file .lock) .append
    DiskSession.openWithLock (lock.tryLock (exclusive := true))
      (fun _ => IO.userError s!"database already open: {dir.path}") (fun _ => lock.unlock) fun _ => do
        let files ← SyncFiles.open dir.path
        let opened ← (do
          rejectFlatWal dir
          if (← optionalMetadata (dir.file .walBoundary)).isSome then
            WalSegmentRepair.reopenMarkedBoundedWith dir readOptionalFile FilePath.readDir inspectWalSegment
              readRequiredFile (readKeeperPrefix files)
              (fun path => (IO.FS.removeFile path).toBaseIO) files.stage files.syncPaths IO.FS.rename
          else bootstrapSegmented dir files : IO WalSegmentRepair.Reopened)
        DiskSession.installReady opened.installed (fun phase => IO.mkRef phase) (fun _ => IO.mkRef ())
          fun phase session => pure ⟨dir, lock, files, phase, session⟩) := rfl

def DiskTable.close (db : DiskTable) : IO Unit := do
  (← db.phase.get).close (fun _ => db.lock.unlock) fun _ => do
    db.files.active.set none
    db.files.pending.set []
    db.files.directory.set none
    db.phase.set .closed

private def DiskTable.installed (db : DiskTable) : IO Installed := do
  (← db.phase.get).installed

private def DiskTable.planWalCollectionAt (db : DiskTable) (state : Installed) : IO (List Nat) :=
  planWalCollectionWith db.dir state.generation state.walBytes state.activeFirst
    readOptionalFile FilePath.readDir inspectWalSegment

/-- Inspect which sealed WAL segments the current durable checkpoint covers.
The result describes the inventory observed during this call. -/
def DiskTable.planWalCollection (db : DiskTable) : IO (List Nat) := do
  db.planWalCollectionAt (← db.installed)

theorem DiskTable.planWalCollection_fileEffects (db : DiskTable) :
    db.planWalCollection = (do
      let state ← (← db.phase.get).installed
      planWalCollectionWith db.dir state.generation state.walBytes state.activeFirst
        readOptionalFile FilePath.readDir inspectWalSegment) := rfl

/-- Reclaim sealed WAL segments covered by the current durable checkpoint.
A failed preflight leaves the writer ready. An unlink or directory sync
error requires close and reopen before further use. The directory is
synced on every completed pass, including a pass with no eligible files. -/
def DiskTable.collectCoveredWal (db : DiskTable) : IO Unit := do
  let state ← db.installed
  let selected ← db.planWalCollectionAt state
  DiskSession.publishPrepared db.phase.set
    (RunCollection.run selected (RunCollection.performPaths (fun path => (IO.FS.removeFile path).toBaseIO)
      (fun path => db.files.syncPaths #[path]) throw (fun first => db.dir.file (.walSegment first)) db.dir.path))
    (db.phase.set (.ready state))

/-- Plan under the held writer before marking it unavailable, then run the
shared unlink and directory-barrier schedule at the same resolved paths. -/
theorem DiskTable.collectCoveredWal_fileEffects (db : DiskTable) :
    db.collectCoveredWal = (do
      let state ← (← db.phase.get).installed
      let selected ← planWalCollectionWith db.dir state.generation state.walBytes state.activeFirst
        readOptionalFile FilePath.readDir inspectWalSegment
      db.phase.set .poisoned
      RunCollection.run selected (RunCollection.performPaths (fun path => (IO.FS.removeFile path).toBaseIO)
        (fun path => db.files.syncPaths #[path]) throw (fun first => db.dir.file (.walSegment first)) db.dir.path)
      db.phase.set (.ready state)) := rfl

private def checkActiveSegment (dir : DiskDirectory) (state : Installed) : IO Unit := do
  let path := dir.file (.walSegment state.activeFirst)
  let metadata ← path.symlinkMetadata
  checkPrivateRegular path metadata
  unless metadata.byteSize.toNat == state.walBytes - state.activeFirst * WAL.frameSize do
    throw (IO.userError s!"active WAL segment size disagrees with its durable marker: '{path}'")

/-- Roll over at the current absolute marker. An already empty active
segment needs no rotation. A failed publication requires reopening. -/
def DiskTable.rotateWal (db : DiskTable) : IO Unit := do
  let state ← db.installed
  let successor := state.walBytes / WAL.frameSize
  if state.activeFirst < successor then
    checkActiveSegment db.dir state
    DiskSession.publishPrepared db.phase.set
      (WalSegmentRotation.runAt db.dir successor
        (fun path => readEmptyWalSegment path "WAL segment successor is not empty")
        db.files.create (fun path => db.files.syncPaths #[path]))
      (do
        db.files.active.set none
        db.phase.set (.ready { state with activeFirst := successor }))

/-- The new active start is installed only after the shared empty-segment
creation and both synchronization steps complete. -/
theorem DiskTable.rotateWal_fileEffects (db : DiskTable) : db.rotateWal = (do
    let state ← (← db.phase.get).installed
    let successor := state.walBytes / WAL.frameSize
    if state.activeFirst < successor then
      checkActiveSegment db.dir state
      db.phase.set .poisoned
      WalSegmentRotation.runAt db.dir successor
        (fun path => readEmptyWalSegment path "WAL segment successor is not empty")
        db.files.create (fun path => db.files.syncPaths #[path])
      db.files.active.set none
      db.phase.set (.ready { state with activeFirst := successor })) := rfl

/-- The outcome of a failed write at the WAL mutation boundary. -/
inductive DiskWriteError where
  /-- This submission was rejected before attempting to append a WAL frame. -/
  | rejected (cause : IO.Error)
  /-- WAL mutation was attempted. The write may be recovered after reopening. -/
  | commitUnknown (cause : IO.Error)

/-- Commit the prepared frame to the validated active segment and publish
the new absolute byte count from the locked write path. -/
@[macro_inline] private def commitWalWrite (dir : DiskDirectory) (files : SyncFiles) (activeFirst : Nat) (event : WAL.Write)
    (walBytes : Nat) : IO Unit :=
  WalSegmentCommit.commitAt dir activeFirst event walBytes files.append files.stage files.syncPaths IO.FS.rename

/-- The native commit uses the same append-first schedule and marker steps as
the write-effects model. One sync callback covers the active segment and
the staged marker. Filesystem reports determine which effects persisted. -/
theorem commitWalWrite_fileEffects (dir : DiskDirectory) (files : SyncFiles) (activeFirst : Nat) (event : WAL.Write) (walBytes : Nat) :
    commitWalWrite dir files activeFirst event walBytes =
    WAL.Boundary.commit
      (files.append (dir.file (.walSegment activeFirst)) (WAL.encodeFrame event)) (do
        let stagedPath := dir.file .stagedWalBoundary
        files.stage stagedPath (WAL.Boundary.encode walBytes.toUInt64)
        files.syncPaths #[dir.file (.walSegment activeFirst), stagedPath]
        IO.FS.rename stagedPath (dir.file .walBoundary)
        files.syncPaths #[dir.path]
        pure ()) := rfl

@[inline] private def DiskTable.writeWith (db : DiskTable) (key : UInt64) (value : Option UInt64)
    (onRejected onCommitUnknown : IO.Error → ε) : EIO ε UInt64 := do
  let state ← db.installed.adapt onRejected
  let (event, table) ← (fromOption (prepareWrite state.table key value)
    "write sequence space exhausted").adapt onRejected
  let walBytes := state.walBytes + WAL.frameSize
  unless walBytes < UInt64.size do throw (onRejected (IO.userError "WAL byte count is too large"))
  (checkActiveSegment db.dir state).adapt onRejected
  DiskSession.publishPreparedWrite { state with table, walBytes } event.sequence db.phase.set
    ((commitWalWrite db.dir db.files state.activeFirst event walBytes).adapt onCommitUnknown)

/-- Acknowledgement follows the WAL sync and durable publication of the byte boundary. -/
def DiskTable.write (db : DiskTable) (key : UInt64) (value : Option UInt64) : IO UInt64 :=
  db.writeWith key value id id

/-- Submit a write and report its sequence after durable publication. If the
commit outcome is unknown, close and reopen the database before further use. -/
def DiskTable.writeWithOutcome (db : DiskTable) (key : UInt64) (value : Option UInt64) :
    EIO DiskWriteError UInt64 :=
  db.writeWith key value .rejected .commitUnknown

/-- Rejection checks the required existing segment before any write. An
attempted commit poisons the session until the absolute marker settles. -/
theorem DiskTable.writeWithOutcome_fileEffects (db : DiskTable) (key : UInt64) (value : Option UInt64) :
    db.writeWithOutcome key value = (do
      let state ← db.installed.adapt DiskWriteError.rejected
      let (event, table) ← (fromOption (prepareWrite state.table key value)
        "write sequence space exhausted").adapt DiskWriteError.rejected
      let walBytes := state.walBytes + WAL.frameSize
      unless walBytes < UInt64.size do
        throw (.rejected (IO.userError "WAL byte count is too large"))
      (checkActiveSegment db.dir state).adapt DiskWriteError.rejected
      db.phase.set .poisoned
      (commitWalWrite db.dir db.files state.activeFirst event walBytes).adapt DiskWriteError.commitUnknown
      db.phase.set (.ready { state with table, walBytes })
      return event.sequence) := rfl

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
    (writeRun writeStaged : FilePath → ByteArray → m Unit) (sync : Array FilePath → m Unit)
    (renameFile : FilePath → FilePath → m Unit) : CheckpointPublication.Step → m Unit
  | .writeRun index => do
    let run ← checkRun runs[index]?
    writeRun (dir.file (.run generation index)) run.run.bytes
  | .syncRun index => sync #[dir.file (.run generation index)]
  | .syncRunsDirectory => sync #[dir.path]
  | .manifest step =>
    Publication.performReplacement (writeStaged · manifestBytes) sync renameFile
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
      (fromOption · "checkpoint run index is out of bounds") (writeRunFlushed db.files) db.files.stage db.files.syncPaths IO.FS.rename)
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
          manifestBytes (fromOption · "checkpoint run index is out of bounds")
          (writeRunFlushed db.files) db.files.stage db.files.syncPaths IO.FS.rename)
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
    (fun path => db.files.syncPaths #[path]) throw (fun (generation, index) => db.dir.file (.run generation index))
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
        (fun path => db.files.syncPaths #[path]) throw (fun (generation, index) => db.dir.file (.run generation index))
        db.dir.path)) := rfl

end Alvoki.Storage
