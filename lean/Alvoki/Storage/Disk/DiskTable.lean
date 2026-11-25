import Alvoki.Storage.Disk.DiskPaths
import Alvoki.Storage.Disk.WalBoundary
import Alvoki.Storage.Disk.CheckpointRead
import Alvoki.Storage.Disk.IntegrityCheckpointRead
import Alvoki.Storage.Disk.DiskSession
import Alvoki.Storage.Disk.RunFileSelection
import Alvoki.Storage.Disk.ReadRecoveryPrefix
import Alvoki.Storage.Disk.ManifestAcquisition
import Alvoki.Storage.Disk.StagingFile
import Alvoki.Storage.Disk.SyncHandleRouting
import Alvoki.Storage.Disk.WalBatch
import Alvoki.Storage.Disk.WalSegmentCommit
import Alvoki.Storage.Disk.WalSegmentBootstrapIO
import Alvoki.Storage.Disk.WalSegmentCollectionPlan
import Alvoki.Storage.Disk.WalSegmentRotationIO
import Alvoki.Storage.Disk.WalSegmentCachedExtentOpen
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
private opaque fsyncHandle : @& IO.FS.Handle → IO Unit

/-- A successful directory listing ended at EOF. A readdir error
discards the partial listing before planning any file mutations. -/
@[extern "alvoki_read_dir_checked"]
private opaque readDirectoryChecked : @& FilePath → IO (Array IO.FS.DirEntry)

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

/-- Open the directory before allocating the three synchronization references. -/
@[macro_inline] def DiskSession.openSyncFilesWith [Monad m]
    (openDirectory : m handle) (recordDirectory : Option handle → m rDirectory)
    (recordActive : Option (FilePath × handle) → m rActive)
    (recordPending : List (FilePath × handle) → m rPending)
    (assemble : rDirectory → rActive → rPending → files) : m files := do
  let directory ← openDirectory
  let captured ← recordDirectory (some directory)
  let active ← recordActive none
  let pending ← recordPending []
  return assemble captured active pending

theorem syncFilesOpen_schedule (dir : FilePath) :
    SyncFiles.open dir = DiskSession.openSyncFilesWith (m := IO)
      (IO.FS.Handle.mk dir .read) (fun value => liftM (IO.mkRef value))
      (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value)) (SyncFiles.mk dir) := rfl

private def SyncFiles.remember (files : SyncFiles) (path : FilePath)
    (handle : IO.FS.Handle) : IO Unit :=
  files.pending.modify (SyncHandleRouting.pushPending path handle)

private def SyncFiles.stage (files : SyncFiles) (path : FilePath) (bytes : ByteArray) : IO Unit := do
  files.remember path (← writeFreshStagedHandle path bytes)

private def SyncFiles.create (files : SyncFiles) (path : FilePath) : IO Unit := do
  files.remember path (← IO.FS.Handle.mk path .writeNew)

/-- Exclusive creation remembers exactly the description returned by
the zero-keeper open. The grouped sync consumes it at the file barrier. -/
theorem syncFilesCreate_schedule (files : SyncFiles) (path : FilePath) :
    files.create path = (IO.FS.Handle.mk path .writeNew >>= files.remember path) := rfl

private def SyncFiles.append (files : SyncFiles) : FilePath → ByteArray → IO Unit :=
  SyncHandleRouting.appendWithActive files.active.get files.active.set
    (fun path => IO.FS.Handle.mk path .append) IO.FS.Handle.write IO.FS.Handle.flush

private def SyncFiles.sync (files : SyncFiles) (path : FilePath) : IO Unit :=
  SyncHandleRouting.syncWithHandles files.dir path files.directory.get files.pending.get
    files.pending.set files.active.get (fun path => IO.FS.Handle.mk path .read) fsyncHandle

/-- A failed member of a grouped barrier does not prevent attempts on the
remaining members. Rename is allowed only if the entire barrier succeeds. -/
private def SyncFiles.syncPaths (files : SyncFiles) (paths : Array FilePath) : IO Unit :=
  SyncPathGroup.run files.sync paths

/-- A bootstrap barrier uses the same cache selector as rotation and
ordinary publication. -/
theorem syncFilesSyncPaths_schedule (files : SyncFiles) (paths : Array FilePath) :
    files.syncPaths paths = SyncPathGroup.run (fun path =>
      SyncHandleRouting.syncWithHandles files.dir path files.directory.get files.pending.get
        files.pending.set files.active.get (fun name => IO.FS.Handle.mk name .read) fsyncHandle) paths := rfl

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
@[macro_inline] def readOptionalDatabaseFileWithMetadata [Monad m]
    (lookup : m (Except IO.Error IO.FS.Metadata)) (read : IO.FS.Metadata → m ByteArray)
    (notRegular : Unit → IO.Error) (fail : IO.Error → m (Option ByteArray)) :
    m (Option ByteArray) := do
  match ← lookup with
  | .ok metadata =>
    unless metadata.type == .file do
      return ← fail (notRegular ())
    return some (← read metadata)
  | .error error@(.noFileOrDirectory _ osCode _) =>
    -- Linux ENOENT identifies a missing directory entry.
    if osCode == 2 then return none else fail error
  | .error error => fail error

@[macro_inline] def readOptionalDatabaseFile [Monad m]
    (lookup : m (Except IO.Error IO.FS.Metadata)) (read : Unit → m ByteArray)
    (notRegular : Unit → IO.Error) (fail : IO.Error → m (Option ByteArray)) :
    m (Option ByteArray) :=
  readOptionalDatabaseFileWithMetadata lookup (fun _ => read ()) notRegular fail

private def readOptionalFile (path : FilePath) : IO (Option ByteArray) :=
  readOptionalDatabaseFile path.symlinkMetadata.toBaseIO (fun _ => IO.FS.readBinFile path)
    (fun _ => IO.userError s!"expected a regular database file: '{path}'") throw

theorem readOptionalFile_fileEffects (path : FilePath) :
    readOptionalFile path = readOptionalDatabaseFile (m := IO) path.symlinkMetadata.toBaseIO
      (fun _ => IO.FS.readBinFile path) (fun _ => IO.userError s!"expected a regular database file: '{path}'") throw := rfl

/-- Only a no-follow lookup's ENOENT denotes an absent directory entry. -/
@[macro_inline] def optionalMetadataWith [Monad m] [MonadExceptOf IO.Error m]
    (lookup : m (Except IO.Error IO.FS.Metadata)) : m (Option IO.FS.Metadata) := do
  match ← lookup with
  | .ok metadata => pure (some metadata)
  | .error (.noFileOrDirectory _ 2 _) => pure none
  | .error error => throw error

private def optionalMetadata (path : FilePath) : IO (Option IO.FS.Metadata) :=
  optionalMetadataWith path.symlinkMetadata.toBaseIO

private def checkPrivateRegular (path : FilePath) (metadata : IO.FS.Metadata) : IO Unit := do
  unless metadata.type == .file && metadata.numLinks == 1 do
    throw (IO.userError s!"expected a regular database file with one link: '{path}'")

private def writeRunFlushed (files : SyncFiles) (path : FilePath) (content : ByteArray) : IO Unit := do
  if let some metadata ← optionalMetadata path then checkPrivateRegular path metadata
  let file ← IO.FS.Handle.mk path .write
  file.write content
  file.flush
  files.remember path file

private def requiredRegularMetadata (path : FilePath) : IO IO.FS.Metadata := do
  let metadata ← path.symlinkMetadata
  unless metadata.type == .file do
    throw (IO.userError s!"expected a regular database file: '{path}'")
  return metadata

private def readExactPrefix (mismatch : IO.Error) (file : IO.FS.Handle) (remaining : Nat)
    (bytes : ByteArray) : IO ByteArray :=
  readExactPrefixWith mismatch file.read remaining bytes

/-- The locked-namespace contract relates the no-follow metadata to the
file opened for the marker or manifest read. -/
private def readOptionalCachedOpenFile (directory : DiskDirectory) (path : FilePath) : IO (Option ByteArray) :=
  readOptionalDatabaseFileWithMetadata path.symlinkMetadata.toBaseIO (fun metadata => do
    let file ← IO.FS.Handle.mk path .read
    if path == directory.file .walBoundary then
      readPrefixUntilEofWith (IO.userError "invalid WAL boundary length") file.read
        WAL.Boundary.acquisitionLimit ByteArray.empty
    else
      readIntegrityManifestPrefixWith file.read metadata.byteSize.toNat)
    (fun _ => IO.userError s!"expected a regular database file: '{path}'") throw

private def readCheckpointRunSize (path : FilePath) : IO Nat := do
  return (← requiredRegularMetadata path).byteSize.toNat

/-- The shared checkpoint reader checks this stable file's extent before opening it. -/
private def readCheckpointRunPrefix (path : FilePath) (count : Nat) : IO ByteArray := do
  let file ← IO.FS.Handle.mk path .read
  readExactPrefix (IO.userError checkpointIntegrityMismatch) file count ByteArray.empty

/-- The held inventory has checked the seal's full size. -/
private def readSealedWalPrefix (path : FilePath) (count : Nat) : IO ByteArray := do
  let file ← IO.FS.Handle.mk path .read
  readExactPrefix WalSegmentRepair.selectedWalSpanError file count ByteArray.empty

/-- Use the same held no-follow extent to read and decide whether to replace
the keeper. Preserve the exact opened handle for an aligned keeper sync. -/
private def readKeeperPrefix (files : SyncFiles) : FilePath → Nat → Nat → IO ByteArray :=
  SyncHandleRouting.readKeeperWith (fun path => IO.FS.Handle.mk path .read)
    (fun file count => readExactPrefix (IO.userError "short or oversized WAL keeper read") file count ByteArray.empty)
    files.remember

private def inspectWalSegment (path : FilePath) : IO (Except IO.Error IO.FS.Metadata) := do
  let report ← path.symlinkMetadata.toBaseIO
  if let .ok metadata := report then checkPrivateRegular path metadata
  pure report

private def readEmptyWalSegment (path : FilePath) (nonempty : String) : IO (Option ByteArray) := do
  let some metadata ← optionalMetadata path | return none
  checkPrivateRegular path metadata
  unless metadata.byteSize == 0 do throw (IO.userError nonempty)
  return some ByteArray.empty

@[macro_inline] def rejectFlatWalWith [Monad m] [MonadExceptOf IO.Error m] (dir : DiskDirectory)
    (metadata : m (Option IO.FS.Metadata)) : m Unit := do
  if (← metadata).isSome then
    throw (IO.userError s!"unsupported flat WAL binding: '{dir.file .wal}'")

private def rejectFlatWal (dir : DiskDirectory) : IO Unit :=
  rejectFlatWalWith dir (optionalMetadata (dir.file .wal))

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
  WalSegmentRepair.bootstrapSegmentedWith dir readDirectoryChecked
    (readEmptyWalSegment · WAL.Boundary.missingOpenMarker) optionalMetadata
    files.create files.stage files.syncPaths IO.FS.rename

/-- Check the markerless layout before creating or syncing segment zero,
then publish the zero marker through the staged replacement schedule. -/
theorem bootstrapSegmented_fileEffects (dir : DiskDirectory) : bootstrapSegmented dir files = (do
    let empty ← (do
      let entries ← readDirectoryChecked dir.path
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

/-- Under the writer lock, choose recovery using the visible marker binding. -/
@[macro_inline] def recoverSegmentedWalWith [Monad m] (rejectFlat : m Unit) (marker : m (Option IO.FS.Metadata))
    (marked bootstrap : m WalSegmentRepair.Reopened) : m WalSegmentRepair.Reopened := do
  rejectFlat
  if (← marker).isSome then marked else bootstrap

private def recoverSegmentedWal (dir : DiskDirectory) (files : SyncFiles) : IO WalSegmentRepair.Reopened :=
  recoverSegmentedWalWith (rejectFlatWal dir) (optionalMetadata (dir.file .walBoundary))
    (WalSegmentRepair.reopenMarkedBoundedWithCachedExtents dir (readOptionalCachedOpenFile dir)
      readCheckpointRunSize readCheckpointRunPrefix readDirectoryChecked inspectWalSegment readSealedWalPrefix
      (readKeeperPrefix files)
      (fun path => (IO.FS.removeFile path).toBaseIO) files.stage files.syncPaths IO.FS.rename)
    (bootstrapSegmented dir files)

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
            WalSegmentRepair.reopenMarkedBoundedWithCachedExtents dir (readOptionalCachedOpenFile dir)
              readCheckpointRunSize readCheckpointRunPrefix readDirectoryChecked inspectWalSegment readSealedWalPrefix
              (readKeeperPrefix files)
              (fun path => (IO.FS.removeFile path).toBaseIO) files.stage files.syncPaths IO.FS.rename
          else bootstrapSegmented dir files : IO WalSegmentRepair.Reopened)
        DiskSession.installReady opened.installed (fun phase => IO.mkRef phase) (fun _ => IO.mkRef ())
          fun phase session => pure ⟨dir, lock, files, phase, session⟩) := rfl

/-- Abstract name for the synchronization record already held by the
native opener. Its constructor and fields remain private. -/
abbrev DiskTable.OpenSyncFiles := SyncFiles

/-- The pure constructor at the end of the native open schedule, with
the same reached synchronization record enclosed in the callback. -/
def DiskTable.OpenReferenceAssembly (directory : DiskDirectory) (lock : IO.FS.Handle)
    (files : DiskTable.OpenSyncFiles) (assemble : IO.Ref Phase → IO.Ref Unit → DiskTable) : Prop :=
  assemble = fun phase session => ⟨directory, lock, files, phase, session⟩

/-- This is the constructor passed to the shared installation in
`DiskTable.open_fileTargets`. -/
theorem DiskTable.openReferenceAssembly (directory : DiskDirectory) (lock : IO.FS.Handle)
    (files : DiskTable.OpenSyncFiles) :
    DiskTable.OpenReferenceAssembly directory lock files
      (fun phase session => ⟨directory, lock, files, phase, session⟩) := rfl

/-- Proof-only access to the exact fields of the returned table. The
implementation keeps their projection functions private. -/
def DiskTable.UsesOpenReferences (db : DiskTable) (directory : DiskDirectory) (lock : IO.FS.Handle)
    (files : DiskTable.OpenSyncFiles) (phase : IO.Ref Phase) (session : IO.Ref Unit) : Prop :=
  db.dir = directory ∧ db.lock = lock ∧ db.files = files ∧ db.phase = phase ∧ db.session = session

theorem DiskTable.OpenReferenceAssembly.usesReferences {directory lock files assemble}
    (constructor : DiskTable.OpenReferenceAssembly directory lock files assemble)
    (phase : IO.Ref Phase) (session : IO.Ref Unit) :
    (assemble phase session).UsesOpenReferences directory lock files phase session := by
  rw [constructor]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

@[macro_inline] def checkPrivateRegularWith [Monad m] [MonadExceptOf IO.Error m]
    (path : FilePath) (metadata : IO.FS.Metadata) : m Unit := do
  unless metadata.type == .file && metadata.numLinks == 1 do
    throw (IO.userError s!"expected a regular database file with one link: '{path}'")

/-- Inspect the zero-keeper candidate through the same absent-or-private
empty regular file guard used by the native bootstrap and rotation. -/
@[macro_inline] def WalSegmentRotation.readEmptyWith [Monad m] [MonadExceptOf IO.Error m]
    (lookup : m (Except IO.Error IO.FS.Metadata)) (path : FilePath) (nonempty : String) :
    m (Option ByteArray) := do
  let some metadata ← optionalMetadataWith lookup | return none
  checkPrivateRegularWith path metadata
  unless metadata.byteSize == 0 do throw (IO.userError nonempty)
  return some ByteArray.empty

theorem readEmptyWalSegment_schedule (path : FilePath) (nonempty : String) :
    readEmptyWalSegment path nonempty =
      WalSegmentRotation.readEmptyWith (m := IO) path.symlinkMetadata.toBaseIO path nonempty := rfl

/-- A checkpoint run path may already exist after an interrupted attempt.
Check its private regular binding before opening it for write. Pass the
description used for both the write and flush to the final callback. -/
@[macro_inline] def writeCheckpointRunWith [Monad m] [MonadExceptOf IO.Error m] {handle result : Type}
    (lookup : FilePath → m (Except IO.Error IO.FS.Metadata)) (openWrite : FilePath → m handle)
    (write : handle → ByteArray → m Unit) (flush : handle → m Unit)
    (path : FilePath) (bytes : ByteArray) (retain : handle → m result) : m result := do
  if let some metadata ← optionalMetadataWith (lookup path) then checkPrivateRegularWith path metadata
  let handle ← openWrite path
  write handle bytes
  flush handle
  retain handle

theorem writeRunFlushed_schedule (files : SyncFiles) (path : FilePath) (bytes : ByteArray) :
    writeRunFlushed files path bytes =
      writeCheckpointRunWith (m := IO) (fun name => name.symlinkMetadata.toBaseIO)
        (IO.FS.Handle.mk · .write) IO.FS.Handle.write IO.FS.Handle.flush path bytes (files.remember path) := rfl

/-- Project the concrete pre-lock admission schedule onto supplied
primitive callbacks. Successful append-open identifies the handle passed to
acquisition, including when the lock file has just been created. -/
@[macro_inline] def DiskTable.withOpenAdmission [Monad m] [MonadExceptOf IO.Error m] {handle result : Type}
    (input : FilePath) (realPath : FilePath → m FilePath)
    (lookup : FilePath → m (Except IO.Error IO.FS.Metadata)) (openAppend : FilePath → m handle)
    (acquire : DiskDirectory → handle → m result) : m result := do
  let directory ← DiskDirectory.openWith realPath input
  rejectFlatWalWith directory (optionalMetadataWith (lookup (directory.file .wal)))
  if let some metadata ← optionalMetadataWith (lookup (directory.file .lock)) then
    checkPrivateRegularWith (directory.file .lock) metadata
  let lock ← openAppend (directory.file .lock)
  acquire directory lock

/-- The native opener is the same admission projection at the concrete IO
operations, followed by its existing exclusive flock and recovery. -/
theorem DiskTable.open_admission (input : FilePath) :
    DiskTable.open input = DiskTable.withOpenAdmission input IO.FS.realPath
      (fun path => path.symlinkMetadata.toBaseIO) (IO.FS.Handle.mk · .append) (fun directory lock =>
        DiskSession.openWithLock lock.tryLock
          (fun _ => IO.userError s!"database already open: {directory.path}") (fun _ => lock.unlock) fun _ => do
            let files ← SyncFiles.open directory.path
            installReopened directory lock files (← recoverSegmentedWal directory files)) := rfl

def DiskTable.close (db : DiskTable) : IO Unit := do
  (← db.phase.get).close (fun _ => db.lock.unlock) fun _ => do
    db.files.active.set none
    db.files.pending.set []
    db.files.directory.set none
    db.phase.set .closed

/-- Project close onto its phase, unlock and cache callbacks. -/
@[macro_inline] def DiskSession.closeSchedule [Monad m] (phase : m (Phase α))
    (unlock : Unit → m Unit) (clearActive clearPending clearDirectory finish : m Unit) : m Unit := do
  (← phase).close unlock fun _ => do
    clearActive
    clearPending
    clearDirectory
    finish

theorem DiskTable.close_schedule (db : DiskTable) :
    db.close = DiskSession.closeSchedule db.phase.get (fun _ => db.lock.unlock)
      (db.files.active.set none) (db.files.pending.set []) (db.files.directory.set none) (db.phase.set .closed) := rfl

/-- The three cache cells belonging to the synchronization record
captured by the opener. -/
def DiskTable.OpenSyncFiles.UsesCacheReferences (files : DiskTable.OpenSyncFiles)
    (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (directory : IO.Ref (Option IO.FS.Handle)) : Prop :=
  files.active = active ∧ files.pending = pending ∧ files.directory = directory

/-- The path used for directory dispatch in the synchronization record. -/
def DiskTable.OpenSyncFiles.AtDirectory (files : DiskTable.OpenSyncFiles) (path : FilePath) : Prop :=
  files.dir = path

/-- The actual initialization action for the synchronization record
allocated on the resolved path by `DiskTable.open`. -/
def DiskTable.OpenSyncFiles.IsOpenAction (path : FilePath) (action : IO DiskTable.OpenSyncFiles) : Prop :=
  action = SyncFiles.open path

theorem DiskTable.openSyncCacheReferences (path : FilePath) :
    ∃ (action : IO DiskTable.OpenSyncFiles)
      (assemble : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles),
      DiskTable.OpenSyncFiles.IsOpenAction path action ∧
      action = DiskSession.openSyncFilesWith (m := IO) (IO.FS.Handle.mk path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) assemble ∧
      ∀ directory active pending, (assemble directory active pending).UsesCacheReferences active pending directory ∧
        (assemble directory active pending).AtDirectory path := by
  exact ⟨SyncFiles.open path, SyncFiles.mk path, rfl, syncFilesOpen_schedule path, fun _ _ _ => ⟨⟨rfl, rfl, rfl⟩, rfl⟩⟩

/-- Close reads and writes exactly the phase, lock and cache
references of the opened table. -/
theorem DiskTable.UsesOpenReferences.close {db : DiskTable} {directory lock files phase token}
    (uses : db.UsesOpenReferences directory lock files phase token) :
    ∃ (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
      (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (cachedDirectory : IO.Ref (Option IO.FS.Handle)),
      files.UsesCacheReferences active pending cachedDirectory ∧
      db.close = DiskSession.closeSchedule phase.get (fun _ => lock.unlock)
        (active.set none) (pending.set []) (cachedDirectory.set none) (phase.set .closed) := by
  obtain ⟨_, sameLock, sameFiles, samePhase, _⟩ := uses
  exact ⟨files.active, files.pending, files.directory, ⟨rfl, rfl, rfl⟩,
    by rw [DiskTable.close_schedule, sameLock, sameFiles, samePhase]⟩

private def DiskTable.installed (db : DiskTable) : IO Installed := do
  (← db.phase.get).installed

private def DiskTable.planWalCollectionAt (db : DiskTable) (state : Installed) : IO (List Nat) :=
  planWalCollectionWith db.dir state.generation state.walBytes state.activeFirst
    readOptionalFile readDirectoryChecked inspectWalSegment

/-- Inspect which sealed WAL segments the current durable checkpoint covers.
The result describes the inventory observed during this call. -/
def DiskTable.planWalCollection (db : DiskTable) : IO (List Nat) := do
  db.planWalCollectionAt (← db.installed)

theorem DiskTable.planWalCollection_fileEffects (db : DiskTable) :
    db.planWalCollection = (do
      let state ← (← db.phase.get).installed
      planWalCollectionWith db.dir state.generation state.walBytes state.activeFirst
        readOptionalFile readDirectoryChecked inspectWalSegment) := rfl

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
        readOptionalFile readDirectoryChecked inspectWalSegment
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

/-- The native no-follow active-file guard, interpreted over reported metadata. -/
@[macro_inline] def checkActiveSegmentWith [Monad m] [MonadExceptOf IO.Error m]
    (directory : DiskDirectory) (state : Installed) (lookup : FilePath → m IO.FS.Metadata) : m Unit := do
  let path := directory.file (.walSegment state.activeFirst)
  let metadata ← lookup path
  checkPrivateRegularWith path metadata
  unless metadata.byteSize.toNat == state.walBytes - state.activeFirst * WAL.frameSize do
    throw (IO.userError s!"active WAL segment size disagrees with its durable marker: '{path}'")

theorem checkActiveSegment_fileEffects (directory : DiskDirectory) (state : Installed) :
    checkActiveSegment directory state = checkActiveSegmentWith directory state FilePath.symlinkMetadata := rfl

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

/-- Rotate only a nonempty active segment. Clear the old append handle
after successor publication and before exposing the updated ready phase. -/
@[macro_inline] def DiskSession.rotateWalSchedule [Monad m]
    (installed : m Installed) (guard : Installed → m Unit) (setPhase : DiskSession.Phase Installed → m Unit)
    (publish : Nat → m Unit) (clearActive : m Unit) : m Unit := do
  let state ← installed
  let successor := state.walBytes / WAL.frameSize
  if state.activeFirst < successor then
    guard state
    DiskSession.publishPrepared setPhase (publish successor) do
      clearActive
      setPhase (.ready { state with activeFirst := successor })

theorem DiskTable.rotateWal_schedule (db : DiskTable) : db.rotateWal =
    DiskSession.rotateWalSchedule (m := IO) db.installed
      (fun state => checkActiveSegmentWith db.dir state FilePath.symlinkMetadata) db.phase.set
      (fun successor => WalSegmentRotation.runAt db.dir successor
        (fun path => readEmptyWalSegment path "WAL segment successor is not empty") db.files.create
        (fun path => db.files.syncPaths #[path])) (db.files.active.set none) := rfl

/-- The outcome of a failed write at the WAL mutation boundary. -/
inductive DiskWriteError where
  /-- This submission was rejected before attempting to append a WAL frame. -/
  | rejected (cause : IO.Error)
  /-- WAL mutation was attempted. The write may be recovered after reopening. -/
  | commitUnknown (cause : IO.Error)

/-- The native diagnostic carried by either recorded write outcome. -/
def DiskWriteError.cause : DiskWriteError → IO.Error
  | .rejected cause | .commitUnknown cause => cause

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

/-- Enter the publication callback only after the single-write preflight.
The sequence guard precedes the WAL byte-count guard on this path. -/
@[macro_inline] def DiskSession.withPreparedSingleWrite [Monad m] [MonadExceptOf ε m]
    (key : UInt64) (value : Option UInt64) (installed : m Installed) (rejected : IO.Error → ε)
    (requirePrepared : Option (WAL.Write × PackedTable) → m (WAL.Write × PackedTable))
    (guard : Installed → m Unit) (publish : Installed → WAL.Write → PackedTable → Nat → m UInt64) : m UInt64 := do
  let state ← installed
  let (event, table) ← requirePrepared (prepareWrite state.table key value)
  let walBytes := state.walBytes + WAL.frameSize
  unless walBytes < UInt64.size do throw (rejected (IO.userError "WAL byte count is too large"))
  guard state
  publish state event table walBytes

@[inline] private def DiskTable.writeWith (db : DiskTable) (key : UInt64) (value : Option UInt64)
    (onRejected onCommitUnknown : IO.Error → ε) : EIO ε UInt64 :=
  DiskSession.withPreparedSingleWrite key value (db.installed.adapt onRejected) onRejected
    (fun result => (fromOption result "write sequence space exhausted").adapt onRejected)
    (fun state => (checkActiveSegment db.dir state).adapt onRejected)
    (fun state event table walBytes =>
      DiskSession.publishPreparedWrite { state with table, walBytes } event.sequence db.phase.set
        ((commitWalWrite db.dir db.files state.activeFirst event walBytes).adapt onCommitUnknown))

/-- Acknowledgement follows the WAL sync and durable publication of the byte boundary. -/
def DiskTable.write (db : DiskTable) (key : UInt64) (value : Option UInt64) : IO UInt64 :=
  db.writeWith key value id id

/-- Submit a write and report its sequence after durable publication. If the
commit outcome is unknown, close and reopen the database before further use. -/
def DiskTable.writeWithOutcome (db : DiskTable) (key : UInt64) (value : Option UInt64) :
    EIO DiskWriteError UInt64 :=
  db.writeWith key value .rejected .commitUnknown

/-- Project the native single-write preflight onto the reached phase and
no-follow metadata reads, then the existing append and marker callbacks. -/
theorem DiskTable.writeWithOutcome_schedule (db : DiskTable) (key : UInt64) (value : Option UInt64) :
    db.writeWithOutcome key value =
      DiskSession.withPreparedSingleWrite key value
        (db.installed.adapt DiskWriteError.rejected) DiskWriteError.rejected
        (fun result => (fromOption result "write sequence space exhausted").adapt DiskWriteError.rejected)
        (fun state => (checkActiveSegmentWith db.dir state FilePath.symlinkMetadata).adapt DiskWriteError.rejected)
        (fun state event table walBytes =>
          DiskSession.publishPreparedWrite { state with table, walBytes } event.sequence db.phase.set
            ((WalSegmentCommit.commitAt db.dir state.activeFirst event walBytes
              db.files.append db.files.stage db.files.syncPaths IO.FS.rename).adapt DiskWriteError.commitUnknown)) := rfl

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

@[inline] private def DiskTable.writeBatchWith (db : DiskTable)
    (rows : List (UInt64 × Option UInt64)) (onRejected onCommitUnknown : IO.Error → ε) : EIO ε UInt64 := do
  let state ← db.installed.adapt onRejected
  if rows.isEmpty then return state.table.committed
  let walBytes := state.walBytes + WAL.frameSize * rows.length
  unless walBytes < UInt64.size do throw (onRejected (IO.userError "WAL byte count is too large"))
  let (events, table) ← (fromOption (prepareBatch state.table rows)
    "write sequence space exhausted").adapt onRejected
  (checkActiveSegment db.dir state).adapt onRejected
  DiskSession.publishPreparedWrite { state with table, walBytes } table.committed db.phase.set
    ((WalSegmentCommit.commitBytesAt db.dir state.activeFirst (WAL.encodeBatch events) walBytes
      db.files.append db.files.stage db.files.syncPaths IO.FS.rename).adapt onCommitUnknown)

/-- Publish an ordered batch as one durable WAL boundary. Each mutation
gets a consecutive sequence. An empty batch returns the current sequence. -/
def DiskTable.writeBatch (db : DiskTable) (rows : List (UInt64 × Option UInt64)) : IO UInt64 :=
  db.writeBatchWith rows id id

/-- A failed publication has an unknown outcome for the entire batch.
Close and reopen the session before attempting another operation. -/
def DiskTable.writeBatchWithOutcome (db : DiskTable) (rows : List (UInt64 × Option UInt64)) :
    EIO DiskWriteError UInt64 :=
  db.writeBatchWith rows .rejected .commitUnknown

/-- Project the complete batch schedule onto the reached phase, metadata and
publication callbacks. The commit callback is reached only for a prepared
nonempty batch that passed the active-file guard. -/
@[macro_inline] def DiskSession.writeBatchSchedule [Monad m] [MonadExceptOf ε m]
    (rows : List (UInt64 × Option UInt64)) (installed : m Installed) (reject : IO.Error → ε)
    (requirePrepared : Option (List WAL.Write × PackedTable) → m (List WAL.Write × PackedTable))
    (guard : Installed → m Unit) (setPhase : Phase Installed → m Unit)
    (commit : Installed → List WAL.Write → Nat → m Unit) : m UInt64 := do
  let state ← installed
  if rows.isEmpty then return state.table.committed
  let walBytes := state.walBytes + WAL.frameSize * rows.length
  unless walBytes < UInt64.size do throw (reject (IO.userError "WAL byte count is too large"))
  let (events, table) ← requirePrepared (prepareBatch state.table rows)
  guard state
  DiskSession.publishPreparedWrite { state with table, walBytes } table.committed setPhase
    (commit state events walBytes)

theorem DiskTable.writeBatchWithOutcome_schedule (db : DiskTable) (rows : List (UInt64 × Option UInt64)) :
    db.writeBatchWithOutcome rows =
      DiskSession.writeBatchSchedule (m := EIO DiskWriteError) rows
        (db.installed.adapt DiskWriteError.rejected) DiskWriteError.rejected
        (fun result => (fromOption result "write sequence space exhausted").adapt DiskWriteError.rejected)
        (fun state => (checkActiveSegmentWith db.dir state FilePath.symlinkMetadata).adapt DiskWriteError.rejected)
        db.phase.set
        (fun state events bytes => (WalSegmentCommit.commitBytesAt db.dir state.activeFirst (WAL.encodeBatch events)
          bytes db.files.append db.files.stage db.files.syncPaths IO.FS.rename).adapt DiskWriteError.commitUnknown) := rfl

theorem DiskTable.writeBatch_schedule (db : DiskTable) (rows : List (UInt64 × Option UInt64)) :
    db.writeBatch rows =
      DiskSession.writeBatchSchedule (m := IO) rows (db.installed.adapt id) id
        (fun result => (fromOption result "write sequence space exhausted").adapt id)
        (fun state => (checkActiveSegmentWith db.dir state FilePath.symlinkMetadata).adapt id) db.phase.set
        (fun state events bytes => (WalSegmentCommit.commitBytesAt db.dir state.activeFirst (WAL.encodeBatch events)
          bytes db.files.append db.files.stage db.files.syncPaths IO.FS.rename).adapt id) := rfl

/-- Batch acknowledgement follows the same publication schedule as a
single write, with one appended byte string and one selected boundary. -/
theorem DiskTable.writeBatchWithOutcome_fileEffects (db : DiskTable)
    (rows : List (UInt64 × Option UInt64)) :
    db.writeBatchWithOutcome rows = (do
      let state ← db.installed.adapt DiskWriteError.rejected
      if rows.isEmpty then return state.table.committed
      let walBytes := state.walBytes + WAL.frameSize * rows.length
      unless walBytes < UInt64.size do
        throw (.rejected (IO.userError "WAL byte count is too large"))
      let (events, table) ← (fromOption (prepareBatch state.table rows)
        "write sequence space exhausted").adapt DiskWriteError.rejected
      (checkActiveSegment db.dir state).adapt DiskWriteError.rejected
      db.phase.set .poisoned
      (WalSegmentCommit.commitBytesAt db.dir state.activeFirst (WAL.encodeBatch events) walBytes
        db.files.append db.files.stage db.files.syncPaths IO.FS.rename).adapt DiskWriteError.commitUnknown
      db.phase.set (.ready { state with table, walBytes })
      return table.committed) := rfl

/-- The public write schedules use the phase cell and the synchronization
record that the native opener stored in this table. -/
def DiskTable.UsesOpenWriteSchedules (db : DiskTable) (directory : DiskDirectory)
    (files : DiskTable.OpenSyncFiles) (phase : IO.Ref Phase) : Prop :=
  (∀ key value, db.writeWithOutcome key value =
    DiskSession.withPreparedSingleWrite key value
      ((do (← phase.get).installed : IO Installed).adapt DiskWriteError.rejected) DiskWriteError.rejected
      (fun result => (fromOption result "write sequence space exhausted").adapt DiskWriteError.rejected)
      (fun state => (checkActiveSegmentWith directory state FilePath.symlinkMetadata).adapt DiskWriteError.rejected)
      (fun state event table walBytes =>
        DiskSession.publishPreparedWrite { state with table, walBytes } event.sequence phase.set
          ((WalSegmentCommit.commitAt directory state.activeFirst event walBytes
            files.append files.stage files.syncPaths IO.FS.rename).adapt DiskWriteError.commitUnknown))) ∧
  (∀ rows, db.writeBatchWithOutcome rows =
    DiskSession.writeBatchSchedule (m := EIO DiskWriteError) rows
      ((do (← phase.get).installed : IO Installed).adapt DiskWriteError.rejected) DiskWriteError.rejected
      (fun result => (fromOption result "write sequence space exhausted").adapt DiskWriteError.rejected)
      (fun state => (checkActiveSegmentWith directory state FilePath.symlinkMetadata).adapt DiskWriteError.rejected)
      phase.set
      (fun state events bytes => (WalSegmentCommit.commitBytesAt directory state.activeFirst (WAL.encodeBatch events)
        bytes files.append files.stage files.syncPaths IO.FS.rename).adapt DiskWriteError.commitUnknown))

theorem DiskTable.UsesOpenReferences.writeSchedules {db : DiskTable} {directory lock files phase token}
    (uses : db.UsesOpenReferences directory lock files phase token) : db.UsesOpenWriteSchedules directory files phase := by
  obtain ⟨path, _, cache, cell, _⟩ := uses
  constructor <;> intros <;>
    simp only [DiskTable.writeWithOutcome_schedule, DiskTable.writeBatchWithOutcome_schedule, DiskTable.installed, path, cache, cell]

private theorem adaptWriteBind (mapError : ε → ε')
    (action : EIO ε α) (next : α → EIO ε β) :
    (action >>= next).adapt mapError = action.adapt mapError >>= fun value => (next value).adapt mapError := by
  funext world
  change EIO.adapt mapError (EST.bind action next) world =
    EST.bind (action.adapt mapError) (fun value => (next value).adapt mapError) world
  simp only [EIO.adapt, EST.bind]
  cases action world <;> rfl

private theorem adaptWriteAdapt (action : EIO ε α) (first : ε → ε') (second : ε' → ε'') :
    (action.adapt first).adapt second = action.adapt (second ∘ first) := by
  funext world
  unfold EIO.adapt
  cases action world <;> rfl

private theorem adaptWritePure (mapError : ε → ε') (value : α) :
    (pure value : EIO ε α).adapt mapError = pure value := rfl

private theorem adaptWriteThrow (mapError : ε → ε') (cause : ε) :
    (throw cause : EIO ε α).adapt mapError = throw (mapError cause) := rfl

private theorem adaptWriteIf (mapError : ε → ε') (condition : Prop) [Decidable condition]
    (yes no : EIO ε α) :
    (if condition then yes else no).adapt mapError =
      if condition then yes.adapt mapError else no.adapt mapError := by
  split <;> rfl

/-- The plain single-write API forgets the outcome tag after the same
native schedule runs, preserving the reached state and diagnostic. -/
theorem DiskTable.write_eq_adaptOutcome (db : DiskTable) (key : UInt64) (value : Option UInt64) :
    db.write key value = (db.writeWithOutcome key value).adapt DiskWriteError.cause := by
  simp only [write, writeWithOutcome, writeWith, DiskSession.withPreparedSingleWrite,
    DiskSession.publishPreparedWrite, DiskSession.publishPrepared, adaptWriteBind, adaptWriteAdapt,
    adaptWritePure, adaptWriteThrow, adaptWriteIf]
  rfl

/-- The plain batch API forgets the outcome tag after the same native
schedule runs, including the no-op return for an empty batch. -/
theorem DiskTable.writeBatch_eq_adaptOutcome (db : DiskTable) (rows : List (UInt64 × Option UInt64)) :
    db.writeBatch rows = (db.writeBatchWithOutcome rows).adapt DiskWriteError.cause := by
  simp only [writeBatch, writeBatchWithOutcome, writeBatchWith, DiskSession.publishPreparedWrite,
    DiskSession.publishPrepared, adaptWriteBind, adaptWriteAdapt, adaptWritePure, adaptWriteThrow, adaptWriteIf]
  rfl

def DiskTable.acquireAt (db : DiskTable) (snapshot : UInt64) : IO (Option DiskSnapshotPin) := do
  let state ← db.installed
  match state.table.acquireAt snapshot with
  | none => return none
  | some (pin, table) =>
    db.phase.set (.ready { state with table })
    return some ⟨⟨db.session, pin.handle⟩, pin.sequence⟩

/-- Project the native snapshot acquisition onto the phase and token
callbacks of the reached session. -/
@[macro_inline] def DiskSession.acquireSnapshotWith [Monad m]
    (installed : m DiskSession.Installed) (record : DiskSession.Phase DiskSession.Installed → m Unit)
    (issued : Alvoki.Sequential.SnapshotPin → α) (snapshot : UInt64) : m (Option α) := do
  let state ← installed
  match state.table.acquireAt snapshot with
  | none => return none
  | some (pin, table) =>
    record (.ready { state with table })
    return some (issued pin)

theorem DiskTable.acquireAt_schedule (db : DiskTable) (snapshot : UInt64) :
    db.acquireAt snapshot = DiskSession.acquireSnapshotWith (m := IO) db.installed db.phase.set
      (fun pin => ⟨⟨db.session, pin.handle⟩, pin.sequence⟩) snapshot := rfl

/-- The returned pin carries the exact token of its issuing table
and the local handle and sequence produced by the pure pin allocator. -/
def DiskSnapshotPin.UsesOpenToken (pin : DiskSnapshotPin) (token : IO.Ref Unit)
    (issued : Alvoki.Sequential.SnapshotPin) : Prop :=
  pin.handle.session = token ∧ pin.handle.localHandle = issued.handle ∧ pin.sequence = issued.sequence

/-- On the handle returned by open, the actual public acquisition uses
the reported phase cell for both its read and its possible update. -/
theorem DiskTable.UsesOpenReferences.acquireAt {db : DiskTable} {directory lock files phase token}
    (uses : db.UsesOpenReferences directory lock files phase token) (snapshot : UInt64) :
    ∃ issue : Alvoki.Sequential.SnapshotPin → DiskSnapshotPin,
      (∀ pin, (issue pin).UsesOpenToken token pin) ∧
      db.acquireAt snapshot = DiskSession.acquireSnapshotWith (m := IO)
        (do (← phase.get).installed) phase.set issue snapshot := by
  obtain ⟨_, _, _, cell, identity⟩ := uses
  refine ⟨fun pin => ⟨⟨token, pin.handle⟩, pin.sequence⟩, fun _ => ⟨rfl, rfl, rfl⟩, ?_⟩
  simp only [DiskTable.acquireAt_schedule, DiskTable.installed, cell, identity]

def DiskTable.acquire (db : DiskTable) : IO DiskSnapshotPin := do
  let state ← db.installed
  fromOption (← db.acquireAt state.table.committed) "cannot acquire the latest snapshot"

/-- Read the committed sequence, then acquire it through the same pinned
snapshot action used for an explicit sequence. -/
@[macro_inline] def DiskSession.acquireLatestWith [Monad m] [MonadExceptOf IO.Error m]
    (installed : m DiskSession.Installed) (acquireAt : UInt64 → m (Option α)) : m α := do
  let state ← installed
  match ← acquireAt state.table.committed with
  | some pin => pure pin
  | none => throw (IO.userError "cannot acquire the latest snapshot")

theorem DiskTable.acquire_schedule (db : DiskTable) :
    db.acquire = DiskSession.acquireLatestWith (m := IO) db.installed
      (DiskSession.acquireSnapshotWith db.installed db.phase.set
        (fun pin => ⟨⟨db.session, pin.handle⟩, pin.sequence⟩)) := rfl

def DiskTable.release (db : DiskTable) (handle : DiskSnapshotHandle) : IO Unit :=
  DiskSession.withLocalHandle db.installed (handle.session.ptrEq db.session) () fun state =>
    db.phase.set (.ready { state with table := state.table.release handle.localHandle })

/-- Apply the release update only after the ready and local handle checks. -/
@[macro_inline] def DiskSession.releaseSnapshotWith [Monad m]
    (installed : m DiskSession.Installed) (sameSession : m Bool)
    (record : DiskSession.Phase DiskSession.Installed → m Unit)
    (handle : Alvoki.Sequential.SnapshotHandle) : m Unit :=
  DiskSession.withLocalHandle installed sameSession () fun state =>
    record (.ready { state with table := state.table.release handle })

theorem DiskTable.release_schedule (db : DiskTable) (handle : DiskSnapshotHandle) :
    db.release handle = DiskSession.releaseSnapshotWith (m := IO) db.installed
      (handle.session.ptrEq db.session) db.phase.set handle.localHandle := rfl

/-- Release compares the presented pin's token and updates the phase
cell belonging to this opened table. -/
theorem DiskTable.UsesOpenReferences.releasePin {db : DiskTable} {directory lock files phase token}
    (uses : db.UsesOpenReferences directory lock files phase token) {pin : DiskSnapshotPin}
    {issuer : IO.Ref Unit} {issued : Alvoki.Sequential.SnapshotPin} (owns : pin.UsesOpenToken issuer issued) :
    db.release pin.handle = DiskSession.releaseSnapshotWith (m := IO) (do (← phase.get).installed)
      (issuer.ptrEq token) phase.set issued.handle := by
  obtain ⟨_, _, _, cell, session⟩ := uses
  obtain ⟨tokenOfPin, handle, _⟩ := owns
  simp only [DiskTable.release_schedule, DiskTable.installed, cell, session, tokenOfPin, handle]

def DiskTable.lookup (db : DiskTable) (handle : DiskSnapshotHandle) (key : UInt64) :
    IO (Option (Option UInt64)) :=
  DiskSession.withLocalHandle db.installed (handle.session.ptrEq db.session) none fun state =>
    pure (state.table.lookup handle.localHandle key)

def DiskTable.range (db : DiskTable) (handle : DiskSnapshotHandle) (lo hi : UInt64) :
    IO (Option (List (Alvoki.Compaction.Model.Entry (Option UInt64)))) :=
  DiskSession.withLocalHandle db.installed (handle.session.ptrEq db.session) none fun state =>
    pure (state.table.range handle.localHandle lo hi)

/-- Read the reached ready table when the requested pin belongs to the session. -/
@[macro_inline] def DiskSession.readSnapshotWith [Monad m]
    (installed : m DiskSession.Installed) (sameSession : m Bool)
    (read : PackedTable → Option α) : m (Option α) :=
  DiskSession.withLocalHandle installed sameSession none (fun state => pure (read state.table))

theorem DiskTable.lookup_schedule (db : DiskTable) (handle : DiskSnapshotHandle) (key : UInt64) :
    db.lookup handle key = DiskSession.readSnapshotWith (m := IO) db.installed
      (handle.session.ptrEq db.session) (fun table => table.lookup handle.localHandle key) := rfl

theorem DiskTable.range_schedule (db : DiskTable) (handle : DiskSnapshotHandle) (lo hi : UInt64) :
    db.range handle lo hi = DiskSession.readSnapshotWith (m := IO) db.installed
      (handle.session.ptrEq db.session) (fun table => table.range handle.localHandle lo hi) := rfl

/-- The actual lookup uses the same cell and compares the table's
token to itself when given a pin issued by that table. -/
theorem DiskTable.UsesOpenReferences.lookupPin {db : DiskTable} {directory lock files phase token}
    (uses : db.UsesOpenReferences directory lock files phase token)
    {pin : DiskSnapshotPin} {issued : Alvoki.Sequential.SnapshotPin} (owns : pin.UsesOpenToken token issued)
    (key : UInt64) :
    db.lookup pin.handle key = DiskSession.readSnapshotWith (m := IO) (do (← phase.get).installed)
      (token.ptrEq token) (fun table => table.lookup issued.handle key) := by
  obtain ⟨_, _, _, cell, session⟩ := uses
  obtain ⟨tokenOfPin, handle, _⟩ := owns
  simp only [DiskTable.lookup_schedule, DiskTable.installed, cell, session, tokenOfPin, handle]

/-- The public range follows the same phase-cell and token guard. -/
theorem DiskTable.UsesOpenReferences.rangePin {db : DiskTable} {directory lock files phase token}
    (uses : db.UsesOpenReferences directory lock files phase token)
    {pin : DiskSnapshotPin} {issued : Alvoki.Sequential.SnapshotPin} (owns : pin.UsesOpenToken token issued)
    (lo hi : UInt64) :
    db.range pin.handle lo hi = DiskSession.readSnapshotWith (m := IO) (do (← phase.get).installed)
      (token.ptrEq token) (fun table => table.range issued.handle lo hi) := by
  obtain ⟨_, _, _, cell, session⟩ := uses
  obtain ⟨tokenOfPin, handle, _⟩ := owns
  simp only [DiskTable.range_schedule, DiskTable.installed, cell, session, tokenOfPin, handle]

def DiskTable.advanceFloor (db : DiskTable) (floor : UInt64) : IO Bool := do
  let state ← db.installed
  let some table := state.table.advanceFloor floor | return false
  db.phase.set (.ready { state with table })
  return true

/-- Update only the ready phase, and only when the current pins permit the new floor. -/
@[macro_inline] def DiskSession.advanceFloorWith [Monad m]
    (installed : m DiskSession.Installed) (record : DiskSession.Phase DiskSession.Installed → m Unit)
    (floor : UInt64) : m Bool := do
  let state ← installed
  let some table := state.table.advanceFloor floor | return false
  record (.ready { state with table })
  return true

theorem DiskTable.advanceFloor_schedule (db : DiskTable) (floor : UInt64) :
    db.advanceFloor floor = DiskSession.advanceFloorWith (m := IO) db.installed db.phase.set floor := rfl

/-- The floor guard uses the reached phase and any update writes back
through the same opened phase cell. -/
theorem DiskTable.UsesOpenReferences.advanceFloor {db : DiskTable} {directory lock files phase token}
    (uses : db.UsesOpenReferences directory lock files phase token) (floor : UInt64) :
    db.advanceFloor floor = DiskSession.advanceFloorWith (m := IO)
      (do (← phase.get).installed) phase.set floor := by
  obtain ⟨_, _, _, cell, _⟩ := uses
  simp only [DiskTable.advanceFloor_schedule, DiskTable.installed, cell]

/-- Commit an in-memory run rewrite only when the reached table accepts it. -/
@[macro_inline] def DiskSession.rewriteRunWith [Monad m]
    (installed : m DiskSession.Installed) (record : DiskSession.Phase DiskSession.Installed → m Unit)
    (rewrite : PackedTable → Option PackedTable) : m Bool := do
  let state ← installed
  let some table := rewrite state.table | return false
  record (.ready { state with table })
  return true

def DiskTable.compact (db : DiskTable) (index : Nat) : IO Bool := do
  let state ← db.installed
  let some table := state.table.compact index | return false
  db.phase.set (.ready { state with table })
  return true

theorem DiskTable.compact_schedule (db : DiskTable) (index : Nat) :
    db.compact index = DiskSession.rewriteRunWith (m := IO) db.installed db.phase.set
      (fun table => table.compact index) := rfl

/-- Rewrite one run at the current snapshot floor. Call `checkpoint`
to publish the rewritten run, then collect the superseded generation. -/
def DiskTable.retainRunVersions (db : DiskTable) (index : Nat) : IO Bool := do
  let state ← db.installed
  let some table := state.table.retainRunVersions index | return false
  db.phase.set (.ready { state with table })
  return true

/-- Only a successful packed rewrite changes the installed table. -/
theorem DiskTable.retainRunVersions_fileEffects (db : DiskTable) (index : Nat) :
    db.retainRunVersions index = (do
      let state ← (← db.phase.get).installed
      let some table := state.table.retainRunVersions index | return false
      db.phase.set (.ready { state with table })
      return true) := rfl

theorem DiskTable.retainRunVersions_schedule (db : DiskTable) (index : Nat) :
    db.retainRunVersions index = DiskSession.rewriteRunWith (m := IO) db.installed db.phase.set
      (fun table => table.retainRunVersions index) := rfl

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

/-- Separate the checkpoint's preparation from its phase and file changes.
The publication callback receives the exact next writer state and manifest. -/
@[macro_inline] def DiskSession.withPreparedCheckpoint [Monad m] [MonadExceptOf IO.Error m]
    (installed : m DiskSession.Installed) (validate : {α : Type} → Except String α → m α)
    (publish : DiskSession.Installed → ByteArray → m Unit) : m Unit := do
  let state ← installed
  let table ← flushForCheckpoint state.table validate
  let next := state.generation.toNat + 1
  unless next < UInt64.size ∧ table.runs.length < UInt64.size do
    throw (IO.userError "checkpoint generation or run count is too large")
  let generation := UInt64.ofNat next
  let manifest ← validate (encodeCheckpointIntegrityManifest table generation)
  publish { state with table, generation } manifest

/-- The same preparation guards consume the native phase read before the
actual checkpoint writes the poisoned phase or issues its file schedule. -/
theorem DiskTable.checkpoint_schedule (db : DiskTable) :
    db.checkpoint = DiskSession.withPreparedCheckpoint (do (← db.phase.get).installed) IO.ofExcept
      (fun next manifest => do
        db.phase.set .poisoned
        CheckpointPublication.run next.table.runs.length
          (performCheckpointFileStep db.dir next.generation next.table.runs.toArray (db.dir.file .stagedManifest)
            manifest (fromOption · "checkpoint run index is out of bounds")
            (writeRunFlushed db.files) db.files.stage db.files.syncPaths IO.FS.rename)
        db.phase.set (.ready next)) := by
  rw [db.checkpoint_fileEffects]
  rfl

/-- The public checkpoint uses the opened phase cell for its read and
both setters, and passes the opened synchronization record to every
run and manifest callback. -/
def DiskTable.UsesOpenCheckpointSchedule (db : DiskTable) (directory : DiskDirectory)
    (files : DiskTable.OpenSyncFiles) (phase : IO.Ref Phase) : Prop :=
    db.checkpoint = DiskSession.withPreparedCheckpoint (do (← phase.get).installed) IO.ofExcept
      (fun next manifest => DiskSession.publishPrepared phase.set
        (CheckpointPublication.run next.table.runs.length
          (performCheckpointFileStep directory next.generation next.table.runs.toArray (directory.file .stagedManifest)
            manifest (fromOption · "checkpoint run index is out of bounds")
            (writeRunFlushed files) files.stage files.syncPaths IO.FS.rename))
        (phase.set (.ready next)))

theorem DiskTable.UsesOpenReferences.checkpoint {db : DiskTable} {directory lock files phase token}
    (uses : db.UsesOpenReferences directory lock files phase token) :
    db.UsesOpenCheckpointSchedule directory files phase := by
  obtain ⟨path, _, cache, cell, _⟩ := uses
  simp only [DiskTable.UsesOpenCheckpointSchedule, DiskTable.checkpoint_schedule, path, cache, cell,
    DiskSession.publishPrepared]

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
  let entries ← readDirectoryChecked db.dir.path
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
      let entries ← readDirectoryChecked db.dir.path
      let selected ← selectRunFilesWith db.dir current (retainRunGeneration state.generation heldGenerations)
        (fun path => do
          match ← path.symlinkMetadata.toBaseIO with
          | .ok metadata => return .ok metadata.type
          | .error (.noFileOrDirectory _ 2 _) => return .error "run file is absent"
          | .error error => throw error) (entries.toList.map (·.fileName))
      RunCollection.run selected (RunCollection.performPaths (fun path => (IO.FS.removeFile path).toBaseIO)
        (fun path => db.files.syncPaths #[path]) throw (fun (generation, index) => db.dir.file (.run generation index))
        db.dir.path)) := rfl

/-- The native cached metadata reader opens only after a regular no-follow
lookup. The opened handle determines all subsequent reads. -/
@[macro_inline] def readOptionalCachedOpenFileWith [Monad m] [MonadExceptOf IO.Error m]
    (directory : DiskDirectory) (path : FilePath) (lookup : m (Except IO.Error IO.FS.Metadata))
    (openRead : FilePath → m handle) (read : handle → USize → m ByteArray) : m (Option ByteArray) :=
  readOptionalDatabaseFileWithMetadata lookup (fun metadata => do
    let file ← openRead path
    if path == directory.file .walBoundary then
      readPrefixUntilEofWith (IO.userError "invalid WAL boundary length") (read file)
        WAL.Boundary.acquisitionLimit ByteArray.empty
    else
      readIntegrityManifestPrefixWith (read file) metadata.byteSize.toNat)
    (fun _ => IO.userError s!"expected a regular database file: '{path}'") throw

theorem readOptionalCachedOpenFile_fileEffects (directory : DiskDirectory) (path : FilePath) :
    readOptionalCachedOpenFile directory path =
      readOptionalCachedOpenFileWith (m := IO) directory path path.symlinkMetadata.toBaseIO
        (fun file => IO.FS.Handle.mk file .read) IO.FS.Handle.read := rfl

/-- The inventory callback checks the no-follow result before returning
its metadata to the extent planner. -/
@[macro_inline] def inspectWalSegmentWith [Monad m] [MonadExceptOf IO.Error m]
    (path : FilePath) (lookup : m (Except IO.Error IO.FS.Metadata)) : m (Except IO.Error IO.FS.Metadata) := do
  let report ← lookup
  if let .ok metadata := report then checkPrivateRegularWith path metadata
  pure report

theorem inspectWalSegment_fileEffects (path : FilePath) :
    inspectWalSegment path =
      inspectWalSegmentWith (m := IO) path path.symlinkMetadata.toBaseIO := rfl

theorem readSealedWalPrefix_fileEffects (path : FilePath) (count : Nat) :
    readSealedWalPrefix path count = (do
      let file ← IO.FS.Handle.mk path .read
      readExactPrefixWith WalSegmentRepair.selectedWalSpanError file.read count ByteArray.empty) := rfl

theorem readKeeperPrefix_fileEffects (files : SyncFiles) (path : FilePath) (count fileSize : Nat) :
    readKeeperPrefix files path count fileSize =
      SyncHandleRouting.readKeeperWith (fun name => IO.FS.Handle.mk name .read)
        (fun file size => readExactPrefixWith (IO.userError "short or oversized WAL keeper read")
          file.read size ByteArray.empty)
        files.remember path count fileSize := rfl

/-- The aligned keeper and its barriers use the same cells assembled by
the cache initializer. Remembering the read handle modifies the pending
cell that the keeper sync later reads and clears. -/
theorem DiskTable.OpenSyncFiles.keeperCacheSchedules {files : DiskTable.OpenSyncFiles}
    {dir : FilePath} {active pending directory}
    (uses : files.UsesCacheReferences active pending directory) (atDirectory : files.AtDirectory dir)
    (path : FilePath) (count fileSize : Nat) (paths : Array FilePath) :
    readKeeperPrefix files path count fileSize =
      SyncHandleRouting.readKeeperWith (fun name => IO.FS.Handle.mk name .read)
        (fun file size => readExactPrefixWith (IO.userError "short or oversized WAL keeper read") file.read size ByteArray.empty)
        (fun name file => pending.modify (SyncHandleRouting.pushPending name file)) path count fileSize ∧
    files.syncPaths paths = SyncPathGroup.run (fun name =>
      SyncHandleRouting.syncWithHandles dir name directory.get pending.get pending.set active.get
        (fun file => IO.FS.Handle.mk file .read) fsyncHandle) paths := by
  obtain ⟨rfl, rfl, rfl⟩ := uses
  cases atDirectory
  exact ⟨rfl, rfl⟩

/-- A successful stage remembers the descriptor returned by the native
fresh write and flush. -/
theorem syncFilesStage_schedule (files : SyncFiles) (path : FilePath) (bytes : ByteArray) :
    files.stage path bytes = (writeFreshStagedHandle path bytes >>= files.remember path) := rfl

end Alvoki.Storage
