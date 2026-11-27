import Alvoki.Storage.Disk.Proofs.Read.NativeReadRecoveryTrace
import Alvoki.Storage.Disk.Proofs.Append.BatchAppendRecoveryPrefix
import Alvoki.Storage.Disk.Proofs.Read.SnapshotReadHistoryBounds

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentCommit WalSegmentRepair
open WAL.Boundary

private abbrev AppendFiles := DescriptorInventory × WriteFiles
private abbrev AppendState := CensusDirectoryCache × AppendFiles
private abbrev AppendStop := FilePath × ByteArray
private abbrev AppendM := ExceptT IO.Error (EStateM AppendStop AppendState)

private def projectAppendOpen
    (openAppend : FilePath → EStateM IO.Error AppendFiles CheckpointOpenHandle)
    (census : DescriptorInventory) (path : FilePath) : EStateM IO.Error WriteFiles CheckpointOpenHandle :=
  fun files => match openAppend path (census, files) with
    | .ok file (_, after) => .ok file after
    | .error cause (_, after) => .error cause after

/-- A stop at the first issued WAL data write. The no-follow guard and
the append open or cache hit identify the same canonical keeper. The
outer stop records the issued path and bytes before flush or marker work. -/
structure NativeFirstAppendStop {state : NativeReadyState} (prepared : NativeReadyWritePreparation state) where
  request : WriteRequest
  rows : request.rows = prepared.rows
  root : DeviceInode
  view : DirectoryReadNamespace
  keeper : RunChildLookup root prepared.keeperName view
  lock : RunChildLookup root "LOCK" view
  marker : RunChildLookup root "WAL.commit" view
  stat : FilePath → Except IO.Error (IO.FS.Metadata × Nat)
  metadata : IO.FS.Metadata
  statReturned : stat prepared.keeperPath = .ok (metadata, view.modelObject keeper.child)
  regular : metadata.type = .file
  privateFile : metadata.numLinks = 1
  extent : metadata.byteSize.toNat = state.writer.installed.walBytes - state.writer.installed.activeFirst * WAL.frameSize
  openAppend : FilePath → EStateM IO.Error AppendFiles CheckpointOpenHandle
  openInventory : ∀ handle reached,
    openAppend prepared.keeperPath (state.census, prepared.initial) = .ok handle reached → reached.1 = handle.1
  handle : CheckpointOpenHandle
  selectedCensus : DescriptorInventory
  selects : NativeReadyKeeperSelection prepared keeper (projectAppendOpen openAppend state.census) handle selectedCensus
  drops : List LockReferenceDrop
  keeperRetained : handle.2.1 ∈ (selectedCensus.afterDrops drops).slots
  ownerRetained : state.owner ∈ (selectedCensus.afterDrops drops).slots
  directoryRetained : state.directorySlot ∈ (selectedCensus.afterDrops drops).slots
  rawWrite : CheckpointOpenHandle → ByteArray → EStateM AppendStop AppendFiles (Except IO.Error Unit)
  cut : FirstAppendCut
  stopped : rawWrite handle (WAL.encodeBatch prepared.batch) (selectedCensus, prepared.initial) =
    .error (prepared.keeperPath, WAL.encodeBatch prepared.batch)
      (selectedCensus.afterDrops drops, cut.writeFiles state.writer.history (state.files.image.directory.staged .walBoundary))
  visiblePrefix : ∃ suffix, cut.visibleTail ++ suffix = WAL.encodeBatch prepared.batch
  directoryIdentity : view.modelObject root = state.census.inode state.directorySlot.description
  cachedDirectory : ∃ captured, state.cache.directory = some (captured, state.directorySlot, 0) ∧
    captured.inode state.directorySlot.description = view.modelObject root
  lockIdentity : view.modelObject lock.child = state.census.inode state.owner.description
  bindings : AppendFiles → FilePath → Option Nat
  heldBindings : ∀ files ∈ [(selectedCensus, prepared.initial),
      (selectedCensus.afterDrops drops, cut.writeFiles state.writer.history (state.files.image.directory.staged .walBoundary))],
    bindings files state.session.directory.path = some (view.modelObject root) ∧
    bindings files (state.session.directory.file .lock) = some (view.modelObject lock.child) ∧
    bindings files prepared.keeperPath = some (view.modelObject keeper.child) ∧
    bindings files prepared.markerPath = some (view.modelObject marker.child)

namespace NativeFirstAppendStop

variable {state : NativeReadyState} {prepared : NativeReadyWritePreparation state}

def lookup (stop : NativeFirstAppendStop prepared) (path : FilePath) : Except IO.Error IO.FS.Metadata :=
  (stop.stat path).map Prod.fst

def cutFiles (stop : NativeFirstAppendStop prepared) : AppendFiles :=
  (stop.selectedCensus.afterDrops stop.drops,
    stop.cut.writeFiles state.writer.history (state.files.image.directory.staged .walBoundary))

def session (_stop : NativeFirstAppendStop prepared) : SegmentedSession := { state.session with phase := .poisoned }

private def liftAppendOpen (openAppend : FilePath → EStateM IO.Error AppendFiles CheckpointOpenHandle)
    (path : FilePath) : AppendM CheckpointOpenHandle :=
  fun (cache, files) => match openAppend path files with
    | .ok opened after => .ok (.ok opened) (cache, after)
    | .error cause after => .ok (.error cause) (cache, after)

private def writeFile (stop : NativeFirstAppendStop prepared) (handle : CheckpointOpenHandle) (bytes : ByteArray) :
    AppendM Unit :=
  fun (cache, files) => match stop.rawWrite handle bytes files with
    | .ok value after => .ok value (cache, after)
    | .error tag after => .error tag (cache, after)

private theorem opensSelected {root : DeviceInode} {view : DirectoryReadNamespace}
    {keeper : RunChildLookup root prepared.keeperName view}
    {openAppend : FilePath → EStateM IO.Error AppendFiles CheckpointOpenHandle}
    {handle : CheckpointOpenHandle} {reached : DescriptorInventory}
    (selected : NativeReadyKeeperSelection prepared keeper (projectAppendOpen openAppend state.census) handle reached)
    (inventory : ∀ handle reached,
      openAppend prepared.keeperPath (state.census, prepared.initial) = .ok handle reached → reached.1 = handle.1) :
    selectAppendHandle (m := AppendM) state.cache.active (liftAppendOpen openAppend) prepared.keeperPath
      (state.cache, state.census, prepared.initial) =
    .ok (.ok handle) (state.cache, reached, prepared.initial) := by
  cases selected with
  | fresh slot offset cold free fresh resolved identity opened =>
    cases raw : openAppend prepared.keeperPath (state.census, prepared.initial) with
    | error cause after =>
      simp [projectAppendOpen, raw] at opened
    | ok handle after =>
      have atFiles := inventory handle after raw
      have projected := opened
      simp only [projectAppendOpen, raw, EStateM.Result.ok.injEq] at projected
      have afterEq : after = (handle.1, prepared.initial) := Prod.ext atFiles projected.2
      rw [afterEq, projected.1] at raw
      simp only [selectAppendHandle, cold, liftAppendOpen, raw]
  | cached handle found live inode identity =>
    simp [selectAppendHandle, found, Pure.pure, ExceptT.pure, ExceptT.mk, EStateM.pure]

/-- Execute the native append helper. The stop bypasses both the ordinary
error cleanup and the flush and cache update of a successful append. -/
def append (stop : NativeFirstAppendStop prepared) (flush : CheckpointOpenHandle → AppendM Unit)
    (path : FilePath) (bytes : ByteArray) : AppendM Unit :=
  appendWithActive (fun before => .ok (.ok before.1.active) before)
    (fun active (cache, files) => .ok (.ok ()) ({ cache with active }, files))
    (liftAppendOpen stop.openAppend) stop.writeFile flush path bytes

theorem stopsAppend (stop : NativeFirstAppendStop prepared) (flush : CheckpointOpenHandle → AppendM Unit) :
    stop.append flush prepared.keeperPath (WAL.encodeBatch prepared.batch)
      (state.cache, state.census, prepared.initial) =
    .error (prepared.keeperPath, WAL.encodeBatch prepared.batch) (state.cache, stop.cutFiles) := by
  have issued : stop.writeFile stop.handle (WAL.encodeBatch prepared.batch)
        (state.cache, stop.selectedCensus, prepared.initial) =
      .error (prepared.keeperPath, WAL.encodeBatch prepared.batch) (state.cache, stop.cutFiles) := by
    simp only [writeFile, stop.stopped, cutFiles]
  simp [append, appendWithActive, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, EStateM.bind,
    MonadExcept.tryCatch, MonadExceptOf.tryCatch, tryCatchThe, ExceptT.tryCatch,
    opensSelected stop.selects stop.openInventory, issued]

def logical (stop : NativeFirstAppendStop prepared) : BatchAppendInterruption state.session.directory state.writer :=
  ⟨prepared.rows, prepared.batch, prepared.table, stop.lookup, (prepared.keeperPath, WAL.encodeBatch prepared.batch), stop.cut⟩

theorem valid (stop : NativeFirstAppendStop prepared) : stop.logical.Valid := by
  have lookup : stop.lookup prepared.keeperPath = .ok stop.metadata := by
    rw [NativeFirstAppendStop.lookup, stop.statReturned]
    rfl
  exact ⟨prepared.prepared, prepared.nonempty, prepared.fits,
    ⟨stop.metadata, lookup, stop.regular, stop.privateFile, stop.extent⟩, rfl⟩

private theorem acceptsGuard (stop : NativeFirstAppendStop prepared) :
    checkActiveSegmentWith state.session.directory state.writer.installed stop.lookup = .ok () := by
  obtain ⟨metadata, found, regular, privateFile, extent⟩ := stop.valid.activeGuard
  change stop.lookup prepared.keeperPath = .ok metadata at found
  have kind : (IO.FS.FileType.file == .file) = true := rfl
  simp [checkActiveSegmentWith, checkPrivateRegularWith, found, regular, privateFile, extent, kind,
    Except.bind, Bind.bind, Except.pure, Pure.pure]

def run (stop : NativeFirstAppendStop prepared) (flush : CheckpointOpenHandle → AppendM Unit)
    (stage : FilePath → ByteArray → AppendM Unit) (sync : Array FilePath → AppendM Unit)
    (rename : FilePath → FilePath → AppendM Unit) :=
  stop.request.runWithInterruption state.session.directory stop.lookup
    (fun installed events bytes => commitBytesAt state.session.directory installed.activeFirst (WAL.encodeBatch events) bytes
      (stop.append flush) stage sync rename)
    (state.session.phase, ⟨(state.cache, state.census, prepared.initial), state.files.owners⟩)

theorem stopsWrite (stop : NativeFirstAppendStop prepared) (valid : state.Valid) (flush stage sync rename) :
    stop.run flush stage sync rename =
      .error stop.logical.appendCall (.poisoned, ⟨(state.cache, stop.cutFiles), state.files.owners⟩) := by
  let publish : Installed → List WAL.Write → Nat → AppendM Unit :=
    fun installed events bytes => commitBytesAt state.session.directory installed.activeFirst (WAL.encodeBatch events) bytes
      (stop.append flush) stage sync rename
  let entry : LockedFileState AppendState := ⟨(state.cache, state.census, prepared.initial), state.files.owners⟩
  have issued : (publish state.writer.installed prepared.batch prepared.count).run entry.image =
      .error stop.logical.appendCall (state.cache, stop.cutFiles) := by
    simp [publish, commitBytesAt, WAL.Boundary.commit, Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk,
      EStateM.bind, entry, stop.stopsAppend, logical]
  have batch := runBatchWriteWithInterruption_stopped prepared.nonempty prepared.prepared prepared.fits
    stop.acceptsGuard publish (before := entry) issued
  change stop.request.runWithInterruption state.session.directory stop.lookup publish (state.session.phase, entry) = _
  rw [valid.phase]
  cases request : stop.request with
  | batch rows =>
    have same : rows = prepared.rows := (congrArg WriteRequest.rows request).symm.trans stop.rows
    simpa only [WriteRequest.runWithInterruption, same] using batch
  | single key value =>
    have rows : [(key, value)] = prepared.rows := (congrArg WriteRequest.rows request).symm.trans stop.rows
    have preparedSingle := prepared.prepared
    rw [← rows, prepareBatch_singleton, prepareWrite] at preparedSingle
    have wrote : state.writer.installed.table.write key value = some prepared.table := by
      cases result : state.writer.installed.table.write key value with
      | none => simp [result] at preparedSingle
      | some next =>
        simp only [result, Option.map_some, Option.some.injEq, Prod.mk.injEq] at preparedSingle
        exact congrArg some preparedSingle.2
    simpa only [WriteRequest.runWithInterruption, runSingleWriteWithInterruption_eq_singleton wrote, rows] using batch

def files (stop : NativeFirstAppendStop prepared) : FileImage :=
  FirstAppendCut.projectReached state.writer stop.cutFiles.2

/-- Every admitted tail, including a partial visible write or a torn
crash payload, leaves the marker-selected keeper prefix unchanged. -/
theorem selectsPrior (stop : NativeFirstAppendStop prepared) (valid : state.Valid) :
    stop.files.directory = state.files.image.directory ∧ stop.files.kept = state.files.image.kept ∧
    stop.files.directory.active = state.writer.target.pair ∧
    stop.files.directory.crashImages = [state.writer.target.pair] ∧
    stop.files.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64) ∧
    SelectedIntegrityCheckpoint state.writer.published.durable stop.files.directory.active.manifest state.writer.checkpoint ∧
    (∀ choice ∈ stop.files.keeper.active :: stop.files.keeper.crashImages, ∃ bytes,
      choice = some bytes ∧
      (stop.files.directory.active.walBoundary.mapM fun marker => do
        let count ← WAL.Boundary.decode marker
        selectRetained state.writer.installed.activeFirst count bytes) = .ok (some state.writer.wal.active.bytes)) := by
  let ready := valid.retained
  have pair : stop.files.directory.active = state.writer.target.pair := ready.resumed.ready.selected
  refine ⟨rfl, rfl, pair, ready.resumed.ready.settled, ?_, pair.symm ▸ ready.resumed.selected, ?_⟩
  · rw [pair]
    exact (ready.selectPriorKeeper ByteArray.empty).1
  · let prefixBytes := WAL.encode (state.writer.history.drop state.writer.wal.active.first)
    have readPrefix (tail : ByteArray) :
        (stop.files.directory.active.walBoundary.mapM fun marker => do
          let count ← WAL.Boundary.decode marker
          selectRetained state.writer.installed.activeFirst count (prefixBytes ++ tail)) =
        .ok (some state.writer.wal.active.bytes) := by
      rw [pair, (ready.selectPriorKeeper tail).1, Option.mapM, WAL.Boundary.decode_encode]
      change (some <$> selectRetained state.writer.installed.activeFirst (WAL.encode state.writer.history).size.toUInt64
        (prefixBytes ++ tail)) = _
      rw [(ready.selectPriorKeeper tail).2]
      rfl
    intro choice member
    change choice ∈ some (prefixBytes ++ stop.cut.visibleTail) ::
      (ByteArray.empty :: stop.cut.crashTails).map (fun tail => some (prefixBytes ++ tail)) at member
    rcases List.mem_cons.mp member with rfl | survived
    · exact ⟨_, rfl, readPrefix _⟩
    · obtain ⟨tail, _, rfl⟩ := List.mem_map.mp survived
      exact ⟨_, rfl, readPrefix tail⟩

end NativeFirstAppendStop

/-- The exact outer stop is a terminal native execution step. A newly
opened keeper slot may be live without having entered the active cache.
The attempted group occurs once in the ledger and selects no new frames. -/
structure NativePendingFirstAppend (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} (stop : NativeFirstAppendStop prepared) : Prop where
  stopped : ∀ flush stage sync rename, stop.run flush stage sync rename =
    .error stop.logical.appendCall (.poisoned, ⟨(current.state.cache, stop.cutFiles), current.state.files.owners⟩)
  held : current.state.files.owners.Owns current.state.session.directory current.state.session.descriptor
  phase : stop.session.phase = .poisoned
  census : stop.cutFiles.1 = stop.selectedCensus.afterDrops stop.drops
  inodes : stop.cutFiles.1.inode = current.state.census.inode
  keeperIssued : stop.handle.2.1 ∈ stop.selectedCensus.slots
  keeperLive : stop.handle.2.1 ∈ stop.cutFiles.1.slots
  lockLive : current.state.owner ∈ stop.cutFiles.1.slots
  directoryLive : current.state.directorySlot ∈ stop.cutFiles.1.slots
  keeperCapture : stop.handle.1.inode stop.handle.2.1.description = stop.cutFiles.1.inode stop.handle.2.1.description
  keeperIdentity : stop.bindings stop.cutFiles prepared.keeperPath = some (stop.cutFiles.1.inode stop.handle.2.1.description)
  lockIdentity : stop.bindings stop.cutFiles (current.state.session.directory.file .lock) =
    some (stop.cutFiles.1.inode current.state.owner.description)
  directoryIdentity : stop.bindings stop.cutFiles current.state.session.directory.path =
    some (stop.cutFiles.1.inode current.state.directorySlot.description)
  markerIdentity : stop.bindings stop.cutFiles prepared.markerPath = some (stop.view.modelObject stop.marker.child)
  directoryCapture : ∃ captured, current.state.cache.directory = some (captured, current.state.directorySlot, 0) ∧
    captured.inode current.state.directorySlot.description = stop.cutFiles.1.inode current.state.directorySlot.description
  directoryImage : stop.files.directory = current.state.files.image.directory
  seals : stop.files.kept = current.state.files.image.kept
  pair : stop.files.directory.active = current.state.writer.target.pair
  crashPairs : stop.files.directory.crashImages = [current.state.writer.target.pair]
  marker : stop.files.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64)
  selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
    stop.files.directory.active.manifest current.state.writer.checkpoint
  visibleKeeper : stop.files.keeper.active = some (current.state.writer.wal.active.bytes ++ stop.cut.visibleTail)
  interruptedPayload : ∃ suffix, stop.cut.visibleTail ++ suffix = WAL.encodeBatch prepared.batch
  keeperPrefix : ∀ choice ∈ stop.files.keeper.active :: stop.files.keeper.crashImages, ∃ bytes,
    choice = some bytes ∧
    (stop.files.directory.active.walBoundary.mapM fun marker => do
      let count ← WAL.Boundary.decode marker
      selectRetained current.state.writer.installed.activeFirst count bytes) =
      .ok (some current.state.writer.wal.active.bytes)
  replay : PendingClientReplay (log ++ [.uncertainBatch prepared.batch]) current.reads history
  bounded : ∀ read ∈ current.reads, read.BoundedBy history.length

theorem NativeReadPosition.stopsAtFirstAppend (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} (stop : NativeFirstAppendStop prepared) :
    NativePendingFirstAppend current stop := by
  obtain ⟨valid, exactHistory, prior⟩ := current.readPrefix.refines
  have ordered : WAL.OrdinalsFrom 1 history := exactHistory ▸ valid.retained.resumed.ordered
  obtain ⟨replay, bounded⟩ := prior.appendUncertain (batch := prepared.batch) current.readPrefix.readsBounded (.inl rfl) ordered
  obtain ⟨_, inodes, issued, captured, keeper⟩ := stop.selects.custody
  have reachedInodes : stop.cutFiles.1.inode = current.state.census.inode := inodes
  obtain ⟨root, lock, keeperBound, markerBound⟩ := stop.heldBindings stop.cutFiles (by simp [NativeFirstAppendStop.cutFiles])
  obtain ⟨directory, seals, pair, pairs, marker, checkpoint, fresh⟩ := stop.selectsPrior valid
  refine ⟨stop.stopsWrite valid, valid.retained.held, rfl, rfl, reachedInodes, issued, stop.keeperRetained,
    stop.ownerRetained, stop.directoryRetained, captured, keeperBound.trans (congrArg some keeper),
    lock.trans (congrArg some (stop.lockIdentity.trans (congrFun reachedInodes _).symm)),
    root.trans (congrArg some (stop.directoryIdentity.trans (congrFun reachedInodes _).symm)),
    markerBound, ?_, directory, seals, pair, pairs, ?_, checkpoint, ?_, stop.visiblePrefix, fresh, replay, bounded⟩
  · obtain ⟨captured, cached, identity⟩ := stop.cachedDirectory
    exact ⟨captured, cached, identity.trans (stop.directoryIdentity.trans (congrFun reachedInodes _).symm)⟩
  · simpa only [exactHistory] using marker
  · change some (WAL.encode (current.state.writer.history.drop current.state.writer.wal.active.first) ++ stop.cut.visibleTail) = _
    rw [← valid.retained.layout.activeBytes]

end Alvoki.Storage.DiskSession
