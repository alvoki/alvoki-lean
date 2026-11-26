import Alvoki.Storage.Disk.NativeCheckpointFinalManifest
import Alvoki.Storage.Disk.NativeCheckpointSourceReopen
import Alvoki.Storage.Disk.NativeDurableWriteReboot
import Alvoki.Storage.Disk.NativeOpenSnapshotTrace
import Alvoki.Storage.Disk.NativeAlignedMarkedReady
import Alvoki.Storage.Disk.NativePublishedWriteSnapshot

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair SyncHandleRouting
open WAL.Boundary (CheckpointRepresentsPrefix WalInodeImage)
open Sequential (SnapshotTable)

variable {heap stream : Type} {opened : NativeOpenedHandle heap} {current : NativeOpenedPosition opened}
  {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap} {fsync : CheckpointFsync heap}
  {reason : FilePath} {reached : CheckpointWorld heap}

local notation "dbDir" => current.current.ready.state.session.directory
local notation "ready" => current.current.ready

variable {view : OpenCloseHeapView heap FileImage}
  {rebooted entry : heap} {input : FilePath} {source : RawMarkedOpenInterpreter heap stream}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {write : FilePath → ByteArray → EStateM IO.Error heap Unit}
  {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
  {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
  {ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool}

/-- The reopened writer's footprint uses the selected manifest, the same
WAL files, and the same canonical directory as the checkpoint reset. -/
theorem NativeReadyState.crashPath_forSelectedCheckpoint
    (state : NativeReadyState) (directory : DiskDirectory) (previous : SegmentedWriterState)
    (manifest : Option ByteArray)
    (sameDirectory : state.session.directory = directory)
    (sameKeeper : state.writer.wal.active.first = previous.wal.active.first)
    (sameSeals : state.writer.wal.sealed = previous.wal.sealed)
    (sameManifest : state.writer.target.pair.manifest = manifest) :
    state.crashPath = (fun path => path = directory.path ∨ path = directory.file .lock ∨
      checkpointSurvivorPath directory previous manifest path) := by
  funext path
  simp only [NativeReadyState.crashPath, checkpointSurvivorPath, checkpointWalPath,
    sameDirectory, sameKeeper, sameSeals, sameManifest]

/-- A reboot restores a sampled final checkpoint image. Scoped effects
carry it across the actual failed calls to the healthy aligned opener,
which reads the same files and returns the exact replayed table. With
the durable effects, the same handle can publish a batch and read it. -/
theorem NativeCheckpointSourceStop.reopensSampledFinalCheckpoint
    (stop : NativeCheckpointSourceStop current primitives fsync (.manifest .syncDirectory) reason reached)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView dbDir (inodes atHeap) (runs atHeap))
    (storage : FinalCheckpointStorageEffects stop inodes runs observe)
    (names : FilePath → Option Nat) (chosen : names ∈ (observe reached.2).crashBindings)
    (contents : Nat → ByteArray)
    (sampled : ∀ path, path = (dbDir).file .manifest ∨ storage.scope path →
      ∀ inode, names path = some inode → contents inode ∈ (inodes reached.2).crashBytes inode)
    (resetCensus : (view.descriptors rebooted).slots = [])
    (resetLock : (view.files rebooted).owners ((dbDir).file .lock) = none)
    {errors : List (FilePath × IO.Error)} (attempts : source.FailedCalls rebooted errors entry)
    (effects : OpenPhaseCellEffects view.phase get set) :
    let dir := dbDir
    let state := (ready).state
    let pair : DirectoryPublication.Bindings :=
      ⟨(names (dir.file .manifest)).map contents, (names (dir.file .walBoundary)).map contents⟩
    let wal : WalSegmentImage := { state.writer.wal with directory := .settled pair }
    let actual : RunFiles := fun generation index => (names (dir.file (.run generation index))).map contents
    let retry : LockedFileState FileImage :=
      ⟨wal.checkpointReopenFiles wal.directory none, state.files.owners.set (dir.file .lock) none⟩
    let vacant : TryLockObserves retry.owners dir (.ok true) := fun _ => by simp [retry, LockOwners.set]
    let selectedPath : FilePath → Prop := fun path =>
      path = dir.path ∨ path = dir.file .lock ∨ checkpointSurvivorPath dir state.writer pair.manifest path
    let physical : heap → CheckpointStorageObservation := fun heap => (observe heap).storageObservation
    let filesAt : heap → CheckpointSurvivingFiles := fun heap =>
      ⟨(physical heap).files.names, fun inode => [(inodes heap).visible inode]⟩
    let checkpointFiles : CheckpointSurvivingFiles := ⟨names, fun inode => [contents inode]⟩
    (checkpointFiles.Frames selectedPath (filesAt rebooted)) →
    (∀ {prior : List (FilePath × IO.Error)} {before after : heap} {path : FilePath} {cause : IO.Error},
      source.FailedCalls rebooted prior before → List.IsPrefix (prior ++ [(path, cause)]) errors →
      source.openTable path before = .error cause after →
      (filesAt before).Frames selectedPath (filesAt after) ∧ (view.files after).image = (view.files before).image) →
    (∀ (published : Image) (layout : CanonicalKeeperLayout retry.image state.writer.history),
      Prepared retry.image layout.target layout.plan →
      ∀ {checkpoint}, ∀ selected : SelectedIntegrityCheckpoint ({ published with durable := actual } : Image).durable
          retry.image.directory.active.manifest checkpoint,
      ∃ (opening : CheckpointBarrierAlignedReports input dir (view.descriptors entry) retry layout
          { published with durable := actual } vacant selected names)
        (chronology : CapturedMarkedReadCensus opening.reads opening.finish.readCustody)
        (raw : RawAlignedCheckpointReopenEffects opening chronology view source.calls source.init entry
          phaseIdentity tokenIdentity source.allocatePhase source.allocateToken stream),
        raw.fileCalls = source.fileCalls ∧ raw.directoryCalls = source.directoryCalls ∧
        raw.callbacks = source.keeperCallbacks ∧
        ∀ path, path = dir.path ∨ path = dir.file .lock → opening.reads.bindings path = (physical entry).files.names path) →
    ∃ (published : Image) (layout : CanonicalKeeperLayout retry.image state.writer.history)
      (checkpoint : Option (PackedTable × UInt64))
      (selected : SelectedIntegrityCheckpoint ({ published with durable := actual } : Image).durable
        retry.image.directory.active.manifest checkpoint)
      (opening : CheckpointBarrierAlignedReports input dir (view.descriptors entry) retry layout
        { published with durable := actual } vacant selected names)
      (chronology : CapturedMarkedReadCensus opening.reads opening.finish.readCustody)
      (raw : RawAlignedCheckpointReopenEffects opening chronology view source.calls source.init entry
        phaseIdentity tokenIdentity source.allocatePhase source.allocateToken stream)
      (next : NativeReadPosition current.current.history current.current.submissions)
      (returned : raw.ReturnedAt next source.remove write source.rename source.bootstrap
        RawMarkedOpenInterpreter.assemble get set ptrEq),
      (view.descriptors rebooted).slots = [] ∧
      (view.files rebooted).owners (dir.file .lock) = none ∧
      (view.files rebooted).image = retry.image ∧
      checkpointFiles.Frames selectedPath (filesAt entry) ∧
      view.files entry = retry ∧
      source.openTable input entry = .ok returned.handle.table returned.start.reached ∧
      (view.handle raw.seed.afterPending raw.seed.handle).1.inode
        (view.handle raw.seed.afterPending raw.seed.handle).2.1.description =
        state.census.inode state.directorySlot.description ∧
      (view.handle raw.raw.afterFlock raw.raw.lock).1.inode
        (view.handle raw.raw.afterFlock raw.raw.lock).2.1.description = state.census.inode state.owner.description ∧
      (pair.manifest = none → names (dir.file .manifest) = none ∧
        ∃ filename message, opening.reads.reads.stat (dir.file .manifest) =
          .error (.noFileOrDirectory filename 2 message)) ∧
      (∀ bytes, pair.manifest = some bytes → opening.ReadsSample contents (dir.file .manifest) bytes) ∧
      opening.ReadsSample contents (dir.file .walBoundary)
        (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64) ∧
      (∀ bytes metadata, pair.manifest = some bytes → Manifest.IntegrityCheckpoint.decode bytes = .ok metadata →
        ∀ index < metadata.header.runCount.toNat, ∀ payload, actual metadata.header.generation index = some payload →
        opening.ReadsSample contents (dir.file (.run metadata.header.generation index)) payload) ∧
      (∀ segment ∈ layout.sealed ++ [layout.keeper],
        opening.ReadsSample contents (dir.file (.walSegment segment.first)) segment.bytes) ∧
      returned.start.current.ready.state.writer.checkpoint = checkpoint ∧
      returned.start.current.ready.reads = (ready).reads ∧
      current.current.LedgerSuffix [] returned.start.current ∧
      RebootDirectoryBindings next.state names ∧
      next.state.writer.target = layout.target ∧ next.state.writer.published.durable = actual ∧
      next.state.writer.wal = { wal with directory := next.state.files.image.directory } ∧
      (∀ segment ∈ wal.segments, checkpointFiles.Stored (dir.file (.walSegment segment.first)) segment.bytes) ∧
      (checkpointFiles.Frames selectedPath (physical rebooted).files →
        (∀ names ∈ (physical rebooted).crashNames, names dir.path = checkpointFiles.names dir.path) →
        (∀ {prior : List (FilePath × IO.Error)} {before after : heap} {path : FilePath} {cause : IO.Error},
          source.FailedCalls rebooted prior before → List.IsPrefix (prior ++ [(path, cause)]) errors →
          source.openTable path before = .error cause after →
          (physical before).files.Frames selectedPath (physical after).files ∧
          (physical before).Frames (· = dir.path) (physical after)) →
        AlignedCheckpointWriteEffects raw next.state physical (fun heap => (inodes heap).visible) →
        ∃ cache : OpenSyncCacheRefs returned.handle.files returned.start.current.ready.state.session.directory.path,
          cache.directory = raw.seed.directoryRef ∧ cache.active = raw.seed.activeRef ∧ cache.pending = raw.seed.pendingRef ∧
          returned.start.WriteStorageEntry view cache (physical returned.start.reached) (inodes returned.start.reached).visible ∧
          (∀ {α : Type} (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
            (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
            (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
            (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
            {sequence : UInt64} {writeReached : heap}, request.rows ≠ [] →
            returned.start.ObservesPublishedWrite appender stager syncer view cache inodes runs physical
              inode buffered request lookup rename sequence writeReached →
            ∀ (read : SnapshotReadRequest α), returned.handle.ObservesSnapshotToken writeReached →
            let directory := returned.start.current.ready.state.session.directory
            request.runOnRawOpenPhase directory lookup (appender.run cache.active) (stager.run cache.pending)
              (syncer.group directory.path cache.directory cache.active cache.pending) rename
              returned.handle.phase returned.handle.get returned.handle.set returned.start.reached = .ok sequence writeReached ∧
            ∃ (batch : List WAL.Write) (table : PackedTable) (written last : NativeOpenedPosition returned.handle)
              (reference : SnapshotTable UInt64) (events : List NativeExecutionEvent),
              prepareBatch returned.start.current.ready.state.writer.installed.table request.rows = some (batch, table) ∧
              sequence = table.committed ∧ written.reached = writeReached ∧
              NativeOpenedTrace written [.acquire, .readAt written.pins.length read] events last ∧
              current.current.LedgerSuffix (.acknowledged request batch :: events) last.current ∧
              SnapshotWalReplay .empty (current.current.history ++ batch) reference ∧
              ∀ observation ∈ last.current.ready.reads, observation.agrees reference)) ∧
      recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode current.current.history) =
        .ok returned.start.current.ready.state.writer.installed.table ∧
      InstalledClientReplay current.current.submissions (ready).reads current.current.history
        returned.start.current.ready.state.writer.installed returned.start.current.ready.state.session ∧
      (∀ {α : Type} (request : SnapshotReadRequest α),
        (∀ {event after}, (NativeOpenedReport.acquire (start := returned.start)).Reached event after →
          ptrEq returned.handle.token returned.handle.token after.reached = .ok true after.reached) →
        ∃ (last : NativeOpenedPosition returned.handle) (events : List NativeExecutionEvent)
          (reference : SnapshotTable UInt64),
          NativeOpenedTrace returned.start [.acquire, .readAt returned.start.pins.length request] events last ∧
          current.current.LedgerSuffix events last.current ∧
          SnapshotWalReplay .empty current.current.history reference ∧
          last.current.ready.reads = (ready).reads ++
            [request.record returned.start.current.ready.state.writer.installed.table.committed
              (request.replay reference returned.start.current.ready.state.writer.installed.table.committed)] ∧
          ∀ read ∈ last.current.ready.reads, read.agrees reference) := by
  intro dir state pair wal actual retry vacant selectedPath physical filesAt checkpointFiles reset each observeReads
  obtain ⟨sameFilesAt, sameImage⟩ := attempts.framesAfter .empty
    (fun before after => (filesAt before).Frames selectedPath (filesAt after) ∧
      (view.files after).image = (view.files before).image)
    (fun _ => ⟨fun _ _ => ⟨rfl, fun _ _ => rfl⟩, rfl⟩)
    (fun earlier later => ⟨earlier.1.trans later.1, later.2.trans earlier.2⟩)
    (fun prior inside returned => each prior (by simpa only [List.nil_append] using inside) returned)
  have survivor := reset.trans sameFilesAt
  have entryKeeps : ∀ path, path = dir.path ∨ path = dir.file .lock → (physical entry).files.names path = names path := by
    intro path authority
    exact (survivor path (authority.imp_right Or.inl)).1
  obtain ⟨authority, marker, segments, published, layout, _, walLayout, walValid, keeper, aligned,
    descriptors, offsets, prepared, _, accepted, _, _, _, checkpoint, _, _, selected, _, _, _, _, _⟩ :=
    stop.replaysSampledFinalCheckpoint inodes runs observe storage names chosen contents sampled
  obtain ⟨opening, chronology, raw, sameFiles, sameDirectory, sameKeeper, readsAtEntry⟩ :=
    observeReads published layout prepared selected
  have captures := raw.capturesRebootAuthority rfl (fun atHeap => (physical atHeap).files.names) names authority entryKeeps readsAtEntry
  have markerSelected : retry.image.directory.active.walBoundary =
      some (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64) := by
    obtain ⟨inode, bound, payload⟩ := marker
    change names (dir.file .walBoundary) = some inode at bound
    change [contents inode] = _ at payload
    change (names (dir.file .walBoundary)).map contents = _
    rw [bound, Option.map_some, (List.cons.inj payload).1]
  have readSegments : ∀ segment ∈ layout.sealed ++ [layout.keeper],
      (names (dir.file (.walSegment segment.first))).map contents = some segment.bytes := by
    intro segment included
    have member : segment ∈ state.writer.wal.segments := by
      rw [descriptors, WalSegmentImage.readDescriptors] at included
      split at included
      · exact (List.mem_filter.mp included).1
      · exact List.mem_append_right _ included
    obtain ⟨inode, bound, payload⟩ := segments segment member
    change names (dir.file (.walSegment segment.first)) = some inode at bound
    change [contents inode] = _ at payload
    rw [bound, Option.map_some, (List.cons.inj payload).1]
  obtain ⟨missing, manifestRead, markerRead, runRead, walReads⟩ :=
    opening.readsSelectedSamples contents rfl rfl markerSelected (fun _ _ _ _ _ _ _ stored => stored) aligned readSegments
  have following := opening.reads.walReads.selectedAfterWatermark offsets descriptors
  obtain ⟨prior, history, pending⟩ := (ready).readPrefix.refines
  have first : layout.target.first = wal.active.first := congrArg WalSegment.first keeper
  obtain ⟨next, returned, opened, selectedAgain, priorReads, sameTarget, sameRuns, sameWal, replay, ledger⟩ :=
    raw.returnsSelectedFromFixedInterpreter sameFiles sameDirectory sameKeeper prepared following accepted
      prior.retained.resumed.ordered walLayout walValid prior.retained.spans rfl first rfl
      history pending (ready).readPrefix.readsBounded write effects ptrEq
  have unchanged : current.current.LedgerSuffix [] returned.start.current :=
    ⟨by rw [returned.position]; simp, by rw [returned.position]; simp, by simpa using priorReads, by simp⟩
  have newState := congrArg (fun position : NativeExecutionPosition => position.ready.state) returned.position
  rw [newState] at sameTarget sameRuns sameWal
  have readNames (path : FilePath) (inside : path = dir.path ∨ path = dir.file .lock) :
      opening.reads.bindings path = names path :=
    (readsAtEntry path inside).trans (entryKeeps path inside)
  have newAuthority : RebootDirectoryBindings next.state names := by
    constructor
    · rw [returned.resolvedDirectory, returned.repairCensus, returned.directorySlot, opening.finish.sameCensusObjects]
      exact (readNames _ (.inl rfl)).symm.trans opening.reads.sameObjects.1
    · rw [returned.resolvedDirectory, returned.repairCensus, returned.lockOwner, opening.finish.sameCensusObjects]
      exact (readNames _ (.inr rfl)).symm.trans opening.reads.sameObjects.2.1
  have sameScope : next.state.crashPath = selectedPath := by
    apply NativeReadyState.crashPath_forSelectedCheckpoint _ dir state.writer pair.manifest returned.resolvedDirectory
    · rw [sameWal]
    · rw [sameWal]
    · exact congrArg (fun target : Target => target.pair.manifest) sameTarget
  refine ⟨published, layout, checkpoint, selected, opening, chronology, raw, next, returned,
    resetCensus, resetLock, sameImage.symm.trans (congrArg LockedFileState.image raw.raw.entryFiles), survivor,
    raw.raw.entryFiles, opened, captures.1, captures.2, missing, manifestRead, markerRead, runRead, walReads,
    selectedAgain, priorReads, unchanged, newAuthority, sameTarget, sameRuns, sameWal, segments, ?_, replay, ledger, ?_⟩
  · intro restored parent afterCall laws
    obtain ⟨files, root⟩ := attempts.carriesCheckpointReset physical selectedPath dir.path checkpointFiles
      (.inl rfl) restored parent afterCall
    have writerHistory := next.readPrefix.refines.2.1.trans history.symm
    have firstAtReturn : next.state.writer.wal.active.first = layout.keeper.first :=
      (congrArg (fun image : WalSegmentImage => image.active.first) sameWal).trans (congrArg WalSegment.first keeper.symm)
    have bytesAtReturn : next.state.writer.wal.active.bytes = layout.keeper.bytes :=
      (congrArg (fun image : WalSegmentImage => image.active.bytes) sameWal).trans (congrArg WalSegment.bytes keeper.symm)
    have manifest : (names (next.state.session.directory.file .manifest)).map contents = next.state.writer.target.pair.manifest := by
      rw [returned.resolvedDirectory, sameTarget]
      rfl
    have seals (segment : WalSegment) (present : segment ∈ next.state.writer.wal.sealed) :
        (names (next.state.session.directory.file (.walSegment segment.first))).map contents = some segment.bytes := by
      rw [sameWal] at present
      obtain ⟨inode, bound, stored⟩ := segments segment (List.mem_append_left _ present)
      change names (dir.file (.walSegment segment.first)) = some inode at bound
      change [contents inode] = [segment.bytes] at stored
      rw [returned.resolvedDirectory, bound, Option.map_some, (List.cons.inj stored).1]
    have runMap (generation : UInt64) (index : Nat) : next.state.writer.published.durable generation index =
        (names (next.state.session.directory.file (.run generation index))).map contents := by
      rw [sameRuns, returned.resolvedDirectory]
    have markerAtSample : (names (next.state.session.directory.file .walBoundary)).map contents =
        some (WAL.Boundary.encode (WAL.encode next.state.writer.history).size.toUInt64) := by
      rw [returned.resolvedDirectory, writerHistory]
      exact markerSelected
    let keeperPath := dir.file (.walSegment layout.keeper.first)
    let held := opening.reads.wal.keeper
    have object := opening.keeperChild.sameObject held.calls held.bound held.contents
    obtain ⟨inode, bound, bytes⟩ := segments layout.keeper (by rw [keeper]; exact List.mem_append_right _ (by simp))
    change names keeperPath = some inode at bound
    change [contents inode] = [layout.keeper.bytes] at bytes
    have sameInode := Option.some.inj (object.symm.trans bound)
    subst inode
    have keeperLive : (physical entry).files.names keeperPath = some held.observesFile.object ∧
        (inodes entry).visible held.observesFile.object = layout.keeper.bytes ++ layout.tail := by
      have onKeeper : keeperPath = dir.file (.walSegment state.writer.wal.active.first) := by
        dsimp only [keeperPath]
        rw [keeper]
      have inside : selectedPath keeperPath := .inr (.inr (.inr (.inl (.inr (.inl onKeeper)))))
      obtain ⟨binding, value⟩ := survivor keeperPath inside
      have payload := value held.observesFile.object object
      change [(inodes entry).visible held.observesFile.object] = [contents held.observesFile.object] at payload
      exact ⟨binding.trans object, (List.cons.inj payload).1.trans
        ((List.cons.inj bytes).1.trans opening.finish.keeperPayload.symm)⟩
    obtain ⟨cache, dirRef, activeRef, pendingRef, readyWrite⟩ :=
      returned.writeStorageFromCheckpointSample physical (fun heap => (inodes heap).visible)
        contents firstAtReturn bytesAtReturn newAuthority manifest seals runMap (sameScope.symm ▸ files)
        markerAtSample (returned.resolvedDirectory.symm ▸ root) keeperLive laws
    refine ⟨cache, dirRef, activeRef, pendingRef, readyWrite, ?_⟩
    intro α appender stager syncer inode buffered request lookup rename sequence writeReached nonempty observed read token
    obtain ⟨_, wrote, batch, table, written, last, reference, events, prepared, committed, atWrite, trace, suffix,
      replay, reads⟩ := returned.start.acknowledgesAndReadsLatest appender stager syncer view cache inodes runs
        physical inode buffered request lookup rename nonempty readyWrite observed read token
    have sameHistory : returned.start.current.history = current.current.history := by rw [returned.position]
    exact ⟨wrote, batch, table, written, last, reference, events, prepared, committed, atWrite, trace,
      by simpa only [List.nil_append] using unchanged.append suffix, sameHistory ▸ replay, reads⟩
  · intro α request compareAtAcquire
    obtain ⟨_, _, last, reference, _, _, _, _, calls, reads, snapshotReplay, agrees⟩ :=
      returned.start.acquiresAndReadsLatest request (fun reached => by
        rw [returned.comparesTokens]
        exact compareAtAcquire reached)
    have sameHistory : returned.start.current.history = current.current.history := by rw [returned.position]
    refine ⟨last, _, reference, calls, ?_, sameHistory ▸ snapshotReplay, ?_, agrees⟩
    · simpa only [List.nil_append] using unchanged.append calls.common.ledgerSuffix
    · rwa [priorReads] at reads

end Alvoki.Storage.DiskSession
