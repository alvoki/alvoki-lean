import Alvoki.Storage.Disk.NativeFreshOpenedSessions
import Alvoki.Storage.Disk.NativeCheckpointSourceReopen
import Alvoki.Storage.Disk.NativeOpenSnapshotTrace

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair SyncHandleRouting
open Sequential (SnapshotTable)
open WAL.Boundary (WalInodeImage)

/-- The two source cuts in this pilot, before a manifest has been staged. -/
inductive FreshCheckpointCut where
  | firstRun
  | runsDirectory

def FreshCheckpointCut.step : FreshCheckpointCut → CheckpointPublication.Step
  | .firstRun => .syncRun 0
  | .runsDirectory => .syncRunsDirectory

section EarlyCut

variable {heap : Type} {opened : NativeOpenedHandle heap} {current : NativeOpenedPosition opened}
  {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap} {fsync : CheckpointFsync heap}
  {reason : FilePath} {reached : CheckpointWorld heap}
  {view : OpenCloseHeapView heap FileImage}

/-- The run write, cache and fsync observations at the first run stop. -/
structure FirstRunStopObservations
    (stop : NativeCheckpointSourceStop current primitives fsync (.syncRun 0) reason reached)
    (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView current.current.ready.state.session.directory
      (inodes atHeap) (runs atHeap)) where
  calls : CheckpointRawSyncCalls heap
  projected : view.cacheAt stop.atIssue.2 cache.directory cache.active cache.pending = stop.atIssue.1
  atFsync : heap
  pending : CheckpointPendingSyncAt calls view cache.pending fsync
    (current.current.ready.state.session.directory.file (.run stop.next.generation 0)) stop.atIssue.2 atFsync
  consume : (observe stop.atIssue.2).storageObservation.Frames current.current.ready.state.crashPath
    (observe atFsync).storageObservation
  effective : Bool
  effect : ∀ literal, calls.fsync literal atFsync = .error reason reached.2 →
    let inode := (view.descriptors atFsync).inode (view.handle atFsync literal).2.1.description
    let path := current.current.ready.state.session.directory.file (.run stop.next.generation 0)
    (observe atFsync).visible path = some inode ∧
    (∀ other, (observe atFsync).visible other = some inode → other = path) ∧
    inodes reached.2 = (if effective then (inodes atFsync).completeFileSync inode else inodes atFsync) ∧
    (observe reached.2).visible = (observe atFsync).visible ∧
    (observe reached.2).crashBindings = (observe atFsync).crashBindings
  writeEffect : ∀ payload handle,
    let path := current.current.ready.state.session.directory.file (.run stop.next.generation 0)
    primitives.cached.writeRun path payload stop.poisoned = .ok handle stop.atIssue.2 →
    ∃ inode, RunWriteInodeFrame path inode (inodes stop.atIssue.2) (observe stop.poisoned) (observe stop.atIssue.2) ∧
      ∀ other, (observe stop.poisoned).visible other = some inode → other = path

theorem FirstRunStopObservations.storageAtStop
    {stop : NativeCheckpointSourceStop current primitives fsync (.syncRun 0) reason reached}
    {cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path}
    {inodes : heap → WalInodeImage} {runs : heap → RunUnlinkImage}
    {observe : ∀ atHeap, RunDirectoryInodeView current.current.ready.state.session.directory
      (inodes atHeap) (runs atHeap)}
    (seen : FirstRunStopObservations (view := view) stop cache inodes runs observe)
    (initial : NativeReadyStorage current.current.ready.state (observe stop.poisoned).storageObservation) :
    NativeReadyStorage current.current.ready.state (observe reached.2).storageObservation :=
  initial.frame ((stop.firstRunWriteFrames inodes runs observe seen.writeEffect).trans
    (stop.runSyncFrames seen.calls cache seen.projected seen.pending inodes runs observe
      seen.consume seen.effective seen.effect))

/-- The returned run prefix and the first directory barrier have separate
physical obligations on the same reached execution. -/
structure RunsDirectoryCutObservations
    (stop : NativeCheckpointSourceStop current primitives fsync .syncRunsDirectory reason reached)
    (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView current.current.ready.state.session.directory
      (inodes atHeap) (runs atHeap)) where
  returnedRuns : ReturnedCheckpointRunEffects stop stop.next.table.runs.length inodes runs observe
  atSync : RunsDirectoryStopObservations (view := view) stop cache inodes runs observe

def FreshCheckpointCut.Physical (cut : FreshCheckpointCut)
    (view : OpenCloseHeapView heap FileImage)
    (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView current.current.ready.state.session.directory
      (inodes atHeap) (runs atHeap)) :
    NativeCheckpointSourceStop current primitives fsync cut.step reason reached → Type :=
  match cut with
  | .firstRun => fun stop => FirstRunStopObservations (view := view) stop cache inodes runs observe
  | .runsDirectory => fun stop => RunsDirectoryCutObservations (view := view) stop cache inodes runs observe

/-- The common phase observations and the local effects for one source cut. -/
structure FreshCheckpointStopObservations
    (cut : FreshCheckpointCut)
    (stop : NativeCheckpointSourceStop current primitives fsync cut.step reason reached)
    (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView current.current.ready.state.session.directory
      (inodes atHeap) (runs atHeap)) where
  physical : cut.Physical view cache inodes runs observe stop
  phaseStorage : (observe current.reached).storageObservation.Frames current.current.ready.state.crashPath
    (observe stop.poisoned).storageObservation
  returnedKeeps : ∀ step ∈ stop.completed, ∀ before after,
    (primitives.checkpointStepUntilStop current.current.ready.state.session.directory
      fsync stop.next stop.manifest step).run before = .ok (.ok ()) after →
    opened.contents after.2 opened.phase = opened.contents before.2 opened.phase
  stoppedKeeps : opened.contents reached.2 opened.phase = opened.contents stop.atIssue.2 opened.phase

theorem FreshCheckpointStopObservations.storageAtStop
    {cut : FreshCheckpointCut}
    {stop : NativeCheckpointSourceStop current primitives fsync cut.step reason reached}
    {cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path}
    {inodes : heap → WalInodeImage} {runs : heap → RunUnlinkImage}
    {observe : ∀ atHeap, RunDirectoryInodeView current.current.ready.state.session.directory
      (inodes atHeap) (runs atHeap)}
    (seen : FreshCheckpointStopObservations (view := view) cut stop cache inodes runs observe)
    (initial : NativeReadyStorage current.current.ready.state (observe current.reached).storageObservation) :
    NativeReadyStorage current.current.ready.state (observe reached.2).storageObservation := by
  have atPoison := initial.frame seen.phaseStorage
  cases cut with
  | firstRun => exact FirstRunStopObservations.storageAtStop seen.physical atPoison
  | runsDirectory =>
    have effects : RunsDirectoryCutObservations (view := view) stop cache inodes runs observe := seen.physical
    have runsFrame := stop.returnedRunFrames stop.runsDirectoryIssue.1 inodes runs observe effects.returnedRuns
    exact stop.runsDirectoryPreservesSelected cache inodes runs observe (atPoison.frame runsFrame) effects.atSync

end EarlyCut

section QuietRetry

variable {heap stream : Type} {opened : NativeOpenedHandle heap} {current : NativeOpenedPosition opened}
  {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap} {fsync : CheckpointFsync heap}
  {stage : CheckpointPublication.Step} {reason : FilePath} {reached : CheckpointWorld heap}
  {view : OpenCloseHeapView heap FileImage} {storage : heap → CheckpointStorageObservation}
  {bytes : heap → Nat → ByteArray} {rebooted : heap}

local notation "ready" => current.current.ready
local notation "state" => current.current.ready.state
local notation "dir" => current.current.ready.state.session.directory
local notation "footprint" => checkpointSurvivorPath dir current.current.ready.state.writer
  current.current.ready.state.writer.target.pair.manifest
local notation "liveNames" => fun atHeap => CheckpointSurvivingFiles.names (CheckpointStorageObservation.files (storage atHeap))
local notation "readFiles" => fun atHeap => CheckpointSurvivingFiles.mk (liveNames atHeap) (fun inode => [bytes atHeap inode])

/-- Reboot and two independent open attempts observed after a checkpoint
cut. The reached storage proof indexes the chosen reboot projection. -/
structure QuietCheckpointRetryObservations
    (stable : NativeReadyStorage current.current.ready.state (storage reached.2))
    (source : RawMarkedOpenInterpreter heap stream) (input retryInput : FilePath)
    (diagnostic : IO.Error) (afterFailure : heap) where
  names : FilePath → Option Nat
  chosen : names ∈ (storage reached.2).crashNames
  contents : Nat → ByteArray
  durable : ∀ path, footprint path → ∀ inode, names path = some inode →
    contents inode ∈ (storage reached.2).files.bytes inode
  rebootObjects : Nat → Nat
  survivorNames : ∀ path, (state).crashPath path → liveNames rebooted path = names path
  survivorBytes : ∀ path, footprint path →
    ∀ inode, names path = some inode → bytes rebooted inode = contents inode
  booted : let crash := stable.observeCrash names chosen contents durable rebootObjects
    (view.descriptors rebooted, view.files rebooted) = (crash.reboot, crash.retry)
  admission : CensusOpenAdmissionReports input dir (view.descriptors rebooted) (view.files rebooted)
  admitted : RawOpenAdmissionReport admission view source.calls rebooted
  seed : OpenSyncCacheAllocations admission.opened view source.init admitted.afterFlock
  seen : RawManifestStatError (admitted := admitted) seed source.fileCalls
  disposal : RawOpenCacheDisposal (admitted := admitted) seed seen.reached
  disposes : source.dispose = disposal.dispose
  finalized : RawOpenErrorLockFinalization view dir source.release admitted.lock admission.owner disposal.reached
  frames : seen.FileFrames disposal finalized readFiles footprint
  failedWith : disposal.diagnostic seen.cause = diagnostic
  cleanup : finalized.reached = afterFailure
  phaseIdentity : IO.Ref (Phase Installed) → Nat
  tokenIdentity : IO.Ref Unit → Nat
  observe : let crash := stable.observeCrash names chosen contents durable rebootObjects
    ∀ layout : CanonicalKeeperLayout crash.retry.image (state).writer.history,
      layout.target = (state).writer.target → Prepared crash.retry.image layout.target layout.plan →
      ∀ selected : SelectedIntegrityCheckpoint (state).writer.published.durable
        crash.retry.image.directory.active.manifest (state).writer.checkpoint,
        ∃ (reader : NativeReadyRestartReads crash retryInput layout selected)
          (raw : RawAlignedCheckpointReopenEffects reader.opening reader.capturedChronology view source.calls source.init
            finalized.reached phaseIdentity tokenIdentity source.allocatePhase source.allocateToken stream),
          raw.fileCalls = source.fileCalls ∧ raw.directoryCalls = source.directoryCalls ∧
            raw.callbacks = source.keeperCallbacks
  write : FilePath → ByteArray → EStateM IO.Error heap Unit
  get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)
  set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit
  effects : OpenPhaseCellEffects view.phase get set


theorem QuietCheckpointRetryObservations.readsLatest
    (stop : NativeCheckpointSourceStop current primitives fsync stage reason reached)
    {stable : NativeReadyStorage current.current.ready.state (storage reached.2)}
    {source : RawMarkedOpenInterpreter heap stream} {input retryInput : FilePath}
    {diagnostic : IO.Error} {afterFailure : heap}
    {ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool}
    (retry : QuietCheckpointRetryObservations (view := view) (bytes := bytes) (rebooted := rebooted)
      stable source input retryInput diagnostic afterFailure)
    (request : SnapshotReadRequest α)
    (compareToken : ∀ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      handle.ptrEq = ptrEq →
      source.openTable retryInput afterFailure = .ok handle.table start.reached →
      ∀ {event after}, (NativeOpenedReport.acquire (start := start)).Reached event after →
        ptrEq handle.token handle.token after.reached = .ok true after.reached) :
    RawQuietRebootEntry (stable.observeCrash retry.names retry.chosen retry.contents retry.durable retry.rebootObjects)
      view liveNames bytes reached.2 rebooted (view.descriptors reached.2) ∧
    source.openTable input rebooted = .error diagnostic afterFailure ∧
    ∃ (handle : NativeOpenedHandle heap) (start last : NativeOpenedPosition handle)
      (events : List NativeExecutionEvent) (reference : SnapshotTable UInt64),
      source.openTable retryInput afterFailure = .ok handle.table start.reached ∧
      NativeOpenedTrace start [.acquire, .readAt start.pins.length request] events last ∧
      current.current.LedgerSuffix events last.current ∧
      SnapshotWalReplay .empty current.current.history reference ∧
      last.current.ready.reads = (ready).reads ++ [request.record start.current.ready.state.writer.installed.table.committed
        (request.replay reference start.current.ready.state.writer.installed.table.committed)] ∧
      ∀ read ∈ last.current.ready.reads, read.agrees reference := by
  obtain ⟨boot, denied, _, _, _, _, _, _, next, sameReads, _, _, returned, reopened⟩ :=
    stop.reopensQuietAfterManifestRejection stable retry.names retry.chosen retry.contents retry.durable retry.rebootObjects
      retry.survivorNames retry.survivorBytes retry.booted source retry.seen retry.disposal retry.disposes retry.finalized
      retry.frames retry.observe retry.write retry.effects ptrEq
  rw [retry.failedWith, retry.cleanup] at denied
  have reopenedAt : source.openTable retryInput afterFailure = .ok returned.handle.table returned.start.reached :=
    (congrArg (source.openTable retryInput) retry.cleanup).symm.trans reopened
  obtain ⟨_, _, last, reference, _, _, _, _, calls, reads, replay, agrees⟩ :=
    returned.start.acquiresAndReadsLatest request (fun atAcquire => by
      rw [returned.comparesTokens]
      exact compareToken returned.handle returned.start returned.comparesTokens reopenedAt atAcquire)
  have history : returned.start.current.history = current.current.history := by rw [returned.position]
  have submissions : returned.start.current.submissions = current.current.submissions := by rw [returned.position]
  have earlierReads : returned.start.current.ready.reads = (ready).reads := by
    rw [returned.position]
    exact sameReads
  have recoveredLedger : current.current.LedgerSuffix [] returned.start.current :=
    ⟨by simpa using history, by simpa using submissions, by simpa using earlierReads, by simp⟩
  refine ⟨boot, denied, returned.handle, returned.start, last, _, reference, reopenedAt, calls, ?_, history ▸ replay, ?_, agrees⟩
  · simpa only [List.nil_append] using recoveredLedger.append calls.common.ledgerSuffix
  · rwa [earlierReads] at reads

end QuietRetry


private theorem storageObservation_cast {directory other : DiskDirectory}
    {inodes : WalInodeImage} {runs : RunUnlinkImage} (same : directory = other)
    (view : RunDirectoryInodeView directory inodes runs) :
    (same ▸ view : RunDirectoryInodeView other inodes runs).storageObservation = view.storageObservation := by
  subst other
  rfl

variable {heap : Type} {call : EStateM IO.Error heap DiskTable} {entry : heap}

/-- Follow the actual first acknowledgement through an early checkpoint
cut. The stopped ledger and the exact retry and snapshot use the storage
derived from that same source stop. -/
theorem FreshBootstrapOpenHeap.Returned.replaysAfterEarlyCheckpointStop
    (opened : FreshBootstrapOpenHeap.Returned call entry) {input : FilePath} {directory : DiskDirectory}
    {report : EmptyOpenSuccessReports input directory} {after : LockedFileState WalSegmentRotation.State}
    (used : (NativeOpenSuccessReports.empty report).UsesReachedState opened.start.current.ready.state after)
    (view : OpenCloseHeapView heap FileImage)
    {directoryRef : IO.Ref (Option IO.FS.Handle)}
    {activeRef : IO.Ref (Option (FilePath × IO.FS.Handle))}
    {pendingRef : IO.Ref (List (FilePath × IO.FS.Handle))}
    (resolved : opened.handle.directory = directory)
    (references : opened.handle.files.UsesCacheReferences activeRef pendingRef directoryRef)
    (atDirectory : opened.handle.files.AtDirectory directory.path)
    (census : view.descriptors opened.start.reached = opened.start.current.ready.state.census)
    (cacheAt : view.cacheAt opened.start.reached directoryRef activeRef pendingRef = opened.start.current.ready.state.cache)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (filesObserved : ∀ atHeap, RunDirectoryInodeView directory (inodes atHeap) (runs atHeap))
    (settled : let state := opened.start.current.ready.state
      NativeReadyStorage state (filesObserved opened.start.reached).storageObservation ∧
      ∀ inode, (filesObserved opened.start.reached).storageObservation.files.names (state.session.directory.file
        (.walSegment state.writer.wal.active.first)) = some inode →
        (inodes opened.start.reached).visible inode = state.writer.wal.active.bytes)
    (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) {sequence : UInt64} {reached : heap}
    (nonempty : request.rows ≠ [])
    (seen : ∀ (cache : OpenSyncCacheRefs opened.handle.files opened.start.current.ready.state.session.directory.path),
      cache.directory = directoryRef → cache.active = activeRef → cache.pending = pendingRef →
      opened.start.ObservesPublishedWrite appender stager syncer view cache inodes runs
        (fun atHeap => (filesObserved atHeap).storageObservation)
        inode buffered request lookup rename sequence reached)
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap)
    (fsync : CheckpointFsync heap) (cutStage : FreshCheckpointCut) {reason : FilePath} {stoppedAt : CheckpointWorld heap}
    (stopped : (runCheckpointOnOpenPhaseUntilSyncStop directory
      opened.handle.phase opened.handle.get opened.handle.set primitives fsync).run
      (view.cacheAt reached directoryRef activeRef pendingRef, reached) = .error (cutStage.step, reason) stoppedAt)
    (cutEffects : ∀ (next : NativeOpenedPosition opened.handle)
      (directoryAtNext : next.current.ready.state.session.directory = directory),
      next.reached = reached →
      ∀ (cache : OpenSyncCacheRefs opened.handle.files next.current.ready.state.session.directory.path),
        cache.directory = directoryRef → cache.active = activeRef → cache.pending = pendingRef →
        ∀ stop : NativeCheckpointSourceStop next primitives fsync cutStage.step reason stoppedAt,
          Nonempty (FreshCheckpointStopObservations (view := view) cutStage stop cache inodes runs
            (fun atHeap => directoryAtNext.symm ▸ filesObserved atHeap)))
    {stream : Type} (source : RawMarkedOpenInterpreter heap stream)
    {failedInput retryInput : FilePath} {rebooted afterFailure : heap} {diagnostic : IO.Error}
    (retryBytes : heap → Nat → ByteArray)
    (retryEffects : ∀ (next : NativeOpenedPosition opened.handle), next.reached = reached →
      ∀ stable : NativeReadyStorage next.current.ready.state (filesObserved stoppedAt.2).storageObservation,
        Nonempty (QuietCheckpointRetryObservations (current := next) (view := view) (reached := stoppedAt)
          (storage := fun atHeap => (filesObserved atHeap).storageObservation)
          (bytes := retryBytes) (rebooted := rebooted) stable source failedInput retryInput diagnostic afterFailure))
    (snapshot : SnapshotReadRequest α) (reopenPtrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)
    (compares : ∀ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      handle.ptrEq = reopenPtrEq →
      source.openTable retryInput afterFailure = .ok handle.table start.reached →
      ∀ {event after}, (NativeOpenedReport.acquire (start := start)).Reached event after →
        reopenPtrEq handle.token handle.token after.reached = .ok true after.reached) :
    call entry = .ok opened.handle.table opened.start.reached ∧
    request.runOnRawOpenPhase directory lookup (appender.run activeRef) (stager.run pendingRef)
      (syncer.group directory.path directoryRef activeRef pendingRef)
      rename opened.handle.phase opened.handle.get opened.handle.set opened.start.reached = .ok sequence reached ∧
    source.openTable failedInput rebooted = .error diagnostic afterFailure ∧
    ∃ (batch : List WAL.Write) (next : NativeOpenedPosition opened.handle)
      (stop : NativeCheckpointSourceStop next primitives fsync cutStage.step reason stoppedAt)
      (poisoned : opened.handle.contents stoppedAt.2 opened.handle.phase = some .poisoned),
      let ending := NativeExecutionEnd.stoppedCheckpoint rfl stop poisoned
      next.reached = reached ∧ next.current.history = batch ∧ ending.Reached ∧
      (∃ chosen, ending.allows chosen ∧ PendingClientReplay ending.submissions next.current.ready.reads chosen ∧
        ∀ read ∈ next.current.ready.reads, read.BoundedBy chosen.length) ∧
      NativeReadyStorage next.current.ready.state (filesObserved stoppedAt.2).storageObservation ∧
      ∃ (crash : NativeReadyQuietCrash next.current.ready.state)
        (handle : NativeOpenedHandle heap) (start last : NativeOpenedPosition handle)
        (events : List NativeExecutionEvent) (reference : SnapshotTable UInt64),
        crash.live = (filesObserved stoppedAt.2).storageObservation.files ∧
        crash.crashNames = (filesObserved stoppedAt.2).storageObservation.crashNames ∧
        RawQuietRebootEntry crash view (fun atHeap => (filesObserved atHeap).storageObservation.files.names)
          retryBytes stoppedAt.2 rebooted (view.descriptors stoppedAt.2) ∧
        source.openTable retryInput afterFailure = .ok handle.table start.reached ∧
        NativeOpenedTrace start [.acquire, .readAt start.pins.length snapshot] events last ∧
        opened.start.current.LedgerSuffix (.acknowledged request batch :: events) last.current ∧
        SnapshotWalReplay .empty batch reference ∧
        last.current.ready.reads = [snapshot.record start.current.ready.state.writer.installed.table.committed
          (snapshot.replay reference start.current.ready.state.writer.installed.table.committed)] ∧
        InstalledClientReplay last.current.submissions last.current.ready.reads last.current.history
          last.current.ready.state.writer.installed last.current.ready.state.session := by
  obtain ⟨actual, _, cache, batch, _, next, nextDirectory, sameDirectory, sameActive, samePending, wrote, _, _, atNext, _,
    ledger, whole, _, reads, physical, _⟩ :=
    opened.acknowledgesFirstWrite used view resolved references atDirectory census cacheAt inodes runs
      (fun atHeap => (filesObserved atHeap).storageObservation) settled
      appender stager syncer inode buffered request lookup rename nonempty seen
  have originalDir := opened.start.directory.trans resolved
  have directoryAtNext := nextDirectory.trans originalDir
  rw [sameDirectory, sameActive, samePending, originalDir] at wrote
  let openedCache : OpenSyncCacheRefs opened.handle.files next.current.ready.state.session.directory.path :=
    ⟨cache.directory, cache.active, cache.pending, cache.references,
      (congrArg DiskDirectory.path nextDirectory).symm ▸ cache.atRoot⟩
  have cacheAtNext := physical.cacheAt
  change view.cacheAt next.reached cache.directory cache.active cache.pending = _ at cacheAtNext
  rw [atNext, sameDirectory, sameActive, samePending] at cacheAtNext
  obtain ⟨stop⟩ := next.checkpointStopsAtReachedCache primitives fsync directoryAtNext cacheAtNext atNext stopped
  obtain ⟨cut⟩ := cutEffects next directoryAtNext atNext openedCache sameDirectory sameActive samePending stop
  have initial : NativeReadyStorage next.current.ready.state
      ((directoryAtNext.symm ▸ filesObserved next.reached :
        RunDirectoryInodeView next.current.ready.state.session.directory (inodes next.reached)
          (runs next.reached)).storageObservation) := by
    rw [storageObservation_cast]
    exact physical.physical
  have stable : NativeReadyStorage next.current.ready.state (filesObserved stoppedAt.2).storageObservation := by
    simpa only [storageObservation_cast] using cut.storageAtStop initial
  have terminal := stop.refinesTerminalLedger cut.returnedKeeps cut.stoppedKeeps ledger
  obtain ⟨retry⟩ := retryEffects next atNext stable
  obtain ⟨boot, denied, handle, start, last, events, reference, reopened, calls, subsequent, replay, observed, _⟩ :=
    retry.readsLatest stop snapshot compares
  have combined := ledger.append subsequent
  have final := opened.refinesLedger combined
  refine ⟨actual, wrote, denied, batch, next, stop, stop.phaseAtStop cut.returnedKeeps cut.stoppedKeeps,
    atNext, whole, terminal.2.1, terminal.2.2, stable, _, handle, start, last, events, reference, rfl, rfl, boot, reopened, calls,
    combined, whole ▸ replay, ?_, final.2.2.2⟩
  simpa only [reads, List.nil_append] using observed

end Alvoki.Storage.DiskSession
