import Alvoki.Storage.Disk.NativeGroupedWriteRecovery
import Alvoki.Storage.Disk.NativeAlignedWriteRecovery
import Alvoki.Storage.Disk.NativePublishedWriteSnapshot

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)
open Sequential (SnapshotTable)

section

variable {heap stream : Type} {opened : NativeOpenedHandle heap}
  (current : NativeOpenedPosition opened) (view : OpenCloseHeapView heap FileImage)
  (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
  (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
  (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
  (observe : ∀ atHeap, RunDirectoryInodeView current.current.ready.state.session.directory (inodes atHeap) (runs atHeap))

local notation "ready" => current.current.ready
local notation "state" => current.current.ready.state
local notation "dir" => current.current.ready.state.session.directory
local notation "installed" => current.current.ready.state.writer.installed
local notation "storage" => fun atHeap => RunDirectoryInodeView.storageObservation (observe atHeap)
local notation "names" => fun atHeap => CheckpointSurvivingFiles.names (CheckpointStorageObservation.files (storage atHeap))
local notation "visible" => fun atHeap => WalInodeImage.visible (inodes atHeap)

variable
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {failed : heap} {cause : IO.Error}
    (nonempty : request.rows ≠ [])
    (returned : request.runOnRawOpenPhase current.current.ready.state.session.directory lookup
      (appender.run cache.active) (stager.run cache.pending)
      (syncer.group current.current.ready.state.session.directory.path cache.directory cache.active cache.pending)
      rename opened.phase opened.get opened.set current.reached = .error (.commitUnknown cause) failed)
    (initial : NativeReadyStorage current.current.ready.state (observe current.reached).storageObservation)
    (groupEffects : current.GroupedErrorEffects view cache appender stager syncer inodes observe inode buffered
      request lookup failed cause)
    {rebooted : heap} (reboot : RawWriteRebootEntry current.current.ready.state view
      (fun atHeap => (observe atHeap).storageObservation) (fun atHeap => (observe atHeap).storageObservation.files.names)
      (fun atHeap => (inodes atHeap).visible) failed rebooted)
    (reset : reboot.DurableReset)
    (source : RawMarkedOpenInterpreter heap stream) {input : FilePath} {returns : List (FilePath × IO.Error)}
    {firstOffset : Nat} (covers : ∀ offset ∈ current.current.ready.state.writer.wal.segments.map WalSegment.first,
      firstOffset ≤ offset)
    (nameEffects : current.WalNameEffects appender stager syncer cache request lookup rename
      (fun atHeap => (observe atHeap).storageObservation) firstOffset (current.current.history.length + request.rows.length))
    (initialWindow : current.current.ready.state.writer.wal.SettledNamespaceWindow current.current.ready.state.session.directory
      firstOffset (current.current.history.length + request.rows.length) (observe current.reached).storageObservation)
    {reached : heap} (admission : source.AlignedAdmissionEffects view current.current.ready.state input reached
      (fun atHeap => (observe atHeap).storageObservation) (fun atHeap => (inodes atHeap).visible))
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (rootBinding : (observe reached).storageObservation.files.names current.current.ready.state.session.directory.path =
      some (namespaceView.modelObject root))
    {returnedAt : heap} {reopened : DiskTable}
    (openedTable : source.openTable input reached = .ok reopened returnedAt)
    (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat)
    (openEffects : ∀ {batch table}, prepareBatch current.current.ready.state.writer.installed.table request.rows =
      some (batch, table) →
      ∀ (cache : HeldOpenCache heap) (plan : current.current.ready.SelectedWritePlan batch
        current.current.ready.state.writer.target (view.files reached).image),
        LiteralOpenAuthority view current.current.ready.state.session.directory cache cache.ready →
        namespaceView.modelObject root = cache.captured.inode cache.rootSlot.description →
        source.LiteralOpenEffects cache namespaceView root plan
          (fun atHeap => (observe atHeap).storageObservation) (fun atHeap => (inodes atHeap).visible))
    (alignedEffects : ∀ {batch table}, prepareBatch current.current.ready.state.writer.installed.table request.rows =
      some (batch, table) →
      ∀ (cache : HeldOpenCache heap) (plan : current.current.ready.SelectedWritePlan batch
        current.current.ready.state.writer.target (view.files reached).image),
        LiteralOpenAuthority view current.current.ready.state.session.directory cache cache.ready →
        namespaceView.modelObject root = cache.captured.inode cache.rootSlot.description →
        plan.layout.tail.size = 0 →
        source.LiteralAlignedRepairEffects cache plan
          (fun atHeap => (observe atHeap).storageObservation) (fun atHeap => (inodes atHeap).visible))
    (replacementEffects : ∀ {batch table}, prepareBatch current.current.ready.state.writer.installed.table request.rows =
      some (batch, table) →
      ∀ (cache : HeldOpenCache heap) (plan : current.current.ready.SelectedWritePlan batch
        current.current.ready.state.writer.target (view.files reached).image),
        LiteralOpenAuthority view current.current.ready.state.session.directory cache cache.ready →
        namespaceView.modelObject root = cache.captured.inode cache.rootSlot.description →
        0 < plan.layout.tail.size →
        source.LiteralKeeperReplacementEffects cache (current := current.current.ready) plan
          (fun atHeap => (observe atHeap).storageObservation) (fun atHeap => (inodes atHeap).visible))
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (phase : OpenPhaseCellEffects view.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)

private abbrev retryEffectsFor (attempts : source.FailedCalls rebooted returns reached) : Prop :=
  RawOpenRetryTrace.SelectedEffects view source rebooted (state).writer.target
    (fun atHeap => ⟨names atHeap, fun inode => [visible atHeap inode]⟩) (state).selectedRetryPath
    (fun atHeap => (state).writer.wal.NamespaceWindow dir firstOffset
      (current.current.history.length + request.rows.length) (names atHeap) ∧
      RawOpenRetryTrace.KeeperAt view dir (state).writer.target names visible atHeap ∧
      (state).SelectedRetryDurability (state).writer.target (storage atHeap) ∧
      RawOpenRetryTrace.LaterWalAt view dir (state).writer.target names atHeap) attempts

private abbrev groupedFailure (batch : List WAL.Write) (poisoned : heap) : Prop :=
  let keeperPath := (dir).file (.walSegment (installed).activeFirst)
  let staging := (dir).file .stagedWalBoundary
  ∃ appended staged,
    appender.run cache.active keeperPath (WAL.encodeBatch batch) poisoned = .ok () appended ∧
    stager.run cache.pending staging
      (WAL.Boundary.encode ((installed).walBytes + WAL.frameSize * request.rows.length).toUInt64) appended =
        .ok () staged ∧
    syncer.group (dir).path cache.directory cache.active cache.pending #[keeperPath, staging] staged =
      .error cause failed

include nonempty returned initial groupEffects reset covers nameEffects initialWindow admission
  rootBinding openedTable phaseIdentity tokenIdentity openEffects alignedEffects replacementEffects phase ptrEq

/-- Classify the returned write at the grouped fsync boundary and
interpret the literal next open on the same reboot observation. The
returned handle can issue another write using its physical entry and
settled WAL names. When the keeper contains uncommitted bytes, the
actual open replaces it while keeping the previous history intact. -/
theorem NativeOpenedPosition.reopensAfterGroupedError
    (attempts : source.FailedCalls rebooted returns reached)
    (retryEffects : retryEffectsFor current view inodes runs observe request source (firstOffset := firstOffset) attempts) :
    opened.table.UsesOpenWriteSchedules dir opened.files opened.phase ∧
    ∃ batch table guarded poisoned,
      prepareBatch (installed).table request.rows = some (batch, table) ∧
      checkActiveSegmentWith dir installed lookup current.reached = .ok () guarded ∧
      opened.set opened.phase .poisoned guarded = .ok () poisoned ∧
      let groupFailed := groupedFailure current cache appender stager syncer request
        (failed := failed) (cause := cause) batch poisoned
      ¬ groupFailed ∨
      (groupFailed ∧
        ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle)
          (nextCache : OpenSyncCacheRefs handle.files start.current.ready.state.session.directory.path),
          let directory := start.current.ready.state.session.directory
          source.openTable input reached = .ok handle.table start.reached ∧
          directory = dir ∧
          start.current.history = current.current.history ∧
          current.current.LedgerSuffix [.uncertainWriteCrashRecovered request input cause batch []] start.current ∧
          start.WriteStorageEntry view nextCache (storage start.reached) (visible start.reached) ∧
          (∀ offset ∈ start.current.ready.state.writer.wal.segments.map WalSegment.first, firstOffset ≤ offset) ∧
          ∀ through, start.current.ready.state.writer.wal.SettledNamespaceWindow directory firstOffset through
            (storage start.reached)) := by
  obtain ⟨schedules, batch, table, guarded, poisoned, prepared, fits, guard, assigned, classified⟩ :=
    current.selectsAfterGroupedError view cache appender stager syncer inodes observe inode buffered request lookup rename
      nonempty returned initial groupEffects reboot
  refine ⟨schedules, batch, table, guarded, poisoned, prepared, guard, assigned, ?_⟩
  rcases classified with ⟨group, admitted, selected, _, _⟩ | elsewhere
  · refine .inr ⟨group, ?_⟩
    have nameFrame := current.preservesWalNamesAfterCommitUnknown appender stager syncer cache request lookup rename
      nonempty returned nameEffects
    have window := reboot.walNamespace nameFrame initialWindow
    have upper : (current.current.history ++ batch).length = current.current.history.length + request.rows.length := by
      simp only [List.length_append, (prepareBatch_spec prepared).1]
    obtain ⟨plan, handle, start, nextCache, retained, opened, history, recoveredLedger, _, physical, sameDirectory, coversNext, nextWindow⟩ :=
      (ready).opensLiteralRepairedAfterWriteRetries storage visible request cause prepared fits admitted
        covers selected (by simpa only [upper] using window) (reboot.startsDurableRetry reset selected).2
        (reboot.laterNames selected.valid.selected.symm) (by simpa only [upper] using retryEffects)
        admission namespaceView root rootBinding (openEffects prepared) (alignedEffects prepared)
        (replacementEffects prepared) phaseIdentity tokenIdentity phase ptrEq openedTable
    have old := history.trans plan.oldHistory
    have appended : start.current.history = current.current.history ++ retained := by
      simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, NativeExecutionEvent.writes] using
        recoveredLedger.history
    have omitted : retained = [] := List.append_cancel_left (by
      simpa only [List.append_nil] using appended.symm.trans old)
    rw [omitted] at recoveredLedger
    exact ⟨handle, start, nextCache, opened, sameDirectory, old, recoveredLedger, physical, coversNext, nextWindow⟩
  · exact .inl elsewhere

/-- Interpret the reported group error and retry calls on the same physical
observation, then derive a ledger through the write and snapshot on the
table returned by recovery. A different fault stage is classified separately. -/
theorem NativeOpenedPosition.groupedRetryAndReads
    (retry : ∃ attempts : source.FailedCalls rebooted returns reached, returns ≠ [] ∧
      retryEffectsFor current view inodes runs observe request source (firstOffset := firstOffset) attempts)
    (nextRequest : WriteRequest) (nextSequence : UInt64) (writeHeap : heap) (nextNonempty : nextRequest.rows ≠ [])
    (read : SnapshotReadRequest α)
    (nextCall : ∀ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle)
      (nextCache : OpenSyncCacheRefs handle.files start.current.ready.state.session.directory.path),
      source.openTable input reached = .ok handle.table start.reached →
      start.current.history = current.current.history →
      start.WriteStorageEntry view nextCache (storage start.reached) (visible start.reached) →
      start.ObservesPublishedWrite appender stager syncer view nextCache inodes runs storage
        inode buffered nextRequest lookup rename nextSequence writeHeap ∧ handle.ObservesSnapshotToken writeHeap) :
    opened.table.UsesOpenWriteSchedules dir opened.files opened.phase ∧
    source.FailedCalls rebooted returns reached ∧ returns ≠ [] ∧
    ∃ batch table guarded poisoned,
      prepareBatch (installed).table request.rows = some (batch, table) ∧
      checkActiveSegmentWith dir installed lookup current.reached = .ok () guarded ∧
      opened.set opened.phase .poisoned guarded = .ok () poisoned ∧
      let groupFailed := groupedFailure current cache appender stager syncer request
        (failed := failed) (cause := cause) batch poisoned
      ¬ groupFailed ∨
      (groupFailed ∧
        ∃ (handle : NativeOpenedHandle heap) (start written last : NativeOpenedPosition handle)
          (nextCache : OpenSyncCacheRefs handle.files start.current.ready.state.session.directory.path)
          (nextBatch : List WAL.Write) (events : List NativeExecutionEvent) (reference : SnapshotTable UInt64),
          let directory := start.current.ready.state.session.directory
          source.openTable input reached = .ok handle.table start.reached ∧
          (∀ offset ∈ start.current.ready.state.writer.wal.segments.map WalSegment.first, firstOffset ≤ offset) ∧
          (∀ through, start.current.ready.state.writer.wal.SettledNamespaceWindow directory firstOffset through
            (storage start.reached)) ∧
          handle.table.UsesOpenWriteSchedules directory handle.files handle.phase ∧
          nextRequest.runOnRawOpenPhase directory lookup (appender.run nextCache.active)
            (stager.run nextCache.pending)
            (syncer.group directory.path nextCache.directory nextCache.active nextCache.pending)
            rename handle.phase handle.get handle.set start.reached = .ok nextSequence writeHeap ∧
          written.reached = writeHeap ∧
          NativeOpenedTrace written [.acquire, .readAt written.pins.length read] events last ∧
          current.current.LedgerSuffix
            (.uncertainWriteCrashRecovered request input cause batch [] :: .acknowledged nextRequest nextBatch :: events)
            last.current ∧
          SnapshotWalReplay .empty (current.current.history ++ nextBatch) reference ∧
          (∀ observation ∈ last.current.ready.reads, observation.agrees reference) ∧
          handle.ReturnsLatestAfter
            [.writeOnPhase handle directory nextCache appender stager syncer nextRequest lookup rename (.ok nextSequence)]
            read nextSequence (some (read.replay reference nextSequence)) start.reached last.reached) := by
  obtain ⟨attempts, retried, retryEffects⟩ := retry
  obtain ⟨schedules, batch, table, guarded, poisoned, prepared, guard, assigned, classified⟩ :=
    current.reopensAfterGroupedError view cache appender stager syncer inodes runs observe inode buffered request lookup rename
      nonempty returned initial groupEffects reboot reset source covers nameEffects initialWindow admission namespaceView root
      rootBinding openedTable phaseIdentity tokenIdentity openEffects alignedEffects replacementEffects phase ptrEq
      attempts retryEffects
  refine ⟨schedules, attempts, retried, batch, table, guarded, poisoned, prepared, guard, assigned, ?_⟩
  rcases classified with elsewhere |
    ⟨group, handle, start, nextCache, opened, _, old, recoveredLedger, physical, coversNext, nextWindow⟩
  · exact .inl elsewhere
  · refine .inr ⟨group, ?_⟩
    obtain ⟨write, token⟩ := nextCall handle start nextCache opened old physical
    obtain ⟨schedules, writeReturn, nextBatch, _, written, last, reference, events, _, _, reachedWrite, snapshots,
      wrote, replay, agrees, sourceCalls⟩ :=
      start.acknowledgesAndReadsLatest appender stager syncer view nextCache inodes runs storage inode buffered
        nextRequest lookup rename nextNonempty physical write read token
    exact ⟨handle, start, written, last, nextCache, nextBatch, events, reference, opened, coversNext, nextWindow, schedules,
      writeReturn, reachedWrite, snapshots, recoveredLedger.append wrote, old ▸ replay, agrees, sourceCalls⟩

end

end Alvoki.Storage.DiskSession
