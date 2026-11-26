import Alvoki.Storage.Disk.NativeGroupedWriteRecovery
import Alvoki.Storage.Disk.NativeAlignedWriteRecovery
import Alvoki.Storage.Disk.NativeReadyCallRefinement

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)
open Sequential (SnapshotTable)

/-- The returned preparation, held authority and root identity select
the same plan for read, aligned repair and keeper replacement effects. -/
private abbrev groupedRetryPlanEffects {heap : Type} {opened : NativeOpenedHandle heap}
    (current : NativeOpenedPosition opened) (view : OpenCloseHeapView heap FileImage)
    (request : WriteRequest) (reached : heap) (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (provides : ∀ {batch}, HeldOpenCache heap → current.current.ready.SelectedWritePlan batch
      current.current.ready.state.writer.target (view.files reached).image → Sort u) :=
  ∀ {batch table}, prepareBatch current.current.ready.state.writer.installed.table request.rows =
    some (batch, table) →
    ∀ (held : HeldOpenCache heap) (plan : current.current.ready.SelectedWritePlan batch
      current.current.ready.state.writer.target (view.files reached).image),
      LiteralOpenAuthority view current.current.ready.state.session.directory held held.ready →
      namespaceView.modelObject root = held.captured.inode held.rootSlot.description → provides held plan

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
    {firstOffset : Nat}
    (nameEffects : current.WalNameEffects appender stager syncer cache request lookup rename
      (fun atHeap => (observe atHeap).storageObservation) firstOffset (current.current.history.length + request.rows.length))
    (initialWindow : current.WalWindowAt (fun atHeap => (observe atHeap).storageObservation)
      firstOffset (current.current.history.length + request.rows.length))
    {reached : heap} (admission : source.AlignedAdmissionEffects view current.current.ready.state input reached
      (fun atHeap => (observe atHeap).storageObservation) (fun atHeap => (inodes atHeap).visible))
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (rootBinding : (observe reached).storageObservation.files.names current.current.ready.state.session.directory.path =
      some (namespaceView.modelObject root))
    {returnedAt : heap} {reopened : DiskTable}
    (openedTable : source.openTable input reached = .ok reopened returnedAt)
    (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat)
    (openEffects : groupedRetryPlanEffects current view request reached namespaceView root
      (fun cache plan => source.LiteralOpenEffects cache namespaceView root plan
        (fun atHeap => (observe atHeap).storageObservation) (fun atHeap => (inodes atHeap).visible)))
    (alignedEffects : groupedRetryPlanEffects current view request reached namespaceView root
      (fun cache plan => plan.layout.tail.size = 0 → source.LiteralAlignedRepairEffects cache plan
        (fun atHeap => (observe atHeap).storageObservation) (fun atHeap => (inodes atHeap).visible)))
    (replacementEffects : groupedRetryPlanEffects current view request reached namespaceView root
      (fun cache plan => 0 < plan.layout.tail.size → source.LiteralKeeperReplacementEffects cache
        (current := current.current.ready) plan (fun atHeap => (observe atHeap).storageObservation)
        (fun atHeap => (inodes atHeap).visible)))
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (phase : OpenPhaseCellEffects view.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)

private abbrev retryEffectsFor (attempts : source.FailedCalls rebooted returns reached) : Prop :=
  RawOpenRetryTrace.SelectedEffects view source rebooted (state).writer.target
    (fun atHeap => ⟨names atHeap, fun inode => [visible atHeap inode]⟩) (state).selectedRetryPath
    (RawOpenRetryTrace.RecoveryObservations view state (state).writer.target storage visible firstOffset
      (current.current.history.length + request.rows.length)) attempts

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

include nonempty returned initial groupEffects reset nameEffects initialWindow admission
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
          (∀ {inode}, names reached ((dir).file (.walSegment (state).writer.target.first)) = some inode →
            visible reached inode = (state).writer.target.trimmed →
            names start.reached ((dir).file (.walSegment (state).writer.target.first)) = some inode ∧
              visible start.reached inode = (state).writer.target.trimmed) ∧
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
    have window := reboot.walNamespace nameFrame initialWindow.2
    have upper : (current.current.history ++ batch).length = current.current.history.length + request.rows.length := by
      simp only [List.length_append, (prepareBatch_spec prepared).1]
    obtain ⟨plan, handle, start, nextCache, retained, opened, history, recoveredLedger, _, physical, sameDirectory, coversNext,
      retainedKeeper, nextWindow⟩ :=
      (ready).opensLiteralRepairedAfterWriteRetries storage visible request cause prepared fits admitted
        initialWindow.1 selected (reboot.startsRecoveryObservations reset selected (by simpa only [upper] using window))
        (by simpa only [upper] using retryEffects)
        admission namespaceView root rootBinding (openEffects prepared) (alignedEffects prepared)
        (replacementEffects prepared) phaseIdentity tokenIdentity phase ptrEq openedTable
    have old := history.trans plan.oldHistory
    have appended : start.current.history = current.current.history ++ retained := by
      simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, NativeExecutionEvent.writes] using
        recoveredLedger.history
    have omitted : retained = [] := List.append_cancel_left (by
      simpa only [List.append_nil] using appended.symm.trans old)
    rw [omitted] at recoveredLedger
    exact ⟨handle, start, nextCache, opened, sameDirectory, old, recoveredLedger, physical, coversNext, retainedKeeper, nextWindow⟩
  · exact .inl elsewhere

end

private theorem storageObservation_cast {first last : DiskDirectory} {inodes : WalInodeImage} {runs : RunUnlinkImage}
    (same : first = last) (files : RunDirectoryInodeView first inodes runs) :
    (same ▸ files : RunDirectoryInodeView last inodes runs).storageObservation = files.storageObservation := by
  subst last
  rfl

/-- The final uncertain write fixes the preceding ready calls on the
same handle. Grouped recovery and the next write and snapshot extend
that exact ledger on the actual table returned by the opener. -/
theorem NativeOpenedPosition.groupedRetryAndReads
    {heap stream α : Type} {opened : NativeOpenedHandle heap}
    (start : NativeOpenedPosition opened) (view : OpenCloseHeapView heap FileImage)
    (writes : NativeReadyWriteCalls opened) (issuer : opened.LatestIssuer)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView opened.directory (inodes atHeap) (runs atHeap))
    {origin : NativeExecutionPosition} {earlier : List NativeExecutionEvent}
    (prior : origin.LedgerSuffix earlier start.current)
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    (effects : writes.ReturnEffects view inodes runs (fun atHeap => (observe atHeap).storageObservation) inode buffered)
    (initial : writes.StorageAt view (fun atHeap => (observe atHeap).storageObservation)
      (fun atHeap => (inodes atHeap).visible) start)
    (request : WriteRequest)
    {failed rebooted reached : heap} {cause : IO.Error} {calls : List (NativeReturnedCall opened)}
    (executed : NativeReturnedCalls writes issuer start.reached (start.pins.map NativeOpenedPin.raw)
      (calls ++ [.write request (.error (.commitUnknown cause))]) failed)
    {firstOffset : Nat}
    (readyNames : writes.WalWindowEffects (fun atHeap => (observe atHeap).storageObservation) firstOffset
      (start.current.history.length + (calls.map NativeReturnedCall.requestedRows).sum + request.rows.length))
    (initialWindow : start.WalWindowAt (fun atHeap => (observe atHeap).storageObservation) firstOffset
      (start.current.history.length + (calls.map NativeReturnedCall.requestedRows).sum + request.rows.length))
    (source : RawMarkedOpenInterpreter heap stream) {input : FilePath} {returns : List (FilePath × IO.Error)}
    (attempts : source.FailedCalls rebooted returns reached)
    {returnedAt : heap} {reopened : DiskTable} (openedTable : source.openTable input reached = .ok reopened returnedAt)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (phase : OpenPhaseCellEffects view.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)
    (nextRequest : WriteRequest) {nextSequence : UInt64} {writeHeap : heap} (nextNonempty : nextRequest.rows ≠ [])
    (read : SnapshotReadRequest α) :
    ∃ (current : NativeOpenedPosition opened) (beforeEvents : List NativeExecutionEvent),
      NativeReturnedCalls writes issuer start.reached (start.pins.map NativeOpenedPin.raw) calls current.reached ∧
      beforeEvents.length = calls.length ∧ (∀ pair ∈ calls.zip beforeEvents, pair.1.Records pair.2) ∧
      origin.LedgerSuffix (earlier ++ beforeEvents) current.current ∧
      (NativeReturnedCall.write request (.error (.commitUnknown cause))).Reaches
        writes issuer (current.pins.map NativeOpenedPin.raw) current.reached failed ∧
      let state := current.current.ready.state
      let dir := state.session.directory
      let installed := state.writer.installed
      let files := fun atHeap => current.directory.symm ▸ observe atHeap
      let storage := fun atHeap => (files atHeap).storageObservation
      let names := fun atHeap => (storage atHeap).files.names
      let visible := fun atHeap => (inodes atHeap).visible
      let cache := writes.cacheAtPosition current
      current.GroupedErrorEffects view cache writes.appender writes.stager writes.syncer
          inodes files inode buffered request writes.lookup failed cause →
      ∀ (reboot : RawWriteRebootEntry state view storage names visible failed rebooted),
        reboot.DurableReset →
        current.WalNameEffects writes.appender writes.stager writes.syncer cache request writes.lookup writes.rename
          storage firstOffset (current.current.history.length + request.rows.length) →
        retryEffectsFor current view inodes runs files request source (firstOffset := firstOffset) attempts →
        source.AlignedAdmissionEffects view state input reached storage visible →
        names reached dir.path = some (namespaceView.modelObject root) →
        groupedRetryPlanEffects current view request reached namespaceView root
          (fun held plan => source.LiteralOpenEffects held namespaceView root plan storage visible) →
        groupedRetryPlanEffects current view request reached namespaceView root
          (fun held plan => plan.layout.tail.size = 0 → source.LiteralAlignedRepairEffects held plan storage visible) →
        groupedRetryPlanEffects current view request reached namespaceView root
          (fun held plan => 0 < plan.layout.tail.size →
            source.LiteralKeeperReplacementEffects held (current := current.current.ready) plan storage visible) →
        (∀ (handle : NativeOpenedHandle heap) (reopened : NativeOpenedPosition handle)
          (refs : OpenSyncCacheRefs handle.files reopened.current.ready.state.session.directory.path),
          source.openTable input reached = .ok handle.table reopened.reached →
          reopened.current.history = current.current.history →
          reopened.WriteStorageEntry view refs (storage reopened.reached) (visible reopened.reached) →
          reopened.ObservesPublishedWrite writes.appender writes.stager writes.syncer view refs inodes runs storage
            inode buffered nextRequest writes.lookup writes.rename nextSequence writeHeap ∧ handle.ObservesSnapshotToken writeHeap) →
        opened.table.UsesOpenWriteSchedules dir opened.files opened.phase ∧
        ∃ batch table guarded poisoned,
          prepareBatch installed.table request.rows = some (batch, table) ∧
          checkActiveSegmentWith dir installed writes.lookup current.reached = .ok () guarded ∧
          opened.set opened.phase .poisoned guarded = .ok () poisoned ∧
          let groupFailed := groupedFailure current cache writes.appender writes.stager writes.syncer request
            (failed := failed) (cause := cause) batch poisoned
          ¬ groupFailed ∨
          (groupFailed ∧
            ∃ (handle : NativeOpenedHandle heap) (reopened written last : NativeOpenedPosition handle)
              (refs : OpenSyncCacheRefs handle.files reopened.current.ready.state.session.directory.path)
              (nextBatch : List WAL.Write) (afterEvents : List NativeExecutionEvent) (reference : SnapshotTable UInt64),
              let directory := reopened.current.ready.state.session.directory
              source.openTable input reached = .ok handle.table reopened.reached ∧
              reopened.WriteStorageEntry view refs (storage reopened.reached) (visible reopened.reached) ∧
              (∀ offset ∈ reopened.current.ready.state.writer.wal.segments.map WalSegment.first, firstOffset ≤ offset) ∧
              (∀ {inode}, names reached (dir.file (.walSegment state.writer.target.first)) = some inode →
                visible reached inode = state.writer.target.trimmed →
                names reopened.reached (dir.file (.walSegment state.writer.target.first)) = some inode ∧
                  visible reopened.reached inode = state.writer.target.trimmed) ∧
              (∀ through, reopened.current.ready.state.writer.wal.SettledNamespaceWindow directory firstOffset through
                (storage reopened.reached)) ∧
              handle.table.UsesOpenWriteSchedules directory handle.files handle.phase ∧
              nextRequest.runOnRawOpenPhase directory writes.lookup (writes.appender.run refs.active)
                (writes.stager.run refs.pending) (writes.syncer.group directory.path refs.directory refs.active refs.pending)
                writes.rename handle.phase handle.get handle.set reopened.reached = .ok nextSequence writeHeap ∧
              written.reached = writeHeap ∧
              NativeOpenedTrace written [.acquire, .readAt written.pins.length read] afterEvents last ∧
              origin.LedgerSuffix ((earlier ++ beforeEvents) ++
                .uncertainWriteCrashRecovered request input cause batch [] :: .acknowledged nextRequest nextBatch :: afterEvents)
                last.current ∧
              SnapshotWalReplay .empty (current.current.history ++ nextBatch) reference ∧
              (∀ observation ∈ last.current.ready.reads, observation.agrees reference) ∧
              handle.ReturnsLatestAfter (reopened.readyWriteCalls refs writes.appender writes.stager writes.syncer
                writes.lookup writes.rename) [.write nextRequest (.ok nextSequence)] read nextSequence
                (some (read.replay reference nextSequence)) reopened.reached last.reached) := by
  obtain ⟨current, beforeEvents, ran, _, prefixStorage, length, records, suffix, window, observed⟩ :=
    executed.refinesReadyBeforeWrite (fun _ declared => by cases declared) view inodes runs
      (fun atHeap => (observe atHeap).storageObservation) inode buffered effects start rfl rfl initial readyNames initialWindow
  have through := prior.append suffix
  refine ⟨current, beforeEvents, ran, length, records, through, observed, ?_⟩
  intro state dir installed files storage names visible cache groupEffects reboot reset nameEffects retryEffects admission
    rootBinding openEffects alignedEffects replacementEffects nextCall
  have sameStorage : storage = fun atHeap => (observe atHeap).storageObservation := by
    funext atHeap
    exact storageObservation_cast current.directory.symm (observe atHeap)
  have ready : NativeReadyStorage state (storage current.reached) := by
    rw [sameStorage]
    exact prefixStorage.physical
  have readyWindow : current.WalWindowAt storage firstOffset (current.current.history.length + request.rows.length) :=
    sameStorage.symm ▸ window
  have nonempty := writes.commitUnknownHasRows current observed
  have returned := writes.returnedWriteAt current observed
  obtain ⟨schedules, batch, table, guarded, poisoned, prepared, guard, assigned, classified⟩ :=
    current.reopensAfterGroupedError view cache writes.appender writes.stager writes.syncer inodes runs files
      inode buffered request writes.lookup writes.rename nonempty returned ready groupEffects reboot reset source
      nameEffects readyWindow admission namespaceView root rootBinding openedTable phaseIdentity tokenIdentity
      openEffects alignedEffects replacementEffects phase ptrEq attempts retryEffects
  refine ⟨schedules, batch, table, guarded, poisoned, prepared, guard, assigned, ?_⟩
  rcases classified with elsewhere |
    ⟨group, handle, reopened, refs, opened, _, old, recoveredLedger, physical, coversNext, retainedKeeper, nextWindow⟩
  · exact .inl elsewhere
  · refine .inr ⟨group, ?_⟩
    obtain ⟨write, token⟩ := nextCall handle reopened refs opened old physical
    obtain ⟨schedules, writeReturn, nextBatch, _, written, last, reference, afterEvents, _, _, reachedWrite, snapshots,
      wrote, replay, agrees, sourceCalls⟩ :=
      reopened.acknowledgesAndReadsLatest writes.appender writes.stager writes.syncer view refs inodes runs storage
        inode buffered nextRequest writes.lookup writes.rename nextNonempty physical write read token
    exact ⟨handle, reopened, written, last, refs, nextBatch, afterEvents, reference, opened, physical, coversNext, retainedKeeper,
      nextWindow, schedules, writeReturn, reachedWrite, snapshots, through.append (recoveredLedger.append wrote),
      old ▸ replay, agrees, sourceCalls⟩

end Alvoki.Storage.DiskSession
