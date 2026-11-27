import Alvoki.Storage.Disk.NativeOpenWrite
import Alvoki.Storage.Disk.NativeLateWriteRecovery
import Alvoki.Storage.Disk.NativeEarlyWriteRecovery

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentCommit WalSegmentRepair
open WAL.Boundary (WalInodeImage)

private abbrev PublicationStopM (heap stop error : Type) := ExceptT error (EStateM stop heap)
private abbrev RootStopM (heap error : Type) := PublicationStopM heap IO.FS.Handle error

private def asPublicationReturn {heap stop error α : Type}
    (action : EStateM error heap α) : PublicationStopM heap stop error α :=
  fun before => match action before with
    | .ok value reached => .ok (.ok value) reached
    | .error cause reached => .ok (.error cause) reached

private def classify {heap stop error α : Type} (kind : IO.Error → error)
    (action : PublicationStopM heap stop IO.Error α) : PublicationStopM heap stop error α :=
  fun before => match action.run before with
    | .ok result reached => .ok (result.mapError kind) reached
    | .error handle issued => .error handle issued

private abbrev RawSyncCalls.rootWithFsync {heap : Type} (calls : RawSyncCalls heap)
    (directory : DiskDirectory) {files : DiskTable.OpenSyncFiles}
    (cache : OpenSyncCacheRefs files directory.path)
    (fsync : IO.FS.Handle → EStateM IO.FS.Handle heap (Except IO.Error Unit)) : RootStopM heap IO.Error Unit :=
  SyncPathGroup.run (fun path => calls.toRawSyncCacheCalls.syncPath asPublicationReturn fsync
    directory.path path cache.directory cache.active cache.pending)
    #[directory.path]

/-- Observe an interruption at the original final fsync. Every earlier
callback has its ordinary return. A returned I/O error is inside
`Except`; the outer stop records the selected handle and reached heap. -/
noncomputable def RawSyncCalls.commitUntilRootFsync {heap : Type} (calls : RawSyncCalls heap)
    (directory : DiskDirectory) {files : DiskTable.OpenSyncFiles}
    (cache : OpenSyncCacheRefs files directory.path)
    (append : RawWalAppendCalls heap) (stage : RawWalStageCalls heap)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (fsync : IO.FS.Handle → EStateM IO.FS.Handle heap (Except IO.Error Unit))
    (first count : Nat) (bytes : ByteArray) : EStateM IO.FS.Handle heap (Except IO.Error Unit) :=
  (commitBytesAt directory first bytes count
    (fun path payload => asPublicationReturn (append.run cache.active path payload))
    (fun path payload => asPublicationReturn (stage.run cache.pending path payload))
    (fun paths => if paths = #[directory.path] then calls.rootWithFsync directory cache fsync
      else asPublicationReturn (calls.group directory.path cache.directory cache.active cache.pending paths))
    (fun source target => asPublicationReturn (rename source target))).run

theorem RawSyncCalls.stopsAtRootFsync {heap : Type} (calls : RawSyncCalls heap)
    (directory : DiskDirectory) {files : DiskTable.OpenSyncFiles}
    (cache : OpenSyncCacheRefs files directory.path)
    (append : RawWalAppendCalls heap) (stage : RawWalStageCalls heap)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (fsync : IO.FS.Handle → EStateM IO.FS.Handle heap (Except IO.Error Unit))
    {first count : Nat} {bytes : ByteArray} {entry appended staged grouped renamed issued reached : heap}
    {handle : IO.FS.Handle}
    (wrote : append.run cache.active (directory.file (.walSegment first)) bytes entry = .ok () appended)
    (remembered : stage.run cache.pending (directory.file .stagedWalBoundary) (WAL.Boundary.encode count.toUInt64)
      appended = .ok () staged)
    (synced : calls.group directory.path cache.directory cache.active cache.pending
      #[directory.file (.walSegment first), directory.file .stagedWalBoundary] staged = .ok () grouped)
    (moved : rename (directory.file .stagedWalBoundary) (directory.file .walBoundary) grouped = .ok () renamed)
    (loaded : calls.readDirectory cache.directory renamed = .ok (some handle) issued)
    (stopped : fsync handle issued = .error handle reached) :
    calls.commitUntilRootFsync directory cache append stage rename fsync first count bytes entry = .error handle reached := by
  have groupByFiles : #[directory.file (.walSegment first), directory.file .stagedWalBoundary] ≠ #[directory.path] := by
    intro same
    have impossible : (2 : Nat) = 1 := congrArg Array.size same
    omega
  let syncRoot := fun path => calls.toRawSyncCacheCalls.syncPath asPublicationReturn
    (m := RootStopM heap IO.Error) fsync
    directory.path path cache.directory cache.active cache.pending
  have chosen : syncRoot directory.path renamed = .error handle reached := by
    simp [syncRoot, RawSyncCacheCalls.syncPath, syncWithHandles, Bind.bind, ExceptT.bind,
      ExceptT.bindCont, ExceptT.mk, EStateM.bind, asPublicationReturn, loaded, Pure.pure, ExceptT.pure, EStateM.pure, stopped]
  have rootIssued : calls.rootWithFsync directory cache fsync renamed = .error handle reached := by
    change (SyncPathGroup.run syncRoot #[directory.path]) renamed = _
    simp [SyncPathGroup.run, ← Array.forIn_toList, List.forIn_cons, List.forIn_nil, MonadExcept.tryCatch,
      MonadExceptOf.tryCatch, tryCatchThe, ExceptT.tryCatch, Bind.bind, ExceptT.bind, ExceptT.mk,
      EStateM.bind, StateT.pure, Pure.pure, ExceptT.pure, chosen]
  unfold commitUntilRootFsync
  rw [commitBytesAt_fileEffects]
  simp only [WAL.Boundary.commit, ExceptT.run, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, EStateM.bind,
    asPublicationReturn, wrote, remembered, groupByFiles, ↓reduceIte, synced, moved, rootIssued]

/-- Interpret an unresolved publication callback through the public
dispatcher on the same heap as the original phase and metadata callbacks. -/
noncomputable def WriteRequest.runUntilPublicationStop {heap stop : Type}
    (request : WriteRequest) (directory : DiskDirectory)
    (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (publish : Installed → ByteArray → Nat → EStateM stop heap (Except IO.Error Unit))
    (phase : IO.Ref (Phase Installed))
    (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit) :
    EStateM stop heap (Except DiskWriteError UInt64) :=
  let load : PublicationStopM heap stop DiskWriteError Installed := do
    let stored ← classify .rejected (asPublicationReturn (get phase))
    liftExcept ((stored.installed : Except IO.Error Installed).mapError DiskWriteError.rejected)
  (request.runWithPublication load
    (fun installed => classify .rejected (asPublicationReturn (checkActiveSegmentWith directory installed lookup)))
    (fun next => classify .rejected (asPublicationReturn (set phase next)))
    (fun installed bytes count => classify .commitUnknown (publish installed bytes count))).run

/-- The reached guard and poison setter lead to the publication. Its
outer stop exits the schedule before the ready setter and acknowledgement. -/
theorem WriteRequest.stopsDuringPublication {heap stop : Type} (request : WriteRequest) (directory : DiskDirectory)
    (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (publish : Installed → ByteArray → Nat → EStateM stop heap (Except IO.Error Unit))
    (phase : IO.Ref (Phase Installed))
    (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit)
    {installed : Installed} {batch : List WAL.Write} {table : PackedTable}
    {entry guarded poisoned reached : heap} {tag : stop}
    (nonempty : request.rows ≠ [])
    (prepared : prepareBatch installed.table request.rows = some (batch, table))
    (fits : installed.walBytes + WAL.frameSize * request.rows.length < UInt64.size)
    (loaded : get phase entry = .ok (.ready installed) entry)
    (guard : checkActiveSegmentWith directory installed lookup entry = .ok () guarded)
    (assigned : set phase .poisoned guarded = .ok () poisoned)
    (commit : publish installed (WAL.encodeBatch batch) (installed.walBytes + WAL.frameSize * request.rows.length)
      poisoned = .error tag reached) :
    request.runUntilPublicationStop directory lookup publish phase get set entry = .error tag reached := by
  cases request with
  | single key value =>
    rw [WriteRequest.rows, prepareBatch_singleton] at prepared
    cases written : installed.table.write key value with
    | none => simp [prepareWrite, written] at prepared
    | some next =>
      simp only [prepareWrite, written, Option.map_some, Option.some.injEq, Prod.mk.injEq] at prepared
      obtain ⟨rfl, rfl⟩ := prepared
      simp only [WriteRequest.rows, List.length_singleton, Nat.mul_one, WAL.encodeBatch_singleton] at fits commit
      simp [runUntilPublicationStop, runWithPublication, withPreparedSingleWrite, prepareWrite, WriteRequest.requireWritePreparation,
        publishPreparedWrite, publishPrepared, classify, asPublicationReturn, loaded, written, fits, guard, assigned, commit,
        Phase.installed, liftExcept, Except.pure, Except.mapError, Bind.bind, ExceptT.bind, ExceptT.bindCont,
        ExceptT.mk, ExceptT.run, EStateM.bind, Pure.pure, ExceptT.pure, EStateM.pure]
  | batch rows =>
    simp only [WriteRequest.rows] at fits prepared commit
    have present : rows.isEmpty = false := by
      cases rows <;> simp_all [WriteRequest.rows]
    simp [runUntilPublicationStop, runWithPublication, writeBatchSchedule, WriteRequest.requireWritePreparation, publishPreparedWrite,
      publishPrepared, classify, asPublicationReturn, loaded, present, fits, prepared, guard, assigned, commit, Phase.installed,
      liftExcept, Except.pure, Except.mapError, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run,
      EStateM.bind, Pure.pure, ExceptT.pure, EStateM.pure]

/-- The public dispatcher observing the original final directory fsync. -/
noncomputable def WriteRequest.runUntilRootFsync {heap : Type} (request : WriteRequest) (directory : DiskDirectory)
    {files : DiskTable.OpenSyncFiles} (cache : OpenSyncCacheRefs files directory.path)
    (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (append : RawWalAppendCalls heap) (stage : RawWalStageCalls heap) (calls : RawSyncCalls heap)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (fsync : IO.FS.Handle → EStateM IO.FS.Handle heap (Except IO.Error Unit))
    (phase : IO.Ref (Phase Installed))
    (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit) :
    EStateM IO.FS.Handle heap (Except DiskWriteError UInt64) :=
  request.runUntilPublicationStop directory lookup
    (fun installed bytes count => calls.commitUntilRootFsync directory cache append stage rename fsync
      installed.activeFirst count bytes) phase get set

/-- The selected history adds zero or all of one unanswered request to
the incoming client prefix. Recovery adds one uncertain submission and
does not add a read or an acknowledgement. -/
structure NativeExecutionPosition.InterruptedWriteLedger
    (origin current : NativeExecutionPosition) (events : List NativeExecutionEvent)
    (request : WriteRequest) (batch retained history : List WAL.Write) : Prop where
  prepared : ∃ table, prepareBatch current.ready.state.writer.installed.table request.rows = some (batch, table)
  whole : retained = [] ∨ retained = batch
  history_eq : history = (origin.history ++ events.flatMap NativeExecutionEvent.writes) ++ retained
  pending : PendingClientReplay
    ((origin.submissions ++ events.flatMap NativeExecutionEvent.submissions) ++ [.uncertainBatch batch])
    (origin.ready.reads ++ events.flatMap NativeExecutionEvent.reads) history
  bounded : ∀ read ∈ origin.ready.reads ++ events.flatMap NativeExecutionEvent.reads,
    read.BoundedBy history.length

/-- Recover the ledger at the sampled target before the next opener is
chosen. The literal open and its snapshot lookup use that same history. -/
theorem NativeExecutionPosition.SelectedWriteReboot.interruptedPlan
    {heap : Type} {view : OpenCloseHeapView heap FileImage}
    {storage : heap → CheckpointStorageObservation} {visible : heap → Nat → ByteArray}
    {firstOffset : Nat} {request : WriteRequest} {batch : List WAL.Write} {table : PackedTable} {target : Target}
    {stopped rebooted : heap} {current : NativeExecutionPosition}
    (handoff : current.SelectedWriteReboot view storage visible firstOffset request batch table target stopped rebooted) :
    ∃ (plan : current.ready.SelectedWritePlan batch target (view.files rebooted).image) (retained : List WAL.Write),
      target.range.through = plan.history.length ∧
      (∀ {origin : NativeExecutionPosition} {events : List NativeExecutionEvent},
        origin.LedgerSuffix events current → origin.InterruptedWriteLedger current events request batch retained plan.history) ∧
      ∀ {stream : Type} (opener : RawMarkedOpenInterpreter heap stream) namespaceView root,
        current.ready.state.writer.target.pair.manifest = none →
        opener.ReplaysWalBeforeCheckpointAtOpen view current.ready.state.session.directory current.ready.state.writer.wal.active.first
          storage visible rebooted namespaceView root
          plan.history := by
  obtain ⟨plan, opens⟩ := handoff.sampledPlan
  obtain ⟨retained, whole, selected⟩ : ∃ retained : List WAL.Write,
      (retained = [] ∨ retained = batch) ∧ plan.history = current.history ++ retained := by
    rcases plan.allowed with old | complete
    · exact ⟨[], .inl rfl, by simpa only [List.append_nil] using old⟩
    · exact ⟨batch, .inr rfl, complete⟩
  have cutoff := (congrArg (fun target : Target => target.range.through) plan.targetEq).symm.trans plan.layout.through
  refine ⟨plan, retained, cutoff, ?_, @opens⟩
  intro origin events prior
  refine ⟨⟨table, handoff.prepared⟩, whole, ?_, ?_, ?_⟩
  · simpa only [← prior.history] using selected
  · simpa only [← prior.submissions, ← prior.reads] using plan.pending
  · simpa only [← prior.reads] using plan.bounded

section PhysicalStop

variable {heap : Type} {opened : NativeOpenedHandle heap}
  (current : NativeOpenedPosition opened) (calls : RawSyncCalls heap)

local notation "state" => current.current.ready.state
local notation "dir" => current.current.ready.state.session.directory
local notation "first" => current.current.ready.state.writer.installed.activeFirst
local notation "stagePath" => DiskDirectory.file dir DiskFile.stagedWalBoundary
local notation "markerPath" => DiskDirectory.file dir DiskFile.walBoundary

variable (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
  (view : OpenCloseHeapView heap FileImage)
  (append : RawWalAppendCalls heap) (stage : RawWalStageCalls heap)
  (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
  (observe : ∀ atHeap, RunDirectoryInodeView current.current.ready.state.session.directory (inodes atHeap) (runs atHeap))
  (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)

local notation "storage" => fun atHeap => RunDirectoryInodeView.storageObservation (observe atHeap)

/-- Returns of the exact append, stage, rename and directory-fsync
callbacks reached by one interrupted request on the opened table. -/
structure NativeOpenedPosition.RootFsyncStop
    (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (stopped : IO.FS.Handle → EStateM IO.FS.Handle heap (Except IO.Error Unit)) where
  batch : List WAL.Write
  table : PackedTable
  guarded : heap
  poisoned : heap
  appended : heap
  staged : heap
  grouped : heap
  renamed : heap
  issued : heap
  reached : heap
  handle : IO.FS.Handle
  effective : Bool
  nonempty : request.rows ≠ []
  prepared : prepareBatch (state).writer.installed.table request.rows = some (batch, table)
  fits : (state).writer.installed.walBytes + WAL.frameSize * request.rows.length < UInt64.size
  checked : checkActiveSegmentWith dir (state).writer.installed lookup current.reached = .ok () guarded
  assigned : opened.set opened.phase .poisoned guarded = .ok () poisoned
  preface : (storage current.reached).Frames (state).crashPath (storage poisoned)
  wrote : append.run cache.active ((dir).file (.walSegment first)) (WAL.encodeBatch batch) poisoned = .ok () appended
  remembered : stage.run cache.pending stagePath
    (WAL.Boundary.encode ((state).writer.installed.walBytes + WAL.frameSize * request.rows.length).toUInt64)
    appended = .ok () staged
  synced : calls.group (dir).path cache.directory cache.active cache.pending
    #[(dir).file (.walSegment first), stagePath] staged = .ok () grouped
  groupEffects : calls.WalGroupEffects cache view append stage inodes observe inode buffered first
    ((state).writer.installed.walBytes + WAL.frameSize * request.rows.length)
    (state).writer.wal.active.bytes (WAL.encodeBatch batch) poisoned appended staged grouped
  moved : rename stagePath markerPath grouped = .ok () renamed
  renameEffect : ∀ marker, (observe grouped).visible stagePath = some marker →
    WalMarkerRenameEffect dir marker true (storage grouped) (storage renamed)
  loaded : calls.readDirectory cache.directory renamed = .ok (some handle) issued
  readFrame : WalPublicationPayloads.CacheReadFrame dir first (storage renamed) (storage issued)
  target : RawFsyncTarget view renamed issued handle
  root : (storage issued).files.names (dir).path =
    some ((view.descriptors issued).inode (view.handle issued handle).2.1.description)
  noResponse : stopped handle issued = .error handle reached
  effect : stopped handle issued = .error handle reached →
    (view.handle issued handle).2.1 ∈ (view.descriptors issued).slots →
    (storage issued).files.names (dir).path =
      some ((view.descriptors issued).inode (view.handle issued handle).2.1.description) →
    WalRootSyncEffect dir effective (storage issued) (storage reached)
  frames :
    let frame := fun before after =>
      (storage before).Frames (state).writeFramePath (storage after) ∧
      WalNamePresenceFrame dir 0 (current.current.history.length + request.rows.length)
        (storage before) (storage after)
    current.WriteCallbackFrames append stage calls cache request lookup rename frame (fun fromRename =>
      ∀ {atIssue atStop : heap} {directoryHandle : IO.FS.Handle},
        calls.readDirectory cache.directory fromRename = .ok (some directoryHandle) atIssue →
        RawFsyncTarget view fromRename atIssue directoryHandle →
        (storage atIssue).files.names (dir).path =
          some ((view.descriptors atIssue).inode (view.handle atIssue directoryHandle).2.1.description) →
        stopped directoryHandle atIssue = .error directoryHandle atStop →
        frame fromRename atIssue ∧ frame atIssue atStop)

/-- The reached file group, rename and cached root load establish the
publication payloads at the same unresolved fsync. An observed stop can
settle the new marker even when the write never reports a response. -/
theorem NativeOpenedPosition.stopsAtRootFsync
    (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (stopped : IO.FS.Handle → EStateM IO.FS.Handle heap (Except IO.Error Unit))
    (stop : current.RootFsyncStop calls cache view append stage inodes runs observe inode buffered
      request lookup rename stopped)
    (old : NativeReadyStorage state (storage current.reached)) :
    opened.table.UsesOpenWriteSchedules dir opened.files opened.phase ∧
    request.runUntilRootFsync dir cache lookup append stage calls rename stopped opened.phase opened.get opened.set
      current.reached = .error stop.handle stop.reached ∧
    WalPublicationPayloads.ReachedWrite state stop.batch request.rows (storage stop.reached) true
      (fun published => stop.effective = true → published = true) ∧
    ∀ {rebooted} (sample : RawWriteRebootEntry state view storage (fun h => (storage h).files.names)
        (fun h => (inodes h).visible) stop.reached rebooted), sample.DurableReset →
      current.WalWindowAt storage 0 (current.current.history.length + request.rows.length) →
      ∃ (target : Target) (plan : current.current.ready.SelectedWritePlan stop.batch target (view.files rebooted).image)
        (retained : List WAL.Write),
        current.current.SelectedWriteReboot view storage (fun h => (inodes h).visible) 0 request stop.batch stop.table target
          stop.reached rebooted ∧
        target.range.through = plan.history.length ∧
        (∀ {origin : NativeExecutionPosition} {events : List NativeExecutionEvent},
          origin.LedgerSuffix events current.current →
            origin.InterruptedWriteLedger current.current events request stop.batch retained plan.history) ∧
        ∀ {stream : Type} (opener : RawMarkedOpenInterpreter heap stream) namespaceView root,
          (state).writer.target.pair.manifest = none →
          opener.ReplaysWalBeforeCheckpointAtOpen view (state).session.directory (state).writer.wal.active.first
            storage (fun h => (inodes h).visible)
            rebooted namespaceView root plan.history := by
  obtain ⟨batch, table, guarded, poisoned, appended, staged, grouped, renamed, issued, reached, handle, effective,
    nonempty, prepared, fits, checked, assigned, preface, wrote, remembered, synced, groupEffects, moved, renameEffect,
    loaded, readFrame, target, root, noResponse, effect, frames⟩ := stop
  have valid := current.current.ready.readPrefix.refines.1
  have stored := current.stored.trans (congrArg some valid.phase)
  have loadedPhase := opened.phaseEffects.reads current.reached opened.phase _ stored
  have stopCommit :=
    calls.stopsAtRootFsync dir cache append stage rename stopped wrote remembered synced moved loaded noResponse
  have stopWrite := request.stopsDuringPublication dir lookup
    (fun installed bytes count => calls.commitUntilRootFsync dir cache append stage rename stopped
      installed.activeFirst count bytes) opened.phase opened.get opened.set nonempty prepared fits
    loadedPhase checked assigned stopCommit
  obtain ⟨payloads, grouped, keeper, oldMarker, newMarker⟩ :=
    calls.groupedWalPayloadsFromPublication cache view append stage inodes observe inode buffered
      (rows := request.rows) valid (old.frame preface) wrote remembered synced groupEffects
  have atRename := (renameEffect payloads.newMarker grouped.stagedNamed).selects grouped
  have atIssue := atRename.frameCacheRead readFrame
  have physical := (effect noResponse target.live root).selects atIssue
  have firstExact : first = (state).writer.wal.active.first := valid.retained.resumed.keeper.trans valid.retained.active
  rw [firstExact] at physical
  have published : WalPublicationPayloads.ReachedWrite state batch request.rows (storage reached) true
      (fun published => effective = true → published = true) := by
    refine ⟨payloads, keeper, oldMarker, newMarker, physical.1, ?_⟩
    intro names included
    obtain ⟨published, allowed, selected⟩ := physical.2 names included
    exact ⟨published, (fun settled => by simpa only [settled, ↓reduceIte] using allowed), selected⟩
  refine ⟨current.uses.writeSchedules, stopWrite, published, ?_⟩
  intro rebooted sample reset window
  let frame := fun before after =>
    (storage before).Frames (state).writeFramePath (storage after) ∧
    WalNamePresenceFrame dir 0 (current.current.history.length + request.rows.length)
      (storage before) (storage after)
  have trans {before middle after : heap} (earlier : frame before middle) (later : frame middle after) :
      frame before after := ⟨earlier.1.trans later.1, earlier.2.trans later.2⟩
  obtain ⟨renameFrame, finish⟩ :=
    frames.toPublicationCallbackFrames.throughRename trans prepared checked assigned wrote remembered synced moved
  obtain ⟨cacheFrame, stopFrame⟩ := finish loaded target root noResponse
  have beforeWrite := trans (frames.guard checked) (frames.poison checked assigned)
  have throughStop := trans (trans beforeWrite renameFrame) (trans cacheFrame stopFrame)
  obtain ⟨target, handoff⟩ := current.selectsDurableReachedWrite view storage prepared fits old throughStop.1 published
    (fun h => (inodes h).visible) sample reset throughStop.2 window
  obtain ⟨plan, retained, cutoff, ledger, opens⟩ := handoff.interruptedPlan
  exact ⟨target, plan, retained, handoff, cutoff, @ledger, @opens⟩

end PhysicalStop

/-- The ordinary commit schedule, with the actual keeper write able to
stop before it returns to the append helper. -/
noncomputable def RawWalAppendCalls.commitUntilWrite {heap stop : Type} (appender : RawWalAppendCalls heap)
    (directory : DiskDirectory) {files : DiskTable.OpenSyncFiles}
    (cache : OpenSyncCacheRefs files directory.path)
    (write : IO.FS.Handle → ByteArray → EStateM stop heap (Except IO.Error Unit))
    (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (installed : Installed) (bytes : ByteArray) (count : Nat) : EStateM stop heap (Except IO.Error Unit) :=
  (commitBytesAt directory installed.activeFirst bytes count
    (fun path payload => appender.runUntilWrite cache.active write path payload)
    (fun path payload => asPublicationReturn (stager.run cache.pending path payload))
    (fun paths => asPublicationReturn (syncer.group directory.path cache.directory cache.active cache.pending paths))
    (fun source target => asPublicationReturn (rename source target))).run

section AppendStop

variable {heap stop : Type} {opened : NativeOpenedHandle heap}
  (current : NativeOpenedPosition opened)
  (view : OpenCloseHeapView heap FileImage)
  (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
  (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
  (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
  (request : WriteRequest)

local notation "state" => current.current.ready.state
local notation "dir" => current.current.ready.state.session.directory
local notation "installed" => current.current.ready.state.writer.installed
local notation "keeperPath" =>
  DiskDirectory.file dir (DiskFile.walSegment current.current.ready.state.writer.wal.active.first)
local notation "names" => fun h => CheckpointSurvivingFiles.names (CheckpointStorageObservation.files (storage h))
local notation "horizon" => current.current.history.length

/-- One stopped keeper write goes through the original phase and cache.
It never reaches marker staging. A joint crash sample selects the old
history even if the named keeper acquired extra bytes. -/
theorem NativeOpenedPosition.stopsDuringWalAppend
    (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (write : IO.FS.Handle → ByteArray → EStateM stop heap (Except IO.Error Unit))
    {batch : List WAL.Write} {table : PackedTable} {guarded poisoned cut : heap} {tag : stop}
    (nonempty : request.rows ≠ [])
    (prepared : prepareBatch (installed).table request.rows = some (batch, table))
    (fits : (installed).walBytes + WAL.frameSize * request.rows.length < UInt64.size)
    (checked : checkActiveSegmentWith dir installed lookup current.reached = .ok () guarded)
    (assigned : opened.set opened.phase .poisoned guarded = .ok () poisoned)
    (stopped : appender.runUntilWrite cache.active write ((dir).file (.walSegment (installed).activeFirst))
      (WAL.encodeBatch batch) poisoned = .error tag cut) :
    opened.table.UsesOpenWriteSchedules dir opened.files opened.phase ∧
    request.runUntilPublicationStop dir lookup
      (appender.commitUntilWrite dir cache write stager syncer rename) opened.phase opened.get opened.set
      current.reached = .error tag cut ∧
    let keeps (before after : heap) := (storage before).Frames (state).crashPath (storage after) ∧
      WalNamePresenceFrame dir 0 horizon (storage before) (storage after)
    ∀ (_initial : NativeReadyStorage state (storage current.reached))
      (_guardFrame : keeps current.reached guarded) (_poisonFrame : keeps guarded poisoned)
      (_readFrame : ∀ {cached loaded}, appender.getActive cache.active poisoned = .ok cached loaded →
        keeps poisoned loaded)
      (_selects : ∀ {cached loaded handle issued}, appender.getActive cache.active poisoned = .ok cached loaded →
        selectAppendHandle cached appender.openAppend ((dir).file (.walSegment (installed).activeFirst)) loaded =
          .ok handle issued →
        keeps loaded issued ∧ (view.handle issued handle).2.1 ∈ (view.descriptors issued).slots ∧
          names issued ((dir).file (.walSegment (installed).activeFirst)) =
            some ((view.descriptors issued).inode (view.handle issued handle).2.1.description))
      (_writeEffect : ∀ {handle issued}, write handle (WAL.encodeBatch batch) issued = .error tag cut →
        (view.handle issued handle).2.1 ∈ (view.descriptors issued).slots →
        names issued keeperPath = some ((view.descriptors issued).inode (view.handle issued handle).2.1.description) →
        (state).BeforeMarkerWriteFrame ((view.descriptors issued).inode (view.handle issued handle).2.1.description)
          (storage issued) (storage cut) ∧ WalNamePresenceFrame dir 0 horizon (storage issued) (storage cut)),
      ∀ {rebooted : heap} (sample : RawWriteRebootEntry state view storage names visible cut rebooted),
        BatchRetryTarget (state).writer.history batch (state).writer.wal.active.first (state).writer.target ∧
        RawOpenRetryTrace.SelectedEntry view state (state).writer.target names visible rebooted ∧
        (sample.DurableReset → current.WalWindowAt storage 0 horizon →
        ∃ plan : current.current.ready.SelectedWritePlan batch (state).writer.target (view.files rebooted).image,
          current.current.SelectedWriteReboot view storage visible 0 request batch table (state).writer.target cut rebooted ∧
          plan.history = current.current.history ∧
          (∀ {origin : NativeExecutionPosition} {events : List NativeExecutionEvent},
            origin.LedgerSuffix events current.current →
              origin.InterruptedWriteLedger current.current events request batch [] plan.history) ∧
          ∀ {stream : Type} (opener : RawMarkedOpenInterpreter heap stream) namespaceView root,
            (state).writer.target.pair.manifest = none →
            opener.ReplaysWalBeforeCheckpointAtOpen view dir (state).writer.wal.active.first
              storage visible rebooted namespaceView root plan.history) := by
  have valid := current.current.ready.readPrefix.refines.1
  have loaded := opened.phaseEffects.reads current.reached opened.phase _
    (current.stored.trans (congrArg some valid.phase))
  let publish := appender.commitUntilWrite dir cache write stager syncer rename
  have commit : publish installed (WAL.encodeBatch batch) ((installed).walBytes + WAL.frameSize * request.rows.length)
      poisoned = .error tag cut := by
    simp only [publish, RawWalAppendCalls.commitUntilWrite, commitBytesAt_fileEffects, WAL.Boundary.commit,
      ExceptT.run, Bind.bind, ExceptT.bind, ExceptT.mk, EStateM.bind, stopped]
  refine ⟨current.uses.writeSchedules,
    request.stopsDuringPublication dir lookup publish opened.phase opened.get opened.set nonempty prepared fits loaded
      checked assigned commit, ?_⟩
  intro keeps initial guardFrame poisonFrame readFrame selects writeEffect rebooted sample
  obtain ⟨_, _, handle, issued, read, selected, noResponse⟩ := appender.reachesStoppedWrite stopped
  have compose {before middle after : heap} (first : keeps before middle) (last : keeps middle after) :
      keeps before after := ⟨first.1.trans last.1, first.2.trans last.2⟩
  obtain ⟨selectionFrame, live, bound⟩ := selects read selected
  have sameFirst : (installed).activeFirst = (state).writer.wal.active.first :=
    valid.retained.resumed.keeper.trans valid.retained.active
  rw [sameFirst] at bound
  have beforeWrite := compose (compose guardFrame poisonFrame) (compose (readFrame read) selectionFrame)
  have atEntry : names current.reached keeperPath =
      some ((view.descriptors issued).inode (view.handle issued handle).2.1.description) :=
    ((beforeWrite.1.visible _ (NativeReadyState.crashPath_iff_write.mpr (.inr (.inl rfl)))).1).symm.trans bound
  obtain ⟨effect, namesEffect⟩ := writeEffect noResponse live bound
  have reached := (NativeReadyState.BeforeMarkerWriteFrame.ofFileFrame beforeWrite.1 atEntry).trans effect
  obtain ⟨admitted, chosen, vacant, _⟩ :=
    reached.selectsPriorAtReboot («storage» := storage) (entry := current.reached) (cut := cut)
      valid batch initial atEntry sample
  refine ⟨admitted, chosen, ?_⟩
  intro reset window
  have writerHistory := current.current.ready.readPrefix.refines.2.1
  have cutoff : (state).writer.target.range.through = current.current.history.length :=
    valid.retained.resumed.through.trans (congrArg List.length writerHistory)
  have sampledWindow := sample.walNamespace (beforeWrite.2.trans namesEffect) window.2
  have recovery := sample.startsRecoveryObservations reset chosen (cutoff.symm ▸ sampledWindow)
  let handoff : current.current.SelectedWriteReboot view storage visible 0 request batch table
      (state).writer.target cut rebooted :=
    ⟨prepared, fits, fun _ _ => Nat.zero_le _, vacant, sample, admitted, chosen, recovery⟩
  obtain ⟨plan, opens⟩ := handoff.sampledPlan
  have sameLength : plan.history.length = current.current.history.length :=
    plan.layout.through.symm.trans ((congrArg (fun target : Target => target.range.through) plan.targetEq).trans cutoff)
  have oldHistory : plan.history = current.current.history := by
    rcases plan.allowed with prior | complete
    · exact prior
    · have count := congrArg List.length complete
      rw [List.length_append] at count
      have empty : batch = [] := List.length_eq_zero_iff.mp (by omega)
      simpa only [empty, List.append_nil] using complete
  refine ⟨plan, handoff, oldHistory, ?_, @opens⟩
  intro origin events prior
  refine ⟨⟨table, prepared⟩, .inl rfl, ?_, ?_, ?_⟩
  · simpa only [List.append_nil, ← prior.history] using oldHistory
  · simpa only [← prior.submissions, ← prior.reads] using plan.pending
  · simpa only [← prior.reads] using plan.bounded

end AppendStop

end Alvoki.Storage.DiskSession
