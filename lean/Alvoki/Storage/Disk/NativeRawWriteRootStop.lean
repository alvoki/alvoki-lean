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

private theorem asPublicationReturn_bind {heap stop error α β : Type}
    (action : EStateM error heap α) (next : α → EStateM error heap β) :
    (asPublicationReturn (stop := stop) action >>= fun value => asPublicationReturn (next value)) =
      asPublicationReturn (action >>= next) := by
  funext before
  cases returned : action before <;>
    simp [asPublicationReturn, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, EStateM.bind,
      Pure.pure, EStateM.pure, returned]

private theorem asPublicationReturn_pure {heap stop error α : Type} (value : α) :
    asPublicationReturn (stop := stop) (pure value : EStateM error heap α) =
      (pure value : PublicationStopM heap stop error α) := rfl

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

local macro "simp_publication_stop" " [" facts:Lean.Parser.Tactic.simpArg,* "]"
    loc:(Lean.Parser.Tactic.location)? : tactic => do
  let facts : Lean.Syntax.TSepArray
      [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma] "," :=
    ⟨facts.elemsAndSeps⟩
  `(tactic| simp [classify, asPublicationReturn, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
    ExceptT.run, EStateM.bind, Pure.pure, ExceptT.pure, EStateM.pure, liftExcept, Except.pure,
    Except.mapError, throw, throwThe, MonadExceptOf.throw, $facts,*] $[$loc]?)

private theorem WriteRequest.publicationAfterPreparation {heap stop : Type}
    (request : WriteRequest) (directory : DiskDirectory)
    (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (publish : Installed → ByteArray → Nat → EStateM stop heap (Except IO.Error Unit))
    (phase : IO.Ref (Phase Installed))
    (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit)
    {installed : Installed} {batch : List WAL.Write} {table : PackedTable}
    {entry : heap}
    (nonempty : request.rows ≠ [])
    (prepared : prepareBatch installed.table request.rows = some (batch, table))
    (fits : installed.walBytes + WAL.frameSize * request.rows.length < UInt64.size)
    (loaded : get phase entry = .ok (.ready installed) entry) :
    let count := installed.walBytes + WAL.frameSize * request.rows.length
    request.runUntilPublicationStop directory lookup publish phase get set entry =
      (do
        classify .rejected (asPublicationReturn (checkActiveSegmentWith directory installed lookup))
        publishPreparedWrite { installed with table, walBytes := count } table.committed
          (fun next => classify .rejected (asPublicationReturn (set phase next)))
          (classify .commitUnknown (publish installed (WAL.encodeBatch batch) count))
        : PublicationStopM heap stop DiskWriteError UInt64).run entry := by
  cases request with
  | single key value =>
    rw [WriteRequest.rows, prepareBatch_singleton] at prepared
    cases written : installed.table.write key value with
    | none => simp [prepareWrite, written] at prepared
    | some next =>
      simp only [prepareWrite, written, Option.map_some, Option.some.injEq, Prod.mk.injEq] at prepared
      obtain ⟨rfl, rfl⟩ := prepared
      simp only [WriteRequest.rows, List.length_singleton, Nat.mul_one] at fits
      simp_publication_stop [runUntilPublicationStop, runWithPublication, withPreparedSingleWrite, prepareWrite,
        WriteRequest.requireWritePreparation, loaded, written, fits, Phase.installed, WriteRequest.rows,
        WAL.encodeBatch_singleton, publishPreparedWrite, publishPrepared]
  | batch rows =>
    simp only [WriteRequest.rows] at prepared fits ⊢
    have present : rows.isEmpty = false := List.isEmpty_eq_false_iff.mpr nonempty
    simp_publication_stop [runUntilPublicationStop, runWithPublication, writeBatchSchedule,
      WriteRequest.requireWritePreparation, loaded, present, fits, prepared, Phase.installed,
      publishPreparedWrite, publishPrepared]

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
  rw [request.publicationAfterPreparation directory lookup publish phase get set nonempty prepared fits loaded]
  simp_publication_stop [publishPreparedWrite, publishPrepared, guard, assigned, commit]

/-- An outer stop exposes the prepared batch and its actual reached guard,
poison store and publication. An ordinary I/O failure cannot reach it. -/
theorem WriteRequest.reachesPublicationStop {heap stop : Type} (request : WriteRequest) (directory : DiskDirectory)
    (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (publish : Installed → ByteArray → Nat → EStateM stop heap (Except IO.Error Unit))
    (phase : IO.Ref (Phase Installed))
    (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit)
    {installed : Installed}
    {entry reached : heap} {tag : stop}
    (loaded : get phase entry = .ok (.ready installed) entry)
    (stopped : request.runUntilPublicationStop directory lookup publish phase get set entry = .error tag reached) :
    ∃ (batch : List WAL.Write) (table : PackedTable) (guarded poisoned : heap),
      request.rows ≠ [] ∧ prepareBatch installed.table request.rows = some (batch, table) ∧
      installed.walBytes + WAL.frameSize * request.rows.length < UInt64.size ∧
      checkActiveSegmentWith directory installed lookup entry = .ok () guarded ∧
      set phase .poisoned guarded = .ok () poisoned ∧
      publish installed (WAL.encodeBatch batch) (installed.walBytes + WAL.frameSize * request.rows.length)
        poisoned = .error tag reached := by
  have preparedRequest : ∃ batch table, request.rows ≠ [] ∧
      prepareBatch installed.table request.rows = some (batch, table) ∧
      installed.walBytes + WAL.frameSize * request.rows.length < UInt64.size := by
    cases request with
    | single key value =>
      cases prepared : prepareWrite installed.table key value with
      | none =>
        simp_publication_stop [runUntilPublicationStop, runWithPublication, withPreparedSingleWrite,
          WriteRequest.requireWritePreparation, loaded, prepared, Phase.installed] at stopped
      | some plan =>
        obtain ⟨event, table⟩ := plan
        by_cases fits : installed.walBytes + WAL.frameSize < UInt64.size
        · exact ⟨[event], table, by simp [WriteRequest.rows],
            by simp [WriteRequest.rows, prepareBatch_singleton, prepared],
            by simpa only [WriteRequest.rows, List.length_singleton, Nat.mul_one] using fits⟩
        · simp_publication_stop [runUntilPublicationStop, runWithPublication, withPreparedSingleWrite,
          WriteRequest.requireWritePreparation, loaded, prepared, fits, Phase.installed] at stopped
    | batch rows =>
      by_cases empty : rows = []
      · subst rows
        simp_publication_stop [runUntilPublicationStop, runWithPublication, writeBatchSchedule, loaded,
          Phase.installed] at stopped
      · have present := List.isEmpty_eq_false_iff.mpr empty
        by_cases fits : installed.walBytes + WAL.frameSize * rows.length < UInt64.size
        · cases prepared : prepareBatch installed.table rows with
          | none =>
            simp_publication_stop [runUntilPublicationStop, runWithPublication, writeBatchSchedule,
              WriteRequest.requireWritePreparation, loaded, present, fits, prepared, Phase.installed] at stopped
          | some plan =>
            exact ⟨plan.1, plan.2, empty, by simpa only [WriteRequest.rows] using prepared, fits⟩
        · simp_publication_stop [runUntilPublicationStop, runWithPublication, writeBatchSchedule, loaded, present,
          fits, Phase.installed] at stopped
  obtain ⟨batch, table, nonempty, prepared, fits⟩ := preparedRequest
  rw [request.publicationAfterPreparation directory lookup publish phase get set nonempty prepared fits loaded] at stopped
  cases checked : checkActiveSegmentWith directory installed lookup entry with
  | error cause failed =>
    simp_publication_stop [checked] at stopped
  | ok value guarded =>
    cases value
    cases assigned : set phase .poisoned guarded with
    | error cause failed =>
      simp_publication_stop [checked, assigned, publishPreparedWrite, publishPrepared] at stopped
    | ok value poisoned =>
      cases value
      let count := installed.walBytes + WAL.frameSize * request.rows.length
      cases commit : publish installed (WAL.encodeBatch batch) count poisoned with
      | error actual after =>
        simp_publication_stop [count, checked, assigned, commit, publishPreparedWrite, publishPrepared] at stopped
        obtain ⟨rfl, rfl⟩ := stopped
        exact ⟨batch, table, guarded, poisoned, nonempty, prepared, fits, rfl, assigned, commit⟩
      | ok result settled =>
        cases result with
        | error cause =>
          simp_publication_stop [count, checked, assigned, commit, publishPreparedWrite, publishPrepared] at stopped
        | ok value =>
          cases value
          cases restored : set phase (.ready { installed with table, walBytes := count }) settled <;>
            simp_publication_stop [count, checked, assigned, commit, restored, publishPreparedWrite,
              publishPrepared] at stopped

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

/-- The marker suffix is lifted from ordinary effects. An outer stop in
the whole commit can therefore come only from the original append. -/
theorem RawWalAppendCalls.reachesStoppedAppend {heap stop : Type} (appender : RawWalAppendCalls heap)
    (directory : DiskDirectory) {files : DiskTable.OpenSyncFiles}
    (cache : OpenSyncCacheRefs files directory.path)
    (write : IO.FS.Handle → ByteArray → EStateM stop heap (Except IO.Error Unit))
    (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {installed : Installed} {bytes : ByteArray} {count : Nat} {entry reached : heap} {tag : stop}
    (stopped : appender.commitUntilWrite directory cache write stager syncer rename installed bytes count entry =
      .error tag reached) :
    appender.runUntilWrite cache.active write (directory.file (.walSegment installed.activeFirst)) bytes entry =
      .error tag reached := by
  simp only [commitUntilWrite, commitBytesAt_fileEffects, WAL.Boundary.commit,
    ← asPublicationReturn_pure, asPublicationReturn_bind] at stopped
  cases append : appender.runUntilWrite cache.active write
      (directory.file (.walSegment installed.activeFirst)) bytes entry with
  | error actual cut =>
    simp_publication_stop [append] at stopped ⊢
    exact stopped
  | ok result appended =>
    cases result with
    | error cause => simp_publication_stop [append] at stopped
    | ok value =>
      simp_publication_stop [append] at stopped
      split at stopped <;> contradiction

section AppendStop

variable {heap stop : Type} {opened : NativeOpenedHandle heap}
  (current : NativeOpenedPosition opened)
  (view : OpenCloseHeapView heap FileImage)
  (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
  (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
  (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
  (request : WriteRequest) {firstOffset : Nat}

local notation "state" => current.current.ready.state
local notation "dir" => current.current.ready.state.session.directory
local notation "installed" => current.current.ready.state.writer.installed
local notation "keeperPath" =>
  DiskDirectory.file dir (DiskFile.walSegment current.current.ready.state.writer.wal.active.first)
local notation "names" => fun h => CheckpointSurvivingFiles.names (CheckpointStorageObservation.files (storage h))
local notation "horizon" => current.current.history.length
local notation "keeps" => fun first before after =>
  CheckpointStorageObservation.Frames (NativeReadyState.crashPath state) (storage before) (storage after) ∧
  WalNamePresenceFrame dir first horizon (storage before) (storage after)

/-- Local effects up to the issued append, on the heap reached by the
guard and the poison store. The stopped write may extend the bound keeper. -/
structure NativeOpenedPosition.AppendStopFrames
    (write : IO.FS.Handle → ByteArray → EStateM stop heap (Except IO.Error Unit))
    (firstOffset : Nat) (batch : List WAL.Write) (guarded poisoned : heap) (tag : stop) (cut : heap) : Prop where
  guard : keeps firstOffset current.reached guarded
  poison : keeps firstOffset guarded poisoned
  read : ∀ {cached loaded}, appender.getActive cache.active poisoned = .ok cached loaded → keeps firstOffset poisoned loaded
  select : ∀ {cached loaded handle issued}, appender.getActive cache.active poisoned = .ok cached loaded →
    selectAppendHandle cached appender.openAppend ((dir).file (.walSegment (installed).activeFirst)) loaded =
      .ok handle issued →
    keeps firstOffset loaded issued ∧ (view.handle issued handle).2.1 ∈ (view.descriptors issued).slots ∧
      names issued ((dir).file (.walSegment (installed).activeFirst)) =
        some ((view.descriptors issued).inode (view.handle issued handle).2.1.description)
  effect : ∀ {handle issued}, write handle (WAL.encodeBatch batch) issued = .error tag cut →
    (view.handle issued handle).2.1 ∈ (view.descriptors issued).slots →
    names issued keeperPath = some ((view.descriptors issued).inode (view.handle issued handle).2.1.description) →
    (state).BeforeMarkerWriteFrame ((view.descriptors issued).inode (view.handle issued handle).2.1.description)
      (storage issued) (storage cut) ∧ WalNamePresenceFrame dir firstOffset horizon (storage issued) (storage cut)

/-- One stopped keeper write goes through the original phase and cache.
It never reaches marker staging. A joint crash sample selects the old
history even if the named keeper acquired extra bytes. -/
theorem NativeOpenedPosition.stopsDuringWalAppend
    (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (write : IO.FS.Handle → ByteArray → EStateM stop heap (Except IO.Error Unit))
    {cut : heap} {tag : stop}
    (stopped : request.runUntilPublicationStop dir lookup
      (appender.commitUntilWrite dir cache write stager syncer rename) opened.phase opened.get opened.set
      current.reached = .error tag cut) :
    opened.table.UsesOpenWriteSchedules dir opened.files opened.phase ∧
    ∃ (batch : List WAL.Write) (table : PackedTable) (guarded poisoned : heap),
    request.rows ≠ [] ∧
    prepareBatch (installed).table request.rows = some (batch, table) ∧
    (installed).walBytes + WAL.frameSize * request.rows.length < UInt64.size ∧
    checkActiveSegmentWith dir installed lookup current.reached = .ok () guarded ∧
    opened.set opened.phase .poisoned guarded = .ok () poisoned ∧
    appender.runUntilWrite cache.active write ((dir).file (.walSegment (installed).activeFirst))
      (WAL.encodeBatch batch) poisoned = .error tag cut ∧
    ∀ (_initial : NativeReadyStorage state (storage current.reached))
      (_frames : current.AppendStopFrames view cache appender storage write firstOffset batch guarded poisoned tag cut),
      ∀ {rebooted : heap} (sample : RawWriteRebootEntry state view storage names visible cut rebooted),
        BatchRetryTarget (state).writer.history batch (state).writer.wal.active.first (state).writer.target ∧
        RawOpenRetryTrace.SelectedEntry view state (state).writer.target names visible rebooted ∧
        (current.WalWindowAt storage firstOffset horizon →
        ∃ plan : current.current.ready.SelectedWritePlan batch (state).writer.target (view.files rebooted).image,
          (sample.DurableReset →
            current.current.SelectedWriteReboot view storage visible firstOffset request batch table (state).writer.target cut rebooted) ∧
          plan.history = current.current.history ∧
          ∀ {origin : NativeExecutionPosition} {events : List NativeExecutionEvent},
            origin.LedgerSuffix events current.current →
            origin.InterruptedWriteLedger current.current events request batch [] plan.history ∧
            ∀ {stream : Type} (opener : RawMarkedOpenInterpreter heap stream) namespaceView root,
              opener.ReadsClientHistoryAtOpen view dir storage visible rebooted namespaceView root
                ((origin.submissions ++ events.flatMap NativeExecutionEvent.submissions) ++ [.uncertainBatch batch])
                (origin.ready.reads ++ events.flatMap NativeExecutionEvent.reads) plan.history) := by
  have valid := current.current.ready.readPrefix.refines.1
  have loaded := opened.phaseEffects.reads current.reached opened.phase _
    (current.stored.trans (congrArg some valid.phase))
  obtain ⟨batch, table, guarded, poisoned, nonempty, prepared, fits, checked, assigned, commit⟩ :=
    request.reachesPublicationStop dir lookup (appender.commitUntilWrite dir cache write stager syncer rename)
      opened.phase opened.get opened.set loaded stopped
  have append := appender.reachesStoppedAppend dir cache write stager syncer rename commit
  refine ⟨current.uses.writeSchedules, batch, table, guarded, poisoned,
    nonempty, prepared, fits, checked, assigned, append, ?_⟩
  intro initial frames rebooted sample
  obtain ⟨_, _, handle, issued, read, selected, noResponse⟩ := appender.reachesStoppedWrite append
  have compose {before middle after : heap} (first : keeps firstOffset before middle) (last : keeps firstOffset middle after) :
      keeps firstOffset before after := ⟨first.1.trans last.1, first.2.trans last.2⟩
  obtain ⟨selectionFrame, live, bound⟩ := frames.select read selected
  have sameFirst : (installed).activeFirst = (state).writer.wal.active.first :=
    valid.retained.resumed.keeper.trans valid.retained.active
  rw [sameFirst] at bound
  have beforeWrite := compose (compose frames.guard frames.poison) (compose (frames.read read) selectionFrame)
  have atEntry : names current.reached keeperPath =
      some ((view.descriptors issued).inode (view.handle issued handle).2.1.description) :=
    ((beforeWrite.1.visible _ (NativeReadyState.crashPath_iff_write.mpr (.inr (.inl rfl)))).1).symm.trans bound
  obtain ⟨effect, namesEffect⟩ := frames.effect noResponse live bound
  have reached := (NativeReadyState.BeforeMarkerWriteFrame.ofFileFrame beforeWrite.1 atEntry).trans effect
  obtain ⟨admitted, chosen, vacant, _⟩ :=
    reached.selectsPriorAtReboot («storage» := storage) (entry := current.reached) (cut := cut)
      valid batch initial atEntry sample
  refine ⟨admitted, chosen, ?_⟩
  intro window
  have writerHistory := current.current.ready.readPrefix.refines.2.1
  have cutoff : (state).writer.target.range.through = current.current.history.length :=
    valid.retained.resumed.through.trans (congrArg List.length writerHistory)
  have sampledWindow := cutoff.symm ▸ sample.walNamespace (beforeWrite.2.trans namesEffect) window.2
  obtain ⟨plan⟩ := current.current.ready.preparesSelectedWrite prepared fits admitted chosen.valid chosen.manifest
  have oldHistory := plan.oldHistory
  have physical := plan.visibleWal names visible window.1 sampledWindow
    chosen.protectedFiles chosen.keeper
  refine ⟨plan, ?_, oldHistory, ?_⟩
  · intro reset
    exact ⟨prepared, fits, window.1, vacant, sample, admitted, chosen,
      sample.startsRecoveryObservations reset chosen sampledWindow⟩
  · intro origin events prior
    have ledger : origin.InterruptedWriteLedger current.current events request batch [] plan.history := by
      refine ⟨⟨table, prepared⟩, .inl rfl, ?_, ?_, ?_⟩
      · simpa only [List.append_nil, ← prior.history] using oldHistory
      · simpa only [← prior.submissions, ← prior.reads] using plan.pending
      · simpa only [← prior.reads] using plan.bounded
    exact ⟨ledger, fun opener namespaceView root =>
      plan.readsClientHistoryAtOpen (source := opener) storage visible namespaceView root chosen physical ledger.pending⟩

end AppendStop

section AppendReopen

variable {heap : Type} {opened : NativeOpenedHandle heap}
  (last : NativeOpenedPosition opened) (view : OpenCloseHeapView heap FileImage)
  (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
  (storage : heap → CheckpointStorageObservation)

local notation "ready" => last.current.ready
local notation "state" => last.current.ready.state
local notation "dir" => last.current.ready.state.session.directory
local notation "installed" => last.current.ready.state.writer.installed
local notation "target" => last.current.ready.state.writer.target
local notation "names" => fun h => CheckpointSurvivingFiles.names (CheckpointStorageObservation.files (storage h))
local notation "visible" => fun h => WalInodeImage.visible (inodes h)
local notation "prepares" => fun request batch table => prepareBatch (Installed.table installed) (WriteRequest.rows request) =
  some (batch, table)

/-- The next public write may stop at its keeper append. Its local
effects, joint reboot, and later calls of the marked opener determine the
exact ready return and its continuation. -/
abbrev NativeOpenedPosition.ContinuesAfterInterruptedAppend
    (cache : OpenSyncCacheRefs opened.files (dir).path)
    (origin : NativeExecutionPosition) (events : List NativeExecutionEvent) (firstOffset : Nat) : Prop :=
    ∀ {stream stop : Type} (request : WriteRequest)
    (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
    (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (write : IO.FS.Handle → ByteArray → EStateM stop heap (Except IO.Error Unit))
    {cut rebooted : heap} {tag : stop}
    (_stopped : request.runUntilPublicationStop dir lookup
      (appender.commitUntilWrite dir cache write stager syncer rename) opened.phase opened.get opened.set
      last.reached = .error tag cut)
    (_frames : ∀ {batch preparedTable guarded poisoned}, prepares request batch preparedTable →
      checkActiveSegmentWith dir installed lookup last.reached = .ok () guarded →
      opened.set opened.phase .poisoned guarded = .ok () poisoned →
      appender.runUntilWrite cache.active write ((dir).file (.walSegment (installed).activeFirst))
        (WAL.encodeBatch batch) poisoned = .error tag cut →
      last.AppendStopFrames view cache appender storage write firstOffset batch guarded poisoned tag cut)
    (sample : RawWriteRebootEntry state view storage names visible cut rebooted) (_reset : sample.DurableReset)
    {source : RawMarkedOpenInterpreter heap stream}
    {returns : List (FilePath × IO.Error)} {reached : heap} {attempts : source.FailedCalls rebooted returns reached}
    (_retryEffects : RawOpenRetryTrace.SelectedEffects view source rebooted target
      (fun h => ⟨names h, fun inode => [visible h inode]⟩) (state).selectedRetryPath
      (RawOpenRetryTrace.RecoveryObservations view state target storage visible firstOffset (target).range.through) attempts)
    {input : FilePath} (_admission : source.AlignedAdmissionEffects view state input reached storage visible)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (_rootBinding : names reached (dir).path = some (namespaceView.modelObject root))
    (_openEffects : ∀ {batch preparedTable}, prepares request batch preparedTable →
      ∀ (cache : HeldOpenCache heap) (plan : (ready).SelectedWritePlan batch target (view.files reached).image),
      LiteralOpenAuthority view dir cache cache.ready →
      namespaceView.modelObject root = cache.captured.inode cache.rootSlot.description →
      source.LiteralOpenEffects cache namespaceView root plan storage visible)
    (_alignedEffects : ∀ {batch preparedTable}, prepares request batch preparedTable →
      ∀ (cache : HeldOpenCache heap) (plan : (ready).SelectedWritePlan batch target (view.files reached).image),
      LiteralOpenAuthority view dir cache cache.ready →
      namespaceView.modelObject root = cache.captured.inode cache.rootSlot.description →
      plan.layout.tail.size = 0 → source.LiteralAlignedRepairEffects cache plan storage visible)
    (_replacementEffects : ∀ {batch preparedTable}, prepares request batch preparedTable →
      ∀ (cache : HeldOpenCache heap) (plan : (ready).SelectedWritePlan batch target (view.files reached).image),
      LiteralOpenAuthority view dir cache cache.ready →
      namespaceView.modelObject root = cache.captured.inode cache.rootSlot.description →
      0 < plan.layout.tail.size → source.LiteralKeeperReplacementEffects cache plan storage visible)
    (_phaseIdentity : IO.Ref (Phase Installed) → Nat) (_tokenIdentity : IO.Ref Unit → Nat)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (_phase : OpenPhaseCellEffects view.phase get set)
    (_ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)
    {returnedAt : heap} {table : DiskTable}
    (_returned : source.openTable input reached = .ok table returnedAt),
    opened.table.UsesOpenWriteSchedules dir opened.files opened.phase ∧
    ∃ batch preparedTable, prepares request batch preparedTable ∧
    (∃ poisoned, appender.runUntilWrite cache.active write ((dir).file (.walSegment (installed).activeFirst))
      (WAL.encodeBatch batch) poisoned = .error tag cut) ∧
    ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle)
      (refs : OpenSyncCacheRefs handle.files start.current.ready.state.session.directory.path),
      table = handle.table ∧ start.reached = returnedAt ∧
      start.current.history = last.current.history ∧
      origin.LedgerSuffix (events ++ [.interruptedAppendCrashRecovered request input batch]) start.current ∧
      start.WriteStorageEntry view refs (storage start.reached) (visible start.reached) ∧
      start.ContinuesReadyCalls refs view inodes runs storage origin
        (events ++ [.interruptedAppendCrashRecovered request input batch]) firstOffset

variable {view inodes storage}

/-- Derive the joint reboot's old-marker handoff at the actual stop and
carry it through the reported failed opens to the observed ready return. -/
theorem NativeOpenedPosition.opensReadyAfterInterruptedAppend
    (cache : OpenSyncCacheRefs opened.files (dir).path)
    (initial : NativeReadyStorage state (storage last.reached))
    {firstOffset : Nat} (walWindow : last.WalWindowAt storage firstOffset last.current.history.length)
    {origin : NativeExecutionPosition} {events : List NativeExecutionEvent}
    (prior : origin.LedgerSuffix events last.current) :
    last.ContinuesAfterInterruptedAppend view inodes runs storage cache origin events firstOffset := by
  intro stream stop request appender stager syncer lookup rename write cut rebooted tag stopped frames sample reset
    source returns reached attempts retryEffects input admission namespaceView root rootBinding openEffects alignedEffects
    replacementEffects phaseIdentity tokenIdentity get set phase ptrEq returnedAt table returned
  obtain ⟨schedules, batch, preparedTable, _, poisoned, _, prepared, _, checked, assigned, append, reboot⟩ :=
    last.stopsDuringWalAppend (firstOffset := firstOffset) view cache appender stager syncer storage visible
      request lookup rename write stopped
  obtain ⟨_, _, recovery⟩ := reboot initial (frames prepared checked assigned append) sample
  obtain ⟨_, choose, _, _⟩ := recovery walWindow
  have handoff := choose reset
  obtain ⟨plan, handle, start, refs, opened, history, submissions, reads, _, writeEntry, pins, _, _, _, window⟩ :=
    (ready).opensLiteralRepairedAfterWriteRetries storage visible handoff.prepared handoff.fits
      handoff.admitted handoff.covers handoff.selected handoff.recovery retryEffects admission namespaceView root rootBinding
      (openEffects prepared) (alignedEffects prepared) (replacementEffects prepared) phaseIdentity tokenIdentity phase ptrEq returned
  have old := history.trans plan.oldHistory
  have recovered : last.current.LedgerSuffix [.interruptedAppendCrashRecovered request input batch] start.current := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [NativeExecutionEvent.writes] using old
    · simpa [NativeExecutionEvent.submissions] using submissions
    · simpa [NativeExecutionEvent.reads] using reads
    · simp [NativeExecutionEvent.uncertainBatchWhole]
  have throughRecovery := prior.append recovered
  have endpoints := EStateM.Result.ok.inj (returned.symm.trans opened)
  exact ⟨schedules, batch, preparedTable, prepared, ⟨poisoned, append⟩, handle, start, refs,
    endpoints.1, endpoints.2.symm, old, throughRecovery, writeEntry,
    start.continuesReadyCalls refs view inodes runs storage origin
      (events ++ [.interruptedAppendCrashRecovered request input batch]) firstOffset pins throughRecovery writeEntry window⟩

end AppendReopen

end Alvoki.Storage.DiskSession
