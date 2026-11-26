import Alvoki.Storage.Disk.NativeOpenWrite
import Alvoki.Storage.Disk.NativeLateWriteRecovery

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentCommit WalSegmentRepair
open WAL.Boundary (WalInodeImage)

private abbrev RootStopM (heap error : Type) := ExceptT error (EStateM IO.FS.Handle heap)

private def returned {heap error α : Type} (action : EStateM error heap α) : RootStopM heap error α :=
  fun before => match action before with
    | .ok value reached => .ok (.ok value) reached
    | .error cause reached => .ok (.error cause) reached

private def classify {heap error α : Type} (kind : IO.Error → error)
    (action : RootStopM heap IO.Error α) : RootStopM heap error α :=
  fun before => match action.run before with
    | .ok result reached => .ok (result.mapError kind) reached
    | .error handle issued => .error handle issued

private abbrev RawSyncCalls.rootWithFsync {heap : Type} (calls : RawSyncCalls heap)
    (directory : DiskDirectory) {files : DiskTable.OpenSyncFiles}
    (cache : OpenSyncCacheRefs files directory.path)
    (fsync : IO.FS.Handle → EStateM IO.FS.Handle heap (Except IO.Error Unit)) : RootStopM heap IO.Error Unit :=
  SyncPathGroup.run (fun path => calls.toRawSyncCacheCalls.syncPath returned fsync
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
    (fun path payload => returned (append.run cache.active path payload))
    (fun path payload => returned (stage.run cache.pending path payload))
    (fun paths => if paths = #[directory.path] then calls.rootWithFsync directory cache fsync
      else returned (calls.group directory.path cache.directory cache.active cache.pending paths))
    (fun source target => returned (rename source target))).run

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
  let syncRoot := fun path => calls.toRawSyncCacheCalls.syncPath returned
    (m := RootStopM heap IO.Error) fsync
    directory.path path cache.directory cache.active cache.pending
  have chosen : syncRoot directory.path renamed = .error handle reached := by
    simp [syncRoot, RawSyncCacheCalls.syncPath, syncWithHandles, Bind.bind, ExceptT.bind,
      ExceptT.bindCont, ExceptT.mk, EStateM.bind, returned, loaded, Pure.pure, ExceptT.pure, EStateM.pure, stopped]
  have rootIssued : calls.rootWithFsync directory cache fsync renamed = .error handle reached := by
    change (SyncPathGroup.run syncRoot #[directory.path]) renamed = _
    simp [SyncPathGroup.run, ← Array.forIn_toList, List.forIn_cons, List.forIn_nil, MonadExcept.tryCatch,
      MonadExceptOf.tryCatch, tryCatchThe, ExceptT.tryCatch, Bind.bind, ExceptT.bind, ExceptT.mk,
      EStateM.bind, StateT.pure, Pure.pure, ExceptT.pure, chosen]
  unfold commitUntilRootFsync
  rw [commitBytesAt_fileEffects]
  simp only [WAL.Boundary.commit, ExceptT.run, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, EStateM.bind,
    returned, wrote, remembered, groupByFiles, ↓reduceIte, synced, moved, rootIssued]

/-- The same public dispatcher can observe an issued final fsync instead
of waiting for its return. The phase, metadata and file prefix all use
the one raw heap and the original handle's callbacks. -/
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
  let load : RootStopM heap DiskWriteError Installed := do
    let stored ← classify .rejected (returned (get phase))
    liftExcept ((stored.installed : Except IO.Error Installed).mapError DiskWriteError.rejected)
  (request.runWithPublication load
    (fun installed => classify .rejected (returned (checkActiveSegmentWith directory installed lookup)))
    (fun next => classify .rejected (returned (set phase next)))
    (fun installed bytes count => classify .commitUnknown
      (calls.commitUntilRootFsync directory cache append stage rename fsync installed.activeFirst count bytes))).run

/-- The actual successful guard can advance the heap. Its reached poison
setter leads to the commit, whose stop exits before the ready setter. -/
theorem WriteRequest.stopsAtRootFsync {heap : Type} (request : WriteRequest) (directory : DiskDirectory)
    {files : DiskTable.OpenSyncFiles} (cache : OpenSyncCacheRefs files directory.path)
    (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (append : RawWalAppendCalls heap) (stage : RawWalStageCalls heap) (calls : RawSyncCalls heap)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (fsync : IO.FS.Handle → EStateM IO.FS.Handle heap (Except IO.Error Unit))
    (phase : IO.Ref (Phase Installed))
    (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit)
    {installed : Installed} {batch : List WAL.Write} {table : PackedTable}
    {entry guarded poisoned reached : heap} {handle : IO.FS.Handle}
    (nonempty : request.rows ≠ [])
    (prepared : prepareBatch installed.table request.rows = some (batch, table))
    (fits : installed.walBytes + WAL.frameSize * request.rows.length < UInt64.size)
    (loaded : get phase entry = .ok (.ready installed) entry)
    (guard : checkActiveSegmentWith directory installed lookup entry = .ok () guarded)
    (assigned : set phase .poisoned guarded = .ok () poisoned)
    (commit : calls.commitUntilRootFsync directory cache append stage rename fsync installed.activeFirst
      (installed.walBytes + WAL.frameSize * request.rows.length) (WAL.encodeBatch batch) poisoned = .error handle reached) :
    request.runUntilRootFsync directory cache lookup append stage calls rename fsync phase get set entry = .error handle reached := by
  cases request with
  | single key value =>
    rw [WriteRequest.rows, prepareBatch_singleton] at prepared
    cases written : installed.table.write key value with
    | none => simp [prepareWrite, written] at prepared
    | some next =>
      simp only [prepareWrite, written, Option.map_some, Option.some.injEq, Prod.mk.injEq] at prepared
      obtain ⟨rfl, rfl⟩ := prepared
      simp only [WriteRequest.rows, List.length_singleton, Nat.mul_one, WAL.encodeBatch_singleton] at fits commit
      simp [runUntilRootFsync, runWithPublication, withPreparedSingleWrite, prepareWrite, WriteRequest.requireWritePreparation,
        publishPreparedWrite, publishPrepared, classify, returned, loaded, written, fits, guard, assigned, commit,
        Phase.installed, liftExcept, Except.pure, Except.mapError, Bind.bind, ExceptT.bind, ExceptT.bindCont,
        ExceptT.mk, ExceptT.run, EStateM.bind, Pure.pure, ExceptT.pure, EStateM.pure]
  | batch rows =>
    simp only [WriteRequest.rows] at fits prepared commit
    have present : rows.isEmpty = false := by
      cases rows <;> simp_all [WriteRequest.rows]
    simp [runUntilRootFsync, runWithPublication, writeBatchSchedule, WriteRequest.requireWritePreparation, publishPreparedWrite,
      publishPrepared, classify, returned, loaded, present, fits, prepared, guard, assigned, commit, Phase.installed,
      liftExcept, Except.pure, Except.mapError, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run,
      EStateM.bind, Pure.pure, ExceptT.pure, EStateM.pure]

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

/-- The reached file group, rename and cached root load establish the
publication payloads at the same unresolved fsync. An observed stop can
settle the new marker even when the write never reports a response. -/
theorem NativeOpenedPosition.stopsAtRootFsync
    (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    {batch : List WAL.Write} {table : PackedTable}
    {guarded poisoned appended staged grouped renamed issued reached : heap} {handle : IO.FS.Handle}
    (nonempty : request.rows ≠ [])
    (prepared : prepareBatch (state).writer.installed.table request.rows = some (batch, table))
    (fits : (state).writer.installed.walBytes + WAL.frameSize * request.rows.length < UInt64.size)
    (checked : checkActiveSegmentWith dir (state).writer.installed lookup current.reached = .ok () guarded)
    (assigned : opened.set opened.phase .poisoned guarded = .ok () poisoned)
    (old : NativeReadyStorage state (storage current.reached))
    (preface : (storage current.reached).Frames (state).crashPath (storage poisoned))
    (wrote : append.run cache.active ((dir).file (.walSegment first)) (WAL.encodeBatch batch) poisoned = .ok () appended)
    (remembered : stage.run cache.pending stagePath
      (WAL.Boundary.encode ((state).writer.installed.walBytes + WAL.frameSize * request.rows.length).toUInt64)
      appended = .ok () staged)
    (synced : calls.group (dir).path cache.directory cache.active cache.pending
      #[(dir).file (.walSegment first), stagePath] staged = .ok () grouped)
    (groupEffects : calls.WalGroupEffects cache view append stage inodes observe inode buffered first
      ((state).writer.installed.walBytes + WAL.frameSize * request.rows.length)
      (state).writer.wal.active.bytes (WAL.encodeBatch batch) poisoned appended staged grouped)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (moved : rename stagePath markerPath grouped = .ok () renamed)
    (renameEffect : ∀ marker, (observe grouped).visible stagePath = some marker →
      WalMarkerRenameEffect dir marker true (storage grouped) (storage renamed))
    (loaded : calls.readDirectory cache.directory renamed = .ok (some handle) issued)
    (readFrame : WalPublicationPayloads.CacheReadFrame dir first (storage renamed) (storage issued))
    (target : RawFsyncTarget view renamed issued handle)
    (root : (storage issued).files.names (dir).path =
      some ((view.descriptors issued).inode (view.handle issued handle).2.1.description))
    (stopped : IO.FS.Handle → EStateM IO.FS.Handle heap (Except IO.Error Unit))
    (noResponse : stopped handle issued = .error handle reached) {effective : Bool}
    (effect : stopped handle issued = .error handle reached →
      (view.handle issued handle).2.1 ∈ (view.descriptors issued).slots →
      (storage issued).files.names (dir).path =
        some ((view.descriptors issued).inode (view.handle issued handle).2.1.description) →
      WalRootSyncEffect dir effective (storage issued) (storage reached)) :
    opened.table.UsesOpenWriteSchedules dir opened.files opened.phase ∧
    request.runUntilRootFsync dir cache lookup append stage calls rename stopped opened.phase opened.get opened.set
      current.reached = .error handle reached ∧
    WalPublicationPayloads.ReachedWrite state batch request.rows (storage reached) true
      (fun published => effective = true → published = true) ∧
    ∀ {rebooted} (sample : RawWriteRebootEntry state view storage (fun h => (storage h).files.names)
        (fun h => (inodes h).visible) reached rebooted), sample.DurableReset →
      (storage current.reached).Frames (state).writeFramePath (storage reached) →
      WalNamePresenceFrame dir 0 (current.current.history.length + request.rows.length)
        (storage current.reached) (storage reached) →
      current.WalWindowAt storage 0 (current.current.history.length + request.rows.length) →
      ∃ target : Target, current.current.SelectedWriteReboot view storage (fun h => (inodes h).visible) 0
        request batch table target reached rebooted := by
  have valid := current.current.ready.readPrefix.refines.1
  have stored := current.stored.trans (congrArg some valid.phase)
  have loadedPhase := opened.phaseEffects.reads current.reached opened.phase _ stored
  have stopCommit :=
    calls.stopsAtRootFsync dir cache append stage rename stopped wrote remembered synced moved loaded noResponse
  have stopWrite := request.stopsAtRootFsync dir cache lookup append stage calls rename stopped opened.phase
    opened.get opened.set nonempty prepared fits loadedPhase checked assigned stopCommit
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
  intro rebooted sample reset frame names window
  exact current.selectsDurableReachedWrite view storage prepared fits old frame published
    (fun h => (inodes h).visible) sample reset names window

end PhysicalStop

end Alvoki.Storage.DiskSession
