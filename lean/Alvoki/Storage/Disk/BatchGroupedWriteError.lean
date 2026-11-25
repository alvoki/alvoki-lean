import Alvoki.Storage.Disk.AppendHandleCustody
import Alvoki.Storage.Disk.ClientWriteTrace

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentCommit WAL.Boundary

/-- The reached prefix through the two-file barrier. The append and stage
reports record their actual returned files and the selected handles. No
rename or directory barrier observation is needed after a group error. -/
structure BatchGroupedWriteError (directory : DiskDirectory) (before : SegmentedWriterState) (handle : Type) where
  rows : List (UInt64 × Option UInt64)
  batch : List WAL.Write
  table : PackedTable
  nonempty : rows ≠ []
  prepared : prepareBatch before.installed.table rows = some (batch, table)
  fits : before.installed.walBytes + WAL.frameSize * rows.length < UInt64.size
  guard : BatchActiveGuard directory before.installed
  cache : Cache handle
  openAppend : FilePath → EStateM IO.Error WriteFiles handle
  write : handle → ByteArray → EStateM IO.Error WriteFiles Unit
  flush : handle → EStateM IO.Error WriteFiles Unit
  stage : FilePath → ByteArray → EStateM IO.Error WriteFiles handle
  rename : FilePath → FilePath → EStateM IO.Error (Cache handle × WriteFiles) Unit
  keeper : handle
  marker : handle
  opened : WriteFiles
  written : WriteFiles
  appended : WriteFiles
  staged : WriteFiles
  tails : List ByteArray
  selected : selectAppendHandle cache.active openAppend (directory.file (.walSegment before.installed.activeFirst))
    (WriteFiles.initial before.history (before.wal.directory.staged .walBoundary)) = .ok keeper opened
  wrote : write keeper (WAL.encodeBatch batch) opened = .ok () written
  flushed : flush keeper written = .ok () appended
  appendedFiles : appended =
    { WriteFiles.initial before.history (before.wal.directory.staged .walBoundary) with
      visibleTail := WAL.encode batch, crashTails := ByteArray.empty :: tails, crashPossible := by simp }
  markerWritten : stage (directory.file .stagedWalBoundary)
    (WAL.Boundary.encode (before.installed.walBytes + WAL.frameSize * rows.length).toUInt64) appended = .ok marker staged
  stagedFiles : staged = { appended with marker := { appended.marker with
    staged := some (WAL.Boundary.encode (before.installed.walBytes + WAL.frameSize * rows.length).toUInt64, false) } }
  syncFiles : Array FilePath → EStateM IO.Error WriteFiles Unit
  group : ReachedWriteGroup (handle := handle) directory before.installed.activeFirst
    (WAL.Boundary.encode (before.installed.walBytes + WAL.frameSize * rows.length).toUInt64) staged syncFiles
  groupCache : group.cache =
    Cache.remember ({ cache with active := some (directory.file (.walSegment before.installed.activeFirst), keeper) } :
      Cache handle) (directory.file .stagedWalBoundary) marker
  memberFailed : (∃ cause after, group.fsync group.keeperHandle staged = .error cause after) ∨
    ∃ cause after, group.fsync group.stagedHandle (reachedState (group.fsync group.keeperHandle staged)) = .error cause after

namespace BatchGroupedWriteError

variable {directory : DiskDirectory} {before : SegmentedWriterState} {handle : Type}

private abbrev count (seen : BatchGroupedWriteError directory before handle) : Nat :=
  before.installed.walBytes + WAL.frameSize * seen.rows.length

private abbrev initial (before : SegmentedWriterState) : WriteFiles :=
  WriteFiles.initial before.history (before.wal.directory.staged .walBoundary)

private def appendCache (seen : BatchGroupedWriteError directory before handle) : Cache handle :=
  { seen.cache with active := some (directory.file (.walSegment before.installed.activeFirst), seen.keeper) }

/-- The native-shaped callbacks run the exact append and stage schedules
and use the actual grouped sync, with two reached member observations. -/
noncomputable def calls (seen : BatchGroupedWriteError directory before handle) : WriteRequest.Calls handle where
  cache := seen.cache
  lookup := seen.guard.lookup
  append := fun path bytes => runAppendWithCache path bytes seen.openAppend seen.write seen.flush
  stage := fun path bytes => stageFreshWithCache path bytes seen.stage
  sync := SyncPathGroup.run (sync directory.path seen.group.openRead seen.group.fsync)
  rename := seen.rename

private def modeled (seen : BatchGroupedWriteError directory before handle) : WriteEffects :=
  seen.group.effects ⟨.ok (), seen.tails, .ok (), .ok (), .errorBeforeEffect, .errorBeforeEffect⟩

private theorem appendReturned (seen : BatchGroupedWriteError directory before handle) :
    seen.calls.append (directory.file (.walSegment before.installed.activeFirst)) (WAL.encodeBatch seen.batch)
      (seen.cache, initial before) = .ok () (seen.appendCache, seen.appended) := by
  simp only [calls, runAppendWithCache_effect, seen.selected, seen.wrote, seen.flushed, appendCache]

private theorem stageReturned (seen : BatchGroupedWriteError directory before handle) :
    seen.calls.stage (directory.file .stagedWalBoundary) (WAL.Boundary.encode seen.count.toUInt64)
      (seen.appendCache, seen.appended) = .ok () (seen.group.cache, seen.staged) := by
  simp only [calls, stageFreshWithCache, seen.markerWritten, seen.groupCache, appendCache]

/-- The keeper is the handle written and flushed by append, and the
second sync uses the pending handle returned by the staged-marker write. -/
theorem issuingHandles (seen : BatchGroupedWriteError directory before handle) :
    seen.group.keeperHandle = seen.keeper ∧ seen.group.stagedHandle = seen.marker ∧
      seen.group.keeper.effectDescription = seen.group.description seen.keeper ∧
      seen.group.staged.effectDescription = seen.group.description seen.marker := by
  have active := seen.group.active
  have pending := seen.group.pending
  rw [seen.groupCache] at active pending
  simp [Cache.remember, pushPending] at active pending
  exact ⟨active.symm, pending.symm,
    seen.group.keeper.sameDescription.trans (congrArg seen.group.description active.symm),
    seen.group.staged.sameDescription.trans (congrArg seen.group.description pending.symm)⟩

private theorem syncReturned (seen : BatchGroupedWriteError directory before handle) :
    ∃ cause reached, seen.calls.sync #[directory.file (.walSegment before.installed.activeFirst),
      directory.file .stagedWalBoundary] (seen.group.cache, seen.staged) =
      .error cause (seen.group.cache.consume (directory.file .stagedWalBoundary), reached) := by
  simp only [calls]
  rw [groupedActivePending seen.group.keeperNotDirectory seen.group.stagedNotDirectory seen.group.keeperMiss
    seen.group.active seen.group.pending seen.group.openRead seen.group.fsync seen.staged]
  cases keeper : seen.group.fsync seen.group.keeperHandle seen.staged with
  | error cause after =>
    dsimp only
    cases seen.group.fsync seen.group.stagedHandle after with
    | ok value reached => cases value; exact ⟨_, _, rfl⟩
    | error markerCause reached => exact ⟨_, _, rfl⟩
  | ok value after =>
    cases value
    rcases seen.memberFailed with ⟨cause, reached, failed⟩ | ⟨cause, reached, failed⟩
    · rw [keeper] at failed
      contradiction
    · rw [keeper, reachedState] at failed
      dsimp only
      rw [failed]
      exact ⟨_, _, rfl⟩

private theorem groupProjection (seen : BatchGroupedWriteError directory before handle) :
    projectWriteGroup (seen.calls.sync #[directory.file (.walSegment before.installed.activeFirst),
      directory.file .stagedWalBoundary] (seen.group.cache, seen.staged)) =
      seen.modeled.markerStep (WAL.Boundary.encode seen.count.toUInt64) .syncStaged seen.staged :=
  (seen.group.projected ⟨.ok (), seen.tails, .ok (), .ok (), .errorBeforeEffect, .errorBeforeEffect⟩
    (by rw [seen.stagedFiles, seen.appendedFiles]) (by rw [seen.stagedFiles])).2

private theorem groupFailureKeepsMarker (seen : BatchGroupedWriteError directory before handle)
    {cause : IO.Error} {reached : WriteFiles}
    (failed : seen.calls.sync #[directory.file (.walSegment before.installed.activeFirst),
      directory.file .stagedWalBoundary] (seen.group.cache, seen.staged) =
      .error cause (seen.group.cache.consume (directory.file .stagedWalBoundary), reached)) :
    reached.marker.active = (initial before).marker.active ∧
      reached.marker.crashImages = (initial before).marker.crashImages := by
  have effect := seen.groupProjection
  rw [failed, projectWriteGroup] at effect
  have scratch : seen.staged.marker.staged = some (WAL.Boundary.encode seen.count.toUInt64, false) := by
    rw [seen.stagedFiles]
  cases reported : seen.modeled.sync with
  | ok value =>
    cases value
    rw [seen.modeled.markerStep_syncStaged_success _ scratch reported] at effect
    contradiction
  | error outcome =>
    obtain ⟨wal, marker⟩ := outcome
    cases wal <;> cases marker <;>
      simp [WriteEffects.markerStep, reported, WriteFiles.syncWal, WriteFiles.stepMarker, Publication.Image.step,
        scratch] at effect <;>
      simp [effect, seen.stagedFiles, seen.appendedFiles]

private noncomputable def physicalAppend (seen : BatchGroupedWriteError directory before handle)
    (path : FilePath) (bytes : ByteArray) : EStateM IO.Error WriteFiles Unit :=
  fun state => withoutWriteGroupCache (seen.calls.append path bytes (seen.cache, state))

private noncomputable def physicalStage (seen : BatchGroupedWriteError directory before handle)
    (path : FilePath) (bytes : ByteArray) : EStateM IO.Error WriteFiles Unit :=
  fun state => withoutWriteGroupCache (seen.calls.stage path bytes (seen.appendCache, state))

private noncomputable def physicalRename (seen : BatchGroupedWriteError directory before handle)
    (source target : FilePath) : EStateM IO.Error WriteFiles Unit :=
  fun state => withoutWriteGroupCache (seen.calls.rename source target (seen.group.cache, state))

private theorem modelAppend (seen : BatchGroupedWriteError directory before handle) :
    appendBatch seen.modeled seen.batch (initial before) = .ok () seen.appended := by
  rw [seen.appendedFiles]
  rfl

private theorem modelStage (seen : BatchGroupedWriteError directory before handle) :
    seen.modeled.markerStep (WAL.Boundary.encode seen.count.toUInt64) .writeStaged seen.appended = .ok () seen.staged := by
  rw [seen.stagedFiles]
  rfl

private theorem reachedBeforeFailedGroup {state error : Type} {perform : Publication.Step → EStateM error state Unit}
    {start staged final : state} {cause : error}
    (wrote : perform .writeStaged start = .ok () staged)
    (failed : perform .syncStaged staged = .error cause final)
    {prior remaining : List Publication.Step} {action : Publication.Step} {reached : state}
    (scheduled : Publication.steps = prior ++ action :: remaining)
    (arrived : (prior.forM perform) start = .ok () reached) :
    (action = .writeStaged ∧ reached = start) ∨ (action = .syncStaged ∧ reached = staged) := by
  cases prior with
  | nil =>
    simp only [Publication.steps, List.nil_append, List.cons.injEq] at scheduled
    exact .inl ⟨scheduled.1.symm, (EStateM.Result.ok.inj arrived).2.symm⟩
  | cons first tail =>
    simp only [Publication.steps, List.cons_append, List.cons.injEq] at scheduled
    obtain ⟨rfl, scheduled⟩ := scheduled
    cases tail with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at scheduled
      change EStateM.bind (perform .writeStaged) (fun _ => pure ()) start = _ at arrived
      simp only [EStateM.bind, wrote, Pure.pure, EStateM.pure] at arrived
      exact .inr ⟨scheduled.1.symm, (EStateM.Result.ok.inj arrived).2.symm⟩
    | cons second tail =>
      simp only [List.cons_append, List.cons.injEq] at scheduled
      obtain ⟨rfl, _⟩ := scheduled
      change EStateM.bind (perform .writeStaged)
        (fun _ => EStateM.bind (perform .syncStaged) (fun _ => tail.forM perform)) start = _ at arrived
      simp only [EStateM.bind, wrote, failed] at arrived
      contradiction

/-- Derive the failure witness at the last reached publication action.
Record the exact projected sync error with the cache after consumption. -/
theorem observedFailure (seen : BatchGroupedWriteError directory before handle) :
    ∃ (failure : SegmentedBatchFailure directory before) (observed : ObservedBatchFailure failure handle),
      seen.calls = WriteRequest.Calls.ofFailure observed ∧ failure.rows = seen.rows ∧ failure.batch = seen.batch ∧
      seen.calls.sync #[directory.file (.walSegment before.installed.activeFirst), directory.file .stagedWalBoundary]
        (seen.group.cache, seen.staged) =
          .error failure.cause (seen.group.cache.consume (directory.file .stagedWalBoundary), failure.failed) := by
  obtain ⟨cause, reached, synced⟩ := seen.syncReturned
  let keeperPath := directory.file (.walSegment before.installed.activeFirst)
  let staging := directory.file .stagedWalBoundary
  have modeledSync := seen.groupProjection
  rw [synced, projectWriteGroup] at modeledSync
  have physicalSync : seen.syncFiles #[directory.file (.walSegment before.installed.activeFirst),
      directory.file .stagedWalBoundary] seen.staged = .error cause reached := by
    rw [seen.group.execution]
    exact congrArg withoutWriteGroupCache synced
  have modelReports : BatchCommitReports directory before.installed.activeFirst before.history seen.batch seen.count
      seen.modeled (before.wal.directory.staged .walBoundary) seen.physicalAppend seen.physicalStage seen.syncFiles
      seen.physicalRename := by
    constructor
    · simp only [physicalAppend, seen.appendReturned, withoutWriteGroupCache, forgetError, seen.modelAppend]
    · intro appended appendedReport prior action remaining state scheduled arrived
      have exactAppend := (EStateM.Result.ok.inj (appendedReport.symm.trans seen.modelAppend)).2
      subst appended
      rcases reachedBeforeFailedGroup seen.modelStage modeledSync.symm scheduled arrived with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · change forgetError (seen.physicalStage (directory.file .stagedWalBoundary)
          (WAL.Boundary.encode seen.count.toUInt64)) seen.appended = _
        simp only [physicalStage, seen.stageReturned, withoutWriteGroupCache, forgetError, seen.modelStage]
      · change forgetError (seen.syncFiles #[directory.file (.walSegment before.installed.activeFirst),
          directory.file .stagedWalBoundary]) seen.staged = _
        simp only [forgetError, physicalSync, ← modeledSync]
  have physicalReturned : commitBytesAt directory before.installed.activeFirst (WAL.encodeBatch seen.batch) seen.count
      seen.physicalAppend seen.physicalStage seen.syncFiles seen.physicalRename (initial before) = .error cause reached := by
    rw [commitBytesAt_fileEffects]
    simp only [WAL.Boundary.commit, Bind.bind, EStateM.bind, physicalAppend, physicalStage,
      seen.appendReturned, seen.stageReturned, withoutWriteGroupCache, physicalSync]
  let failure : SegmentedBatchFailure directory before :=
    ⟨seen.rows, seen.batch, seen.table, seen.modeled, seen.physicalAppend, seen.physicalStage, seen.syncFiles,
      seen.physicalRename, cause, reached, seen.nonempty, seen.prepared, seen.fits, modelReports, physicalReturned⟩
  let observed : ObservedBatchFailure failure handle := by
    refine ⟨⟨seen.cache, seen.calls.append, seen.calls.stage, seen.calls.sync, seen.calls.rename, rfl, ?_⟩, seen.guard⟩
    intro afterAppend appended prior action remaining state scheduled
    dsimp only
    intro arrived
    change seen.calls.append keeperPath (WAL.encodeBatch seen.batch) (seen.cache, initial before) = _ at appended
    have exactAppend := (EStateM.Result.ok.inj (appended.symm.trans seen.appendReturned)).2
    subst afterAppend
    have stageEffect : performMarkerAt directory before.installed.activeFirst seen.count seen.calls.stage seen.calls.sync
        seen.calls.rename .writeStaged (seen.appendCache, seen.appended) = .ok () (seen.group.cache, seen.staged) :=
      seen.stageReturned
    have syncEffect : performMarkerAt directory before.installed.activeFirst seen.count seen.calls.stage seen.calls.sync
        seen.calls.rename .syncStaged (seen.group.cache, seen.staged) =
        .error cause (seen.group.cache.consume staging, reached) := synced
    rcases reachedBeforeFailedGroup stageEffect syncEffect scheduled arrived with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · change withoutWriteGroupCache (seen.calls.sync #[keeperPath, staging] (seen.group.cache, seen.staged)) = _
      rw [synced, withoutWriteGroupCache]
      exact physicalSync.symm
  exact ⟨failure, observed, rfl, rfl, rfl, synced⟩

/-- Derive the native returned-publication packet from the reached
append, staged write and failed group. -/
theorem returnedReports (seen : BatchGroupedWriteError directory before handle)
    (request : WriteRequest) (rows : request.rows = seen.rows) :
    WriteRequest.ReturnedReports request directory before handle seen.calls := by
  obtain ⟨failure, observed, calls, submitted, _, _⟩ := seen.observedFailure
  rw [calls]
  exact .unknown failure observed (rows.trans submitted.symm)

/-- The exact diagnostic, cache and files reached by the group are also
the return of the shared single or batch dispatcher. -/
theorem returnsError (seen : BatchGroupedWriteError directory before handle)
    (request : WriteRequest) (rows : request.rows = seen.rows)
    (ready : before.RetainedReady directory descriptor) {cause : IO.Error} {reached : WriteFiles}
    (grouped : seen.calls.sync #[directory.file (.walSegment before.installed.activeFirst), directory.file .stagedWalBoundary]
      (seen.group.cache, seen.staged) =
        .error cause (seen.group.cache.consume (directory.file .stagedWalBoundary), reached)) :
    seen.calls.run request directory before = .error (.commitUnknown cause)
      (.poisoned, ⟨(seen.group.cache.consume (directory.file .stagedWalBoundary), reached), before.owners⟩) := by
  have commit : commitBytesAt directory before.installed.activeFirst (WAL.encodeBatch seen.batch) seen.count
      seen.calls.append seen.calls.stage seen.calls.sync seen.calls.rename (seen.cache, initial before) =
      .error cause (seen.group.cache.consume (directory.file .stagedWalBoundary), reached) := by
    rw [commitBytesAt_fileEffects]
    simp only [WAL.Boundary.commit, Bind.bind, EStateM.bind, seen.appendReturned, seen.stageReturned, grouped]
  rw [WriteRequest.Calls.run, request.runReported_eq_batch ready, rows]
  change runBatchWrite directory seen.rows seen.calls.lookup seen.calls.append seen.calls.stage seen.calls.sync
    seen.calls.rename (.ready before.installed, ⟨(seen.cache, WriteFiles.initial before.history
      (before.files.directory.staged .walBoundary)), before.owners⟩) = _
  rw [ready.directoryFiles]
  exact runBatchWrite_commitUnknown seen.guard seen.nonempty seen.prepared seen.fits commit

/-- The grouped error reaches the actual poisoned write outcome and the
client certificate without an eventual release or reopen premise. -/
theorem refinesClient (seen : BatchGroupedWriteError directory before handle)
    (request : WriteRequest) (rows : request.rows = seen.rows)
    (trace : SegmentedClientReadTrace directory initialDescriptor initialWriter allowCollection log reads writer before)
    (initialReady : initialWriter.RetainedReady directory initialDescriptor) :
    ∃ cause reached,
      seen.calls.run request directory before = .error (.commitUnknown cause)
        (.poisoned, ⟨(seen.group.cache.consume (directory.file .stagedWalBoundary), reached), before.owners⟩) ∧
      reached.marker.active = some (WAL.Boundary.encode (WAL.encode before.history).size.toUInt64) ∧
      reached.marker.crashImages = [reached.marker.active] ∧
      WriteRequest.ClientReturn request directory initialDescriptor initialWriter allowCollection log reads writer
        before handle seen.calls (seen.calls.run request directory before) := by
  obtain ⟨cause, reached, grouped⟩ := seen.syncReturned
  have ready := (trace.writes.preservesRetained initialReady).1
  obtain ⟨marker, crashes⟩ := seen.groupFailureKeepsMarker grouped
  have unchanged : reached.marker.crashImages = [reached.marker.active] := by rw [crashes, marker]; rfl
  exact ⟨cause, reached, seen.returnsError request rows ready grouped, marker, unchanged,
    (seen.returnedReports request rows).refinesClient trace initialReady⟩

end BatchGroupedWriteError
end Alvoki.Storage.DiskSession
