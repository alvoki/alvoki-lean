import Alvoki.Storage.Disk.Proofs.Native.WAL.NativePendingStagedMarkerSync

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentCommit WalSegmentRepair WAL.Boundary

private abbrev StageCall := FilePath × ByteArray
private abbrev StageFiles := DescriptorInventory × WriteFiles
private abbrev StageState := CensusDirectoryCache × StageFiles
private abbrev StageM := ExceptT IO.Error (EStateM StageCall StageState)

private def stageContents {before : NativeReadyState} (prepared : NativeReadyWritePreparation before)
    (contents : Option (ByteArray × Bool)) : WriteFiles :=
  { prepared.appended with marker := { prepared.appended.marker with staged := contents } }

/-- The callbacks up to the marker payload write, in the stage file
and descriptor projection. The no-follow report includes the child
identity consumed by the regular-file check before retrying. -/
structure MarkerStageOpenCalls where
  tryCreate : FilePath → EStateM IO.Error StageFiles (Except IO.Error CheckpointOpenHandle)
  statNoFollow : FilePath → EStateM IO.Error StageFiles (Except IO.Error (IO.FS.Metadata × DeviceInode))
  unlink : FilePath → EStateM IO.Error StageFiles (Except IO.Error Unit)
  create : FilePath → EStateM IO.Error StageFiles CheckpointOpenHandle

namespace MarkerStageOpenCalls

def metadata (calls : MarkerStageOpenCalls) (path : FilePath) :
    EStateM IO.Error StageFiles (Except IO.Error IO.FS.Metadata) :=
  (calls.statNoFollow path).map (Except.map Prod.fst)

end MarkerStageOpenCalls

/-- The first exclusive create found a stale regular scratch name.
The checked unlink removes only that binding and the next exclusive
create supplies the slot for the pending payload write. -/
structure MarkerStageStaleRetry {before : NativeReadyState} {prepared : NativeReadyWritePreparation before}
    (allocated : NativeReadyWriteStageAllocation prepared) (calls : MarkerStageOpenCalls) where
  stale : RunChildLookup allocated.root "WAL.commit.next" allocated.view
  fileName : String
  details : String
  conflict : calls.tryCreate prepared.stagedPath (allocated.afterSelect, prepared.appended) =
    .ok (.error (.alreadyExists fileName 17 details)) (allocated.afterSelect, prepared.appended)
  metadata : IO.FS.Metadata
  checked : calls.statNoFollow prepared.stagedPath (allocated.afterSelect, prepared.appended) =
    .ok (.ok (metadata, stale.child)) (allocated.afterSelect, prepared.appended)
  regular : metadata.type = .file
  detached : calls.unlink prepared.stagedPath (allocated.afterSelect, prepared.appended) =
    .ok (.ok ()) (allocated.afterSelect, stageContents prepared none)
  detachedView : DirectoryReadNamespace
  objects : detachedView.modelObject = allocated.view.modelObject
  unbound : detachedView.child allocated.root "WAL.commit.next" = none
  otherNames : ∀ name, name ≠ "WAL.commit.next" → detachedView.child allocated.root name = allocated.view.child allocated.root name
  opened : calls.create prepared.stagedPath (allocated.afterSelect, stageContents prepared none) =
    .ok allocated.stageHandle (allocated.afterMarkerOpen, stageContents prepared (some (ByteArray.empty, false)))

/-- A direct create or a checked stale retry reaches the same payload
write schedule, with the handle supplied by the successful create. -/
inductive MarkerStageAcquisition {before : NativeReadyState} {prepared : NativeReadyWritePreparation before}
    (allocated : NativeReadyWriteStageAllocation prepared) (calls : MarkerStageOpenCalls) where
  | first (absent : allocated.view.child allocated.root "WAL.commit.next" = none)
      (opened : calls.tryCreate prepared.stagedPath (allocated.afterSelect, prepared.appended) =
        .ok (.ok allocated.stageHandle) (allocated.afterMarkerOpen, stageContents prepared (some (ByteArray.empty, false))))
  | retry (seen : MarkerStageStaleRetry allocated calls)

/-- The actual exclusive create supplies the temporary descriptor for
the issued marker data write. The stop reports a visible byte prefix. -/
structure NativeMarkerStageWriteStop {before : NativeReadyState} (prepared : NativeReadyWritePreparation before) where
  request : WriteRequest
  rows : request.rows = prepared.rows
  allocated : NativeReadyWriteStageAllocation prepared
  oldMarker : RunChildLookup allocated.root "WAL.commit" allocated.view
  distinct : allocated.stageView.modelObject allocated.openedMarker.child ≠ allocated.view.modelObject oldMarker.child
  calls : MarkerStageOpenCalls
  acquisition : MarkerStageAcquisition allocated calls
  write : CheckpointOpenHandle → ByteArray → EStateM StageCall StageFiles (Except IO.Error Unit)
  visiblePrefix : ByteArray
  isPrefix : ∃ suffix, visiblePrefix ++ suffix = prepared.marker
  stopped : write allocated.stageHandle prepared.marker
      (allocated.afterMarkerOpen, stageContents prepared (some (ByteArray.empty, false))) =
    .error (prepared.stagedPath, prepared.marker) (allocated.afterMarkerOpen,
      (MarkerInterruption.stage (.unsynced (some visiblePrefix))).interrupt prepared.marker prepared.appended)

namespace NativeMarkerStageWriteStop

variable {before : NativeReadyState} {prepared : NativeReadyWritePreparation before}

def cut (stop : NativeMarkerStageWriteStop prepared) : MarkerInterruption := .stage (.unsynced (some stop.visiblePrefix))

def reached (stop : NativeMarkerStageWriteStop prepared) : StageFiles :=
  (stop.allocated.afterMarkerOpen, stop.cut.interrupt prepared.marker prepared.appended)

def session (_stop : NativeMarkerStageWriteStop prepared) : SegmentedSession :=
  { before.session with phase := .poisoned }

private def stageCall (call : EStateM IO.Error StageFiles α) : StageM α :=
  fun (cache, files) => match call files with
  | .ok value reached => .ok (.ok value) (cache, reached)
  | .error cause reached => .ok (.error cause) (cache, reached)

private def writeStage (stop : NativeMarkerStageWriteStop prepared) (file : CheckpointOpenHandle) (bytes : ByteArray) :
    StageM Unit :=
  fun (cache, files) => match stop.write file bytes files with
  | .ok value reached => .ok value (cache, reached)
  | .error tag reached => .error tag (cache, reached)

private noncomputable def detachStale (calls : MarkerStageOpenCalls) (path : FilePath) : StageM Unit :=
  removeStaleStagingWith (fun name => stageCall (calls.metadata name)) (fun name => stageCall (calls.unlink name)) path

/-- The no-follow metadata for the observed child controls the actual
cleanup helper. It returns with exactly the scratch projection cleared. -/
theorem staleDetachReturns {allocated : NativeReadyWriteStageAllocation prepared} {calls : MarkerStageOpenCalls}
    (seen : MarkerStageStaleRetry allocated calls) (cache : CensusDirectoryCache) :
    (detachStale calls prepared.stagedPath).run (cache, allocated.afterSelect, prepared.appended) =
      .ok (.ok ()) (cache, allocated.afterSelect, stageContents prepared none) ∧
    allocated.view.child allocated.root "WAL.commit.next" = some seen.stale.child ∧
    seen.detachedView.child allocated.root "WAL.commit.next" = none ∧
    seen.detachedView.modelObject = allocated.stageView.modelObject ∧
    (∀ name, name ≠ "WAL.commit.next" → allocated.stageView.child allocated.root name =
      seen.detachedView.child allocated.root name) := by
  have bound := seen.stale.binds
  rw [seen.stale.atRoot, seen.stale.atName] at bound
  refine ⟨?_, bound, seen.unbound, seen.objects.trans allocated.stageObjects.symm,
    fun name other => (allocated.stageNames name other).trans (seen.otherNames name other).symm⟩
  have regular : (seen.metadata.type == .file) = true := by rw [seen.regular]; rfl
  simp [detachStale, removeStaleStagingWith, MarkerStageOpenCalls.metadata, stageCall, EStateM.map, Except.map,
    Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run, EStateM.bind, Pure.pure, ExceptT.pure,
    EStateM.pure, seen.checked, regular, seen.detached, RunCollection.ownedUnlinkResult]

/-- Run the real exclusive-create, retry, write and flush schedule. Only
a return of that schedule can remember the staging handle in cache. -/
noncomputable def stage (stop : NativeMarkerStageWriteStop prepared) (flush : CheckpointOpenHandle → StageM Unit)
    (path : FilePath) (bytes : ByteArray) : StageM Unit := do
  let file ← writeFreshStagedWith (fun name => stageCall (stop.calls.tryCreate name)) (detachStale stop.calls)
    (fun name => stageCall (stop.calls.create name)) stop.writeStage flush path bytes
  fun (cache, files) => .ok (.ok ()) (cache.remember path file, files)

theorem stopsStage (stop : NativeMarkerStageWriteStop prepared) (flush) :
    (stop.stage flush prepared.stagedPath prepared.marker).run
      (stop.allocated.appendCache, stop.allocated.afterSelect, prepared.appended) =
    .error (prepared.stagedPath, prepared.marker) (stop.allocated.appendCache, stop.reached) := by
  cases stop.acquisition with
  | first absent opened =>
    simp [stage, writeFreshStagedWith, withFreshStaging, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run,
      EStateM.bind, Pure.pure, ExceptT.pure, EStateM.pure, stageCall, opened, writeStage, stop.stopped, cut, reached]
  | retry seen =>
    have detached := (staleDetachReturns seen stop.allocated.appendCache).1
    change detachStale stop.calls prepared.stagedPath (stop.allocated.appendCache, stop.allocated.afterSelect, prepared.appended) =
      _ at detached
    simp [stage, writeFreshStagedWith, withFreshStaging, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run,
      EStateM.bind, Pure.pure, ExceptT.pure, stageCall, seen.conflict, detached, seen.opened,
      writeStage, stop.stopped, cut, reached]

noncomputable def publication (stop : NativeMarkerStageWriteStop prepared) (flush : CheckpointOpenHandle → StageM Unit)
    (sync : Array FilePath → StageM Unit) (rename : FilePath → FilePath → StageM Unit)
    (installed : Installed) (events : List WAL.Write) (bytes : Nat) : StageM Unit :=
  let seen := stop.allocated
  commitBytesAt before.session.directory installed.activeFirst (WAL.encodeBatch events) bytes
    (fun path payload => observeReturnedWriteCall seen.afterSelect (seen.append path payload))
    (stop.stage flush) sync rename

theorem stopsPublication (stop : NativeMarkerStageWriteStop prepared) (flush sync rename) :
    (stop.publication flush sync rename before.writer.installed prepared.batch prepared.count).run
      (before.cache, before.census, prepared.initial) =
    .error (prepared.stagedPath, prepared.marker) (stop.allocated.appendCache, stop.reached) := by
  have stage := stop.stopsStage flush
  change stop.stage flush prepared.stagedPath prepared.marker
      (stop.allocated.appendCache, stop.allocated.afterSelect, prepared.appended) = _ at stage
  rw [publication, commitBytesAt_fileEffects]
  simp only [WAL.Boundary.commit, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run, EStateM.bind,
    observeReturnedWriteCall, stop.allocated.appendReturns, show WAL.Boundary.encode prepared.count.toUInt64 = prepared.marker from rfl, stage]

noncomputable def run (stop : NativeMarkerStageWriteStop prepared) (flush sync rename) :=
  stop.request.runWithInterruption before.session.directory stop.allocated.activeGuard.lookup
    (stop.publication flush sync rename)
    (before.session.phase, ⟨(before.cache, before.census, prepared.initial), before.files.owners⟩)

theorem stopsWrite (stop : NativeMarkerStageWriteStop prepared) (valid : before.Valid) (flush sync rename) :
    stop.run flush sync rename = .error (prepared.stagedPath, prepared.marker)
      (.poisoned, ⟨(stop.allocated.appendCache, stop.reached), before.files.owners⟩) := by
  unfold run
  rw [valid.phase]
  exact stop.request.stopsPublication stop.rows prepared.nonempty prepared.prepared prepared.fits
    stop.allocated.activeGuard (stop.publication flush sync rename) (stop.stopsPublication flush sync rename)

def files (stop : NativeMarkerStageWriteStop prepared) : FileImage :=
  resumedAppendFiles before.files.image before.writer.history before.writer.wal.active.first stop.reached.2

theorem batchCut (stop : NativeMarkerStageWriteStop prepared) (valid : before.Valid) :
    BatchCutProjection stop.files (prepared.modeledMarkerCut stop.cut) := by
  apply prepared.projectMarkerCut valid stop.cut
  simp only [MarkerInterruption.reachedBatch, (prepared.extended valid).1]
  rfl

/-- Only the fresh scratch changes the directory. The append has
returned, but its recorded crash tails still sit beyond the old marker. -/
theorem fileChoices (stop : NativeMarkerStageWriteStop prepared) (valid : before.Valid) :
    stop.files.directory.active = before.writer.target.pair ∧
    stop.files.directory.crashImages = [before.writer.target.pair] ∧
    stop.files.directory.staged .walBoundary = some (stop.visiblePrefix, false) ∧
    stop.files.keeper.active = some (before.writer.wal.active.bytes ++ WAL.encode prepared.batch) ∧
    stop.files.keeper.crashImages = (ByteArray.empty :: prepared.tails).map
      (fun tail => some (before.writer.wal.active.bytes ++ tail)) := by
  have old : before.files.image.directory.active = before.writer.target.pair := valid.retained.resumed.ready.selected
  have marker := (valid.retained.selectPriorKeeper ByteArray.empty).1
  have pair :
      (⟨before.files.image.directory.active.manifest, some (WAL.Boundary.encode (WAL.encode before.writer.history).size.toUInt64)⟩ :
        DirectoryPublication.Bindings) = before.writer.target.pair := by
    rw [old, ← marker]
  have bytes := valid.retained.layout.activeBytes.symm
  exact ⟨pair, congrArg (fun pair => [pair]) pair, rfl,
    congrArg (fun prefixBytes => some (prefixBytes ++ WAL.encode prepared.batch)) bytes,
    congrArg (fun prefixBytes => (ByteArray.empty :: prepared.tails).map (fun tail => some (prefixBytes ++ tail))) bytes⟩

end NativeMarkerStageWriteStop
/-- A stopped staging write retains no new frames. Its newly allocated
staging description is live at the raw call and still absent from the
pending cache, and the original held lock survives. -/
structure NativePendingMarkerStageWrite (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} (stop : NativeMarkerStageWriteStop prepared) : Prop where
  stopped : ∀ flush sync rename, stop.run flush sync rename =
    .error (prepared.stagedPath, prepared.marker) (.poisoned,
      ⟨(stop.allocated.appendCache, stop.reached), current.state.files.owners⟩)
  phase : stop.session.phase = .poisoned
  held : current.state.files.owners.Owns current.state.session.directory current.state.session.descriptor
  custody : stop.allocated.Custody stop.oldMarker
  distinct : stop.reached.1.inode stop.allocated.markerSlot.description ≠ stop.allocated.view.modelObject stop.oldMarker.child
  pending : stop.allocated.appendCache.pending = []
  active : stop.allocated.appendCache.active = some (prepared.keeperPath, stop.allocated.keeperHandle)
  directory : stop.allocated.appendCache.directory = some (stop.allocated.directoryCapture, current.state.directorySlot, 0)
  pair : stop.files.directory.active = current.state.writer.target.pair
  crashPairs : stop.files.directory.crashImages = [current.state.writer.target.pair]
  scratch : stop.files.directory.staged .walBoundary = some (stop.visiblePrefix, false)
  partialPayload : ∃ suffix, stop.visiblePrefix ++ suffix = prepared.marker
  seals : stop.files.kept = current.state.files.image.kept
  later : stop.files.later = current.state.files.image.later
  marker : stop.files.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64)
  checkpoint : SelectedIntegrityCheckpoint current.state.writer.published.durable stop.files.directory.active.manifest
    current.state.writer.checkpoint
  visibleKeeper : stop.files.keeper.active = some (current.state.writer.wal.active.bytes ++ WAL.encode prepared.batch)
  crashKeepers : stop.files.keeper.crashImages = (ByteArray.empty :: prepared.tails).map
    (fun tail => some (current.state.writer.wal.active.bytes ++ tail))
  keeperPrefix : ∀ candidate ∈ stop.files.keeper.active :: stop.files.keeper.crashImages, ∃ bytes,
    candidate = some bytes ∧
    selectRetained current.state.writer.installed.activeFirst (WAL.encode history).size.toUInt64 bytes =
      .ok current.state.writer.wal.active.bytes
  replay : PendingClientReplay (log ++ [.uncertainBatch prepared.batch]) current.reads history
  bounded : ∀ read ∈ current.reads, read.BoundedBy history.length

theorem NativeReadPosition.stopsAtMarkerStageWrite (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} (stop : NativeMarkerStageWriteStop prepared) :
    NativePendingMarkerStageWrite current stop := by
  obtain ⟨valid, exactHistory, earlier⟩ := current.readPrefix.refines
  let ready := valid.retained
  obtain ⟨pair, crash, scratch, visible, survivors⟩ := stop.fileChoices valid
  have marker := (ready.selectPriorKeeper ByteArray.empty).1
  have ordered : WAL.OrdinalsFrom 1 history := exactHistory ▸ ready.resumed.ordered
  obtain ⟨pending, bounded⟩ := earlier.appendUncertain (batch := prepared.batch) current.readPrefix.readsBounded (.inl rfl) ordered
  have custody := stop.allocated.custody valid stop.oldMarker
  refine ⟨stop.stopsWrite valid, rfl, ready.held, custody, ?_, stop.allocated.pendingEmpty, rfl,
    stop.allocated.directoryCached, pair, crash, scratch, stop.isPrefix, rfl, rfl, ?_, pair.symm ▸ ready.resumed.selected,
    visible, survivors, ?_, pending, bounded⟩
  · intro alias
    obtain ⟨_, _, stage⟩ := stop.allocated.stageBindings
    have stageObject := custody.stagedNamed
    rw [stage, Option.map_some] at stageObject
    exact stop.distinct ((Option.some.inj stageObject).trans alias)
  · rw [pair, marker, exactHistory]
  · intro candidate member
    rw [visible, survivors] at member
    have selectsTail (tail : ByteArray) :
        selectRetained current.state.writer.installed.activeFirst (WAL.encode history).size.toUInt64
          (current.state.writer.wal.active.bytes ++ tail) = .ok current.state.writer.wal.active.bytes := by
      have selected := (ready.selectPriorKeeper tail).2
      rw [← ready.layout.activeBytes, exactHistory] at selected
      exact selected
    rcases List.mem_cons.mp member with rfl | crash
    · exact ⟨_, rfl, selectsTail _⟩
    · obtain ⟨tail, _, rfl⟩ := List.mem_map.mp crash
      exact ⟨_, rfl, selectsTail tail⟩

end Alvoki.Storage.DiskSession
