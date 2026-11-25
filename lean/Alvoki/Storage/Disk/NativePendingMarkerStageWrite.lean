import Alvoki.Storage.Disk.NativePendingStagedMarkerSync

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentCommit WalSegmentRepair WAL.Boundary

private abbrev StageCall := FilePath × ByteArray
private abbrev StageFiles := DescriptorInventory × WriteFiles
private abbrev StageState := CensusDirectoryCache × StageFiles
private abbrev StageM := ExceptT IO.Error (EStateM StageCall StageState)

private def emptyStage {before : NativeReadyState} (prepared : NativeReadyWritePreparation before) : WriteFiles :=
  { prepared.appended with marker := { prepared.appended.marker with staged := some (ByteArray.empty, false) } }

/-- The first exclusive-create succeeds on the absent staging path. Its
same temporary descriptor sees the issued marker write, which can stop
with an observed visible byte prefix. -/
structure NativeMarkerStageWriteStop {before : NativeReadyState} (prepared : NativeReadyWritePreparation before) where
  request : WriteRequest
  rows : request.rows = prepared.rows
  allocated : NativeReadyWriteStageAllocation prepared
  oldMarker : RunChildLookup allocated.root "WAL.commit" allocated.view
  absent : allocated.view.child allocated.root "WAL.commit.next" = none
  distinct : allocated.stageView.modelObject allocated.openedMarker.child ≠ allocated.view.modelObject oldMarker.child
  tryCreate : FilePath → EStateM IO.Error StageFiles (Except IO.Error CheckpointOpenHandle)
  opened : tryCreate prepared.stagedPath (allocated.afterSelect, prepared.appended) =
    .ok (.ok allocated.stageHandle) (allocated.afterMarkerOpen, emptyStage prepared)
  write : CheckpointOpenHandle → ByteArray → EStateM StageCall StageFiles (Except IO.Error Unit)
  visiblePrefix : ByteArray
  isPrefix : ∃ suffix, visiblePrefix ++ suffix = prepared.marker
  stopped : write allocated.stageHandle prepared.marker (allocated.afterMarkerOpen, emptyStage prepared) =
    .error (prepared.stagedPath, prepared.marker) (allocated.afterMarkerOpen,
      (MarkerInterruption.stage (.unsynced (some visiblePrefix))).interrupt prepared.marker prepared.appended)

namespace NativeMarkerStageWriteStop

variable {before : NativeReadyState} {prepared : NativeReadyWritePreparation before}

def cut (stop : NativeMarkerStageWriteStop prepared) : MarkerInterruption := .stage (.unsynced (some stop.visiblePrefix))

def reached (stop : NativeMarkerStageWriteStop prepared) : StageFiles :=
  (stop.allocated.afterMarkerOpen, stop.cut.interrupt prepared.marker prepared.appended)

def session (_stop : NativeMarkerStageWriteStop prepared) : SegmentedSession :=
  { before.session with phase := .poisoned }

private def tryOpen (stop : NativeMarkerStageWriteStop prepared) (path : FilePath) :
    StageM (Except IO.Error CheckpointOpenHandle) :=
  fun (cache, files) => match stop.tryCreate path files with
  | .ok value reached => .ok (.ok value) (cache, reached)
  | .error cause reached => .ok (.error cause) (cache, reached)

private def writeStage (stop : NativeMarkerStageWriteStop prepared) (file : CheckpointOpenHandle) (bytes : ByteArray) :
    StageM Unit :=
  fun (cache, files) => match stop.write file bytes files with
  | .ok value reached => .ok value (cache, reached)
  | .error tag reached => .error tag (cache, reached)

/-- Run the real exclusive-create, retry, write and flush schedule. Only
a return of that schedule can remember the staging handle in cache. -/
noncomputable def stage (stop : NativeMarkerStageWriteStop prepared) (detach : FilePath → StageM Unit)
    (create : FilePath → StageM CheckpointOpenHandle) (flush : CheckpointOpenHandle → StageM Unit)
    (path : FilePath) (bytes : ByteArray) : StageM Unit := do
  let file ← writeFreshStagedWith stop.tryOpen detach create stop.writeStage flush path bytes
  fun (cache, files) => .ok (.ok ()) (cache.remember path file, files)

theorem stopsStage (stop : NativeMarkerStageWriteStop prepared) (detach create flush) :
    (stop.stage detach create flush prepared.stagedPath prepared.marker).run
      (stop.allocated.appendCache, stop.allocated.afterSelect, prepared.appended) =
    .error (prepared.stagedPath, prepared.marker) (stop.allocated.appendCache, stop.reached) := by
  simp [stage, writeFreshStagedWith, withFreshStaging, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run,
    EStateM.bind, Pure.pure, ExceptT.pure, EStateM.pure, tryOpen, stop.opened, writeStage, stop.stopped, cut, reached]

noncomputable def publication (stop : NativeMarkerStageWriteStop prepared) (detach : FilePath → StageM Unit)
    (create : FilePath → StageM CheckpointOpenHandle) (flush : CheckpointOpenHandle → StageM Unit)
    (sync : Array FilePath → StageM Unit) (rename : FilePath → FilePath → StageM Unit)
    (installed : Installed) (events : List WAL.Write) (bytes : Nat) : StageM Unit :=
  let seen := stop.allocated
  commitBytesAt before.session.directory installed.activeFirst (WAL.encodeBatch events) bytes
    (fun path payload => observeReturnedWriteCall seen.afterSelect (seen.append path payload))
    (stop.stage detach create flush) sync rename

theorem stopsPublication (stop : NativeMarkerStageWriteStop prepared) (detach create flush sync rename) :
    (stop.publication detach create flush sync rename before.writer.installed prepared.batch prepared.count).run
      (before.cache, before.census, prepared.initial) =
    .error (prepared.stagedPath, prepared.marker) (stop.allocated.appendCache, stop.reached) := by
  have stage := stop.stopsStage detach create flush
  change stop.stage detach create flush prepared.stagedPath prepared.marker
      (stop.allocated.appendCache, stop.allocated.afterSelect, prepared.appended) = _ at stage
  rw [publication, commitBytesAt_fileEffects]
  simp only [WAL.Boundary.commit, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run, EStateM.bind,
    observeReturnedWriteCall, stop.allocated.appendReturns, show WAL.Boundary.encode prepared.count.toUInt64 = prepared.marker from rfl, stage]

noncomputable def run (stop : NativeMarkerStageWriteStop prepared) (detach create flush sync rename) :=
  stop.request.runWithInterruption before.session.directory stop.allocated.activeGuard.lookup
    (stop.publication detach create flush sync rename)
    (before.session.phase, ⟨(before.cache, before.census, prepared.initial), before.files.owners⟩)

theorem stopsWrite (stop : NativeMarkerStageWriteStop prepared) (valid : before.Valid) (detach create flush sync rename) :
    stop.run detach create flush sync rename = .error (prepared.stagedPath, prepared.marker)
      (.poisoned, ⟨(stop.allocated.appendCache, stop.reached), before.files.owners⟩) := by
  unfold run
  rw [valid.phase]
  exact stop.request.stopsPublication stop.rows prepared.nonempty prepared.prepared prepared.fits
    stop.allocated.activeGuard (stop.publication detach create flush sync rename) (stop.stopsPublication detach create flush sync rename)

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
  stopped : ∀ detach create flush sync rename, stop.run detach create flush sync rename =
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
