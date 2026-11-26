import Alvoki.Storage.Disk.NativeClassifiedCheckpointRenameError
import Alvoki.Storage.Disk.NativeAlignedCheckpointReopenEffects

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair CheckpointPublication

variable {heap stream image : Type} {state : NativeReadyState} {input : FilePath}
  {cut : CheckpointPowerCut state.session.directory state.writer}
  {report : NativeCheckpointManifestRenameError (image := image) state cut}
  {crash : NativeCheckpointManifestRenameCrash report} {plan : crash.Plan}
  {reader : NativeCheckpointManifestRenameReads crash input plan}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
  {reached rebooted : heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}

private def renameRebootPath (crash : NativeCheckpointManifestRenameCrash report) (path : FilePath) : Prop :=
  path = state.session.directory.path ∨ path = state.session.directory.file .lock ∨
    checkpointSurvivorPath state.session.directory state.writer crash.pair.manifest path

/-- The power-loss observation connects the returned rename's physical
projection and the reboot heap to the same selected namespace. -/
structure RawManifestRenameReboot (crash : NativeCheckpointManifestRenameCrash report)
    (view : OpenCloseHeapView heap FileImage) (names : heap → FilePath → Option Nat)
    (bytes : heap → Nat → ByteArray) (reached rebooted : heap) : Prop where
  returnedFiles : view.files reached = ⟨report.synced.settled.runs.files report.after, state.files.owners⟩
  returnedCensus : view.descriptors reached = report.synced.settled.runs.descriptors report.after
  survivorNames : ∀ path, renameRebootPath crash path → names rebooted path = crash.names path
  survivorBytes : ∀ path, checkpointSurvivorPath state.session.directory state.writer crash.pair.manifest path →
    ∀ inode, crash.names path = some inode →
      bytes rebooted inode ∈ (report.synced.settled.runs.inodes report.after).crashBytes inode

theorem RawManifestRenameReboot.readsSurvivingFile
    (entry : RawManifestRenameReboot crash view names bytes reached rebooted)
    {path : FilePath} {payload : ByteArray}
    (selectedPath : checkpointSurvivorPath state.session.directory state.writer crash.pair.manifest path)
    (read : reader.ReadsSurvivor path payload) :
    ∃ seen : reader.opening.reads.reads.ObservesFile path payload,
      names rebooted path = some seen.object ∧ bytes rebooted seen.object = payload := by
  obtain ⟨seen, bound, durable⟩ := read
  have contents := entry.survivorBytes path selectedPath seen.object bound
  rw [durable] at contents
  exact ⟨seen, (entry.survivorNames path (.inr (.inr selectedPath))).trans bound, List.mem_singleton.mp contents⟩

/-- The rename survivor and its aligned reader determine the actual
raw reopening callbacks and allocation reports. -/
structure RawManifestRenameReopenEffects (reader : NativeCheckpointManifestRenameReads crash input plan)
    (view : OpenCloseHeapView heap FileImage) (calls : RawOpenAdmissionCallbacks heap)
    (init : OpenSyncCacheCallbacks heap) (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray)
    (reached rebooted : heap)
    (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat)
    (allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed)))
    (allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)) (stream : Type)
    extends RawAlignedCheckpointReopenEffects reader.opening reader.chronology view calls init rebooted
      phaseIdentity tokenIdentity allocatePhase allocateToken stream where
  reboot : RawManifestRenameReboot crash view names bytes reached rebooted

/-- The marked-worker input uses the observed reader's selected manifest,
the rebooted WAL directory and the same checked read chronology. -/
private def NativeCheckpointManifestRenameReads.markedReport (seen : NativeCheckpointManifestRenameReads crash input plan)
    (valid : state.Valid) (pending : PendingClientReplay log reads state.writer.history)
    (bounded : ∀ read ∈ reads, read.BoundedBy state.writer.history.length) :
    MarkedOpenSuccessReports input state.session.directory state.writer.history log reads where
  inventory := crash.reboot
  retry := crash.retry
  layout := plan.layout
  published := crash.publication
  checkpoint := plan.checkpoint
  selected := plan.selected
  vacant := crash.vacant
  opening := ⟨seen.opening.admission, seen.opening.callbacks, seen.opening.reads, .aligned seen.opening.finish,
    seen.chronology, seen.opening.marker, seen.opening.markerFound⟩
  prepared := plan.prepared
  following := seen.opening.reads.walReads.selectedAfterWatermark plan.offsets plan.descriptors
  accepted := plan.accepted
  ordered := valid.retained.resumed.ordered
  wal := crash.rebootWal
  walLayout := ⟨valid.retained.layout.ordered, valid.retained.layout.forward, valid.retained.layout.activeEnd,
    valid.retained.layout.activeBytes⟩
  walValid := plan.walValid
  spans := valid.retained.spans
  active := plan.prepared.pair
  keeper := congrArg WalSegment.first plan.keeper
  kept := congrArg FileImage.kept (crash.reachedFiles valid)
  pending := pending
  bounded := bounded


section

variable {opened : NativeOpenedHandle heap} (current : NativeOpenedPosition opened)
  {cut : CheckpointPowerCut current.current.ready.state.session.directory current.current.ready.state.writer}
  {report : NativeCheckpointManifestRenameError (image := image) current.current.ready.state cut}
  {crash : NativeCheckpointManifestRenameCrash report} {plan : crash.Plan}
  {reader : NativeCheckpointManifestRenameReads crash input plan}

/-- The observed checkpoint return and power loss lead to the table
allocated by the same selected reader. -/
theorem NativeOpenedPosition.opensAfterManifestRenameError
    (seen : RawManifestRenameReopenEffects reader view calls init names bytes reached rebooted phaseIdentity tokenIdentity
      allocatePhase allocateToken stream)
    {cause : IO.Error} {after : CensusDirectoryCache × image}
    (returned : runCheckpointOnOpenPhase report.synced.settled.runs.perform opened.phase opened.get opened.set
      (current.reached, report.synced.settled.runs.entry.image) = .error cause (reached, after))
    (samePhase : view.phase = opened.contents)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files)) :
    let state := current.current.ready.state
    opened.table.UsesOpenCheckpointSchedule state.session.directory opened.files opened.phase ∧
    cause = report.cause ∧ after = (state.cache, report.after) ∧ view.phase reached opened.phase = some .poisoned ∧
    (view.descriptors reached, view.files reached) = (report.synced.settled.runs.descriptors after.2,
      ⟨report.synced.settled.runs.files after.2, state.files.owners⟩) ∧
    (view.descriptors rebooted, view.files rebooted) = (crash.reboot, crash.retry) ∧ (view.descriptors rebooted).slots = [] ∧
    names rebooted (state.session.directory.file .lock) = some ((view.handle seen.raw.afterFlock seen.raw.lock).1.inode
      (view.handle seen.raw.afterFlock seen.raw.lock).2.1.description) ∧
    names rebooted state.session.directory.path = some ((view.handle seen.seed.afterPending seen.seed.handle).1.inode
      (view.handle seen.seed.afterPending seen.seed.handle).2.1.description) ∧
    reader.SelectedReads ∧
    (∀ path payload, checkpointSurvivorPath state.session.directory state.writer crash.pair.manifest path →
      reader.ReadsSurvivor path payload → ∃ read : reader.opening.reads.reads.ObservesFile path payload,
        names rebooted path = some read.object ∧ bytes rebooted read.object = payload) ∧
    ∃ (next : NativeReadPosition current.current.history current.current.submissions)
      (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      DiskTable.OpenSyncFiles.IsOpenAction state.session.directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk state.session.directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      NativeCheckpointManifestRenameReopened current.current.ready crash input next ∧
      reader.run = next.opened ∧ next.opened = .ok next.state.session (next.state.census, next.state.files) ∧
      state.writer.target.range.watermark ≤ next.state.writer.target.range.watermark ∧
      seen.toRawAlignedCheckpointReopenEffects.openTable remove write rename bootstrap assemble makeCache =
        .ok handle.table start.reached ∧
      start.current = ⟨current.current.history, current.current.submissions, next⟩ ∧
      handle.lock = seen.raw.lock ∧ handle.files.UsesCacheReferences seen.seed.activeRef seen.seed.pendingRef
        seen.seed.directoryRef ∧ handle.files.AtDirectory state.session.directory.path ∧
      handle.contents = view.phase ∧ handle.get = opened.get ∧ handle.set = opened.set ∧ handle.ptrEq = opened.ptrEq ∧
      tokenIdentity handle.token = next.state.session.sessionRef ∧ start.pins = [] ∧
      view.files start.reached = next.state.files ∧ view.descriptors start.reached = next.state.census ∧
      view.cacheAt start.reached seen.seed.directoryRef seen.seed.activeRef seen.seed.pendingRef = next.state.cache := by
  intro state
  obtain ⟨source, diagnostic, image, poison⟩ := current.checkpointManifestRenameErrorFromReturn report returned
  obtain ⟨valid, rows, replay⟩ := current.current.ready.readPrefix.refines
  have pending : PendingClientReplay current.current.submissions current.current.ready.reads state.writer.history := rows.symm ▸ replay
  have bounded : ∀ read ∈ current.current.ready.reads, read.BoundedBy state.writer.history.length :=
    rows.symm ▸ current.current.ready.readPrefix.readsBounded
  let marked := reader.markedReport valid pending bounded
  obtain ⟨next, reopened, sameReturn, nextReturned, owner, slot, cache⟩ :=
    current.current.ready.reopensCheckpointManifestRenameWith crash reader
  have phaseEffects : OpenPhaseCellEffects view.phase opened.get opened.set := samePhase.symm ▸ opened.phaseEffects
  obtain ⟨installed⟩ := seen.toRawAlignedCheckpointReopenEffects.installsAtReportedPosition (report := marked)
    next remove write rename bootstrap assemble opened.ptrEq rows sameReturn nextReturned cache owner slot constructs phaseEffects
  have stored : view.phase reached opened.phase = some .poisoned := by
    rw [samePhase]
    exact poison
  refine ⟨source, diagnostic, image, stored, ?_,
    Prod.ext seen.raw.entryCensus seen.raw.entryFiles, ?_, ?_, ?_, reader.readsSelected valid,
    fun _ _ => seen.reboot.readsSurvivingFile, next, installed.cacheOpen, installed.makeCache, installed.handle,
    installed.start, installed.cacheAction, installed.cacheSource, reopened, sameReturn, nextReturned,
    reopened.checkpointWatermark.1, installed.rawOpen, installed.position, installed.lock, installed.references,
    installed.directory, installed.contents, installed.readsPhase, installed.writesPhase, installed.comparesTokens,
    installed.tokenRef, installed.pins, installed.files, installed.census, installed.cache⟩
  · rw [image]
    exact Prod.ext seen.reboot.returnedCensus seen.reboot.returnedFiles
  · rw [seen.raw.entryCensus]
    rfl
  · rw [seen.raw.sameLock, seen.raw.appendHandle]
    exact (seen.reboot.survivorNames _ (.inr (.inl rfl))).trans
      ((reader.opening.reads.sameObjects.2.1.symm).trans reader.lockObject).symm
  · rw [seen.seed.sameHandle, seen.seed.openedHandle]
    exact (seen.reboot.survivorNames _ (.inl rfl)).trans
      ((reader.opening.reads.sameObjects.1.symm).trans reader.directoryObject).symm

end

end Alvoki.Storage.DiskSession
