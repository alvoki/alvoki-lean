import Alvoki.Storage.Disk.NativeQuietPowerLossTableOpen
import Alvoki.Storage.Disk.NativeRawManifestStatError
import Alvoki.Storage.Disk.NativeRawCheckpointChunkError
import Alvoki.Storage.Disk.NativeOpenAdmissionStorage

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting

private def observedFiles {heap : Type} (names : heap → FilePath → Option Nat)
    (bytes : heap → Nat → ByteArray) (atHeap : heap) : CheckpointSurvivingFiles :=
  ⟨names atHeap, fun inode => [bytes atHeap inode]⟩

section SelectedReadFiles

variable {heap : Type} {files : heap → CheckpointSurvivingFiles} {selectedPath : FilePath → Prop}

private theorem frameRefl (atHeap : heap) : (files atHeap).Frames selectedPath (files atHeap) :=
  fun _ _ => ⟨rfl, fun _ _ => rfl⟩

/-- Scope effects on the selected paths and their bound inode bytes. -/
abbrev MarkedTemporaryReadCalls.FileFrames (calls : MarkedTemporaryReadCalls heap)
    (files : heap → CheckpointSurvivingFiles) (selectedPath : FilePath → Prop) :=
  calls.ScopeFrames (fun before after => (files before).Frames selectedPath (files after))

end SelectedReadFiles

section ReachedSelectedFiles

variable {heap : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {fileCalls : MarkedTemporaryReadCalls heap}
  {files : heap → CheckpointSurvivingFiles} {selectedPath : FilePath → Prop}

/-- Follow the manifest and each earlier bounded run read, including
their temporary releases. No raw namespace sample is reselected. -/
theorem RawCheckpointRunPrefix.preservesSelectedFiles {stop : Manifest.IntegrityCheckpoint → Nat}
    (seen : RawCheckpointRunPrefix (admitted := admitted) seed fileCalls stop)
    (laws : fileCalls.FileFrames files selectedPath)
    {index : Nat} (within : index ≤ stop seen.manifest) :
    (files seed.afterPending).Frames selectedPath (files (seen.atRun index)) := by
  induction index with
  | zero =>
    have frame := fileCalls.readWithFrames laws CheckpointSurvivingFiles.Frames.trans (directory.file .manifest)
      (fun file => readIntegrityManifestPrefixWith (fileCalls.readChunk file) seen.file.calls.metadata.byteSize.toNat)
      (fun file => manifestReadFrames (frame := fun before after => (files before).Frames selectedPath (files after))
        frameRefl CheckpointSurvivingFiles.Frames.trans (fileCalls.readChunk file) (laws.readChunk file)
        seen.file.calls.metadata.byteSize.toNat) seed.afterPending
    simpa only [seen.manifestRead.returns.1, reachedState] using frame
  | succ index prior =>
    have inside := Nat.lt_of_succ_le within
    let path := directory.file (.run seen.manifest.header.generation index)
    have kept := fileCalls.runPrefixFrames laws frameRefl CheckpointSurvivingFiles.Frames.trans
      path (seen.run index inside).stamp.byteCount.toNat (seen.atRun index)
    have read := (seen.readsRun inside).2.1
    rw [read] at kept
    exact (prior (Nat.le_of_lt inside)).trans kept

/-- A short chunk followed by the read error keeps the exact selected
objects through the temporary handle's scope drop. -/
theorem RawCheckpointChunkReadError.preservesSelectedFiles
    {selected : RawSelectedCheckpointRunStat (admitted := admitted) seed fileCalls}
    (seen : RawCheckpointChunkReadError selected) (laws : fileCalls.FileFrames files selectedPath) :
    (files seed.afterPending).Frames selectedPath (files seen.reached) := by
  have earlier := selected.reads.preservesSelectedFiles laws (Nat.le_refl selected.index)
  have later := fileCalls.runPrefixFrames laws frameRefl CheckpointSurvivingFiles.Frames.trans
    (directory.file (.run selected.reads.manifest.header.generation selected.index))
    selected.stamp.byteCount.toNat (selected.reads.atRun selected.index)
  rw [seen.releasesSelected.returned] at later
  exact earlier.trans later

end ReachedSelectedFiles

section

variable {heap : Type} {input : FilePath} {directory : DiskDirectory}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {admission : CensusOpenAdmissionReports input directory (view.descriptors entry) (view.files entry)}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {fileCalls : MarkedTemporaryReadCalls heap} {release : IO.FS.Handle → heap → heap}

variable {workerReached : heap}
variable (disposal : RawOpenCacheDisposal (admitted := admitted) seed workerReached)
    (finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner disposal.reached)
    (files : heap → CheckpointSurvivingFiles) (selectedPath : FilePath → Prop)

/-- Keep the same protected observation through each reached open,
cache allocation and cleanup operation around a read-only worker. -/
structure RawOpenCacheDisposal.ScopeFileFrames : Prop where
  lockOpen : (files entry).Frames selectedPath (files admitted.afterAppend)
  flock : (files admitted.afterAppend).Frames selectedPath (files admitted.afterFlock)
  openDirectory : (files admitted.afterFlock).Frames selectedPath (files seed.afterOpen)
  directoryRef : (files seed.afterOpen).Frames selectedPath (files seed.afterDirectory)
  activeRef : (files seed.afterDirectory).Frames selectedPath (files seed.afterActive)
  pendingRef : (files seed.afterActive).Frames selectedPath (files seed.afterPending)
  dispose : (files workerReached).Frames selectedPath (files disposal.afterDisposal)
  unlock : (files disposal.afterDisposal).Frames selectedPath (files disposal.reached)
  releaseLock : (files disposal.reached).Frames selectedPath (files finalized.reached)

variable {disposal finalized files selectedPath}

private theorem RawOpenCacheDisposal.ScopeFileFrames.reachesWorker
    (frames : disposal.ScopeFileFrames finalized files selectedPath) :
    (files entry).Frames selectedPath (files seed.afterPending) :=
  admitted.framesThroughCache seed (frame := fun before after => (files before).Frames selectedPath (files after))
    (fun first last => first.trans last) ⟨fun _ => frames.lockOpen, fun _ => frames.flock,
      fun _ => frames.openDirectory, fun _ => frames.directoryRef, fun _ => frames.activeRef, fun _ => frames.pendingRef⟩

/-- Preserve the worker's reached bindings through both runtime drops
and the intervening unlock. These bindings can include a new keeper
that was published before the worker returned an error. -/
theorem RawOpenCacheDisposal.ScopeFileFrames.afterWorker
    (frames : disposal.ScopeFileFrames finalized files selectedPath) :
    (files workerReached).Frames selectedPath (files finalized.reached) :=
  frames.dispose.trans frames.unlock |>.trans frames.releaseLock

/-- Read-only rejectors share the surrounding admission and drops. -/
theorem RawOpenCacheDisposal.ScopeFileFrames.preserves
    (frames : disposal.ScopeFileFrames finalized files selectedPath)
    (worker : (files seed.afterPending).Frames selectedPath (files workerReached)) :
    (files entry).Frames selectedPath (files finalized.reached) :=
  frames.reachesWorker.trans (worker.trans frames.afterWorker)

variable (seen : RawManifestStatError (admitted := admitted) seed fileCalls)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed seen.reached)
    (finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner disposal.reached)
    (files : heap → CheckpointSurvivingFiles) (selectedPath : FilePath → Prop)

/-- The failed manifest stat lies between the same admission and drops. -/
structure RawManifestStatError.FileFrames extends disposal.ScopeFileFrames finalized files selectedPath where
  stat : (files seed.afterPending).Frames selectedPath (files seen.reached)

variable {seen disposal finalized files selectedPath}

/-- Preserve the selected files through the caller-visible stat rejection. -/
theorem RawManifestStatError.FileFrames.preserves
    (frames : seen.FileFrames disposal finalized files selectedPath) :
    (files entry).Frames selectedPath (files finalized.reached) :=
  frames.toScopeFileFrames.preserves frames.stat

end

section FinalizedManifestLookup

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory}
  {view : OpenCloseHeapView heap FileImage} {entry : heap}
  {admission : CensusOpenAdmissionReports input directory (view.descriptors entry) (view.files entry)}
  {source : RawMarkedOpenInterpreter heap stream}
  {raw : RawOpenAdmissionReport admission view source.calls entry}
  {allocation : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock}

/-- Compose the same held lookup and cleanup receipts for any scoped
observation, including the live files and the parent crash maps. -/
theorem RawManifestStatError.finalizesWithFrames
    (seen : RawManifestStatError (admitted := raw) allocation source.fileCalls)
    (disposal : RawOpenCacheDisposal (admitted := raw) allocation seen.reached)
    (sameDisposal : source.dispose = disposal.dispose)
    (finalized : RawOpenErrorLockFinalization view directory source.release raw.lock admission.owner disposal.reached)
    {frame : heap → heap → Prop}
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (admitFrames : raw.CacheFrames allocation frame)
    (stat : source.calls.lookup (directory.file .manifest) allocation.afterPending = .ok (.error seen.cause) seen.reached →
      frame allocation.afterPending seen.reached)
    (dispose : let cache :=
        RawMarkedOpenInterpreter.makeCache directory allocation.directoryRef allocation.activeRef allocation.pendingRef
      source.dispose cache seen.reached = .ok () disposal.afterDisposal → frame seen.reached disposal.afterDisposal)
    (unlock : source.calls.unlock raw.lock disposal.afterDisposal = (match disposal.unlockResult with
        | .ok () => .ok () disposal.reached
        | .error cause => .error cause disposal.reached) →
      frame disposal.afterDisposal disposal.reached)
    (release : source.release raw.lock disposal.reached = finalized.reached → frame disposal.reached finalized.reached) :
    ∃ failed : RawFinalizedOpenAttempt view directory source.calls source.init source.release input entry,
      source.openTable input entry = .error failed.diagnostic failed.reached ∧
      failed.diagnostic = disposal.diagnostic seen.cause ∧ failed.reached = finalized.reached ∧
      frame entry finalized.reached := by
  obtain ⟨failed, returned, cause, reached⟩ := seen.finalizesWithInterpreter source disposal sameDisposal finalized
  have uses := (RawMarkedOpenInterpreter.cacheReferences directory allocation.directoryRef allocation.activeRef
    allocation.pendingRef).1
  have dropped := dispose (sameDisposal.symm ▸ disposal.disposed _ uses)
  exact ⟨failed, returned, cause, reached, trans (raw.framesThroughCache allocation trans admitFrames)
    (trans (stat seen.stat) (trans dropped (trans (unlock disposal.unlocked) (release finalized.finalized))))⟩

end FinalizedManifestLookup

section

variable {heap : Type} {state : NativeReadyState} {crash : NativeReadyQuietCrash state}
  {view : OpenCloseHeapView heap FileImage} {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
  {before rebooted : heap} {beforeCensus : DescriptorInventory}
  {input : FilePath} {calls : RawOpenAdmissionCallbacks heap} {init : OpenSyncCacheCallbacks heap}
  {admission : CensusOpenAdmissionReports input state.session.directory
    (view.descriptors rebooted) (view.files rebooted)}
  {admitted : RawOpenAdmissionReport admission view calls rebooted}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {fileCalls : MarkedTemporaryReadCalls heap} {release : IO.FS.Handle → heap → heap}

/-- A read-only attempt preserves the same selected survivor objects. -/
theorem RawQuietRebootEntry.readsAfterOpenFrame
    (entry : RawQuietRebootEntry crash view names bytes before rebooted beforeCensus)
    {reached : heap}
    (frame : (observedFiles names bytes rebooted).Frames
      (checkpointSurvivorPath state.session.directory state.writer state.writer.target.pair.manifest)
      (observedFiles names bytes reached))
    {retryInput : FilePath}
    {layout : CanonicalKeeperLayout crash.retry.image state.writer.history}
    {selected : SelectedIntegrityCheckpoint state.writer.published.durable
      crash.retry.image.directory.active.manifest state.writer.checkpoint}
    {reader : NativeReadyRestartReads crash retryInput layout selected} {path : FilePath} {payload : ByteArray}
    (selectedPath : checkpointSurvivorPath state.session.directory state.writer state.writer.target.pair.manifest path)
    (observed : reader.ReadsSurvivor path payload) :
    ∃ read : reader.opening.reads.reads.ObservesFile path payload,
      names reached path = some read.object ∧ bytes reached read.object = payload := by
  obtain ⟨read, object, contents⟩ := entry.readsSurvivingFile selectedPath observed
  obtain ⟨sameObject, sameBytes⟩ := frame path selectedPath
  exact ⟨read, sameObject.trans object, (List.cons.inj (sameBytes read.object object)).1.trans contents⟩

/-- A child's local name at the later admission identifies the same
survivor inode at the reboot, even if unrelated names have changed. -/
theorem RawQuietRebootEntry.childAfterOpenFrame
    (entry : RawQuietRebootEntry crash view names bytes before rebooted beforeCensus)
    {reached : heap}
    (frame : (observedFiles names bytes rebooted).Frames
      (checkpointSurvivorPath state.session.directory state.writer state.writer.target.pair.manifest)
      (observedFiles names bytes reached))
    {path : FilePath} {name : String}
    (selectedPath : checkpointSurvivorPath state.session.directory state.writer state.writer.target.pair.manifest path)
    (child : CheckpointCrashChild (names reached) admission path name) :
    CheckpointCrashChild crash.names admission path name :=
  child.trans ((frame path selectedPath).1.trans (entry.survivorNames path (.inr (.inr selectedPath))))

/-- The failed marked manifest stat leaves the selected reader's
exact survivor paths at the heap that the next open will use. -/
theorem RawQuietRebootEntry.readsAfterManifestRejection
    (entry : RawQuietRebootEntry crash view names bytes before rebooted beforeCensus)
    (seen : RawManifestStatError (admitted := admitted) seed fileCalls)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed seen.reached)
    (finalized : RawOpenErrorLockFinalization view state.session.directory release admitted.lock admission.owner disposal.reached)
    (frames : seen.FileFrames disposal finalized (observedFiles names bytes)
      (checkpointSurvivorPath state.session.directory state.writer state.writer.target.pair.manifest))
    {retryInput : FilePath}
    {layout : CanonicalKeeperLayout crash.retry.image state.writer.history}
    {selected : SelectedIntegrityCheckpoint state.writer.published.durable
      crash.retry.image.directory.active.manifest state.writer.checkpoint}
    {reader : NativeReadyRestartReads crash retryInput layout selected} {path : FilePath} {payload : ByteArray}
    (selectedPath : checkpointSurvivorPath state.session.directory state.writer state.writer.target.pair.manifest path)
    (observed : reader.ReadsSurvivor path payload) :
    ∃ read : reader.opening.reads.reads.ObservesFile path payload,
      names finalized.reached path = some read.object ∧ bytes finalized.reached read.object = payload :=
  entry.readsAfterOpenFrame frames.preserves selectedPath observed

end

section

variable {heap stream : Type} {history : List WAL.Write} {log : List DatabaseSubmissions}
  (current : NativeReadPosition history log)
  {crash : NativeReadyQuietCrash current.state}
  {input retryInput : FilePath} {view : OpenCloseHeapView heap FileImage}
  {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
  {before rebooted retryHeap : heap} {beforeCensus : DescriptorInventory}
  {calls : RawOpenAdmissionCallbacks heap} {init : OpenSyncCacheCallbacks heap}
  {admission : CensusOpenAdmissionReports input current.state.session.directory
    (view.descriptors rebooted) (view.files rebooted)}
  {admitted : RawOpenAdmissionReport admission view calls rebooted}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {release : IO.FS.Handle → heap → heap}
  {layout : CanonicalKeeperLayout crash.retry.image current.state.writer.history}
  {selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
    crash.retry.image.directory.active.manifest current.state.writer.checkpoint}
  {reader : NativeReadyRestartReads crash retryInput layout selected}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}

variable (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)

variable (target : layout.target = current.state.writer.target) (keeper : layout.keeper = current.state.writer.wal.active)
    (descriptors : layout.sealed ++ [layout.keeper] = current.state.writer.wal.readDescriptors layout.range.watermark)
    (offsets : selectWalSegmentReads (current.state.writer.wal.segments.map WalSegment.first) layout.range.watermark =
      some (layout.first, (current.state.writer.wal.readDescriptors layout.range.watermark).map WalSegment.first))
    (prepared : Prepared crash.retry.image layout.target layout.plan)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files))
    (effects : OpenPhaseCellEffects view.phase get set)

include target keeper descriptors offsets prepared constructs effects

/-- Carry one reboot's selected names and payloads across the reported
read-only failures to the supplied aligned attempt. Each held failure
uses the worker in its report. Scratch paths stay outside the frame. -/
theorem RawQuietRebootEntry.reopensAfterReadOnlyAttempts
    (entry : RawQuietRebootEntry crash view names bytes before rebooted beforeCensus)
    (booted : (view.descriptors rebooted, view.files rebooted) = (crash.reboot, crash.retry))
    {errors : List (FilePath × IO.Error)}
    (attempts : RawFinalizedOpenAttempts view current.state.session.directory calls init release rebooted errors retryHeap)
    (beforeFlock : ∀ input entry (refused : RawBeforeFlockRejection view calls input entry),
      (observedFiles names bytes entry).Frames current.state.crashPath (observedFiles names bytes refused.reached))
    (flockError : ∀ input entry (refused : RawFlockRejection view calls current.state.session.directory release input entry),
      (observedFiles names bytes entry).Frames current.state.crashPath (observedFiles names bytes refused.reached))
    (held : ∀ input entry (failed : RawFinalizedOpenAttempt view current.state.session.directory calls init release input entry),
      (observedFiles names bytes entry).Frames current.state.crashPath (observedFiles names bytes failed.reached))
    (raw : RawAlignedCheckpointReopenEffects reader.opening reader.capturedChronology view calls init retryHeap
      phaseIdentity tokenIdentity allocatePhase allocateToken stream) :
    (view.descriptors retryHeap, view.files retryHeap) = (view.descriptors rebooted, view.files rebooted) ∧
    (∀ path, current.state.crashPath path → names retryHeap path = crash.names path) ∧
    (∀ path payload,
      checkpointSurvivorPath current.state.session.directory current.state.writer current.state.writer.target.pair.manifest path →
      reader.ReadsSurvivor path payload →
      ∃ read : reader.opening.reads.reads.ObservesFile path payload,
        names retryHeap path = some read.object ∧ bytes retryHeap read.object = payload) ∧
    (∃ next : NativeReadPosition history log, next.reads = current.reads ∧ next.opened = reader.run ∧
      reader.ReachedSession next.state history log current.reads ∧
      Nonempty (raw.ReturnedAt next remove write rename bootstrap assemble get set ptrEq)) := by
  have frame := attempts.frames (frame := fun first last =>
    (observedFiles names bytes first).Frames current.state.crashPath (observedFiles names bytes last))
    (fun _ _ _ => ⟨rfl, fun _ _ => rfl⟩) CheckpointSurvivingFiles.Frames.trans beforeFlock flockError held
  refine ⟨(Prod.ext raw.raw.entryCensus raw.raw.entryFiles).trans booted.symm,
    fun path selected => (frame path selected).1.trans (entry.survivorNames path selected), ?_,
    raw.reopensQuietSelection current remove write rename bootstrap assemble ptrEq target keeper
      descriptors offsets prepared constructs effects⟩
  intro path payload selectedPath observed
  exact entry.readsAfterOpenFrame (fun path selected => frame path (.inr (.inr selected))) selectedPath observed

/-- A finalized read-only failure and its successor use one native
program. Each attempt uses its own cache references. -/
theorem RawQuietRebootEntry.reopensAfterReadOnlyRejection
    (entry : RawQuietRebootEntry crash view names bytes before rebooted beforeCensus)
    (booted : (view.descriptors rebooted, view.files rebooted) = (crash.reboot, crash.retry))
    (raw : RawAlignedCheckpointReopenEffects reader.opening reader.capturedChronology view calls init retryHeap
      phaseIdentity tokenIdentity allocatePhase allocateToken stream)
    (failed : RawFinalizedOpenAttempt view current.state.session.directory calls init release input rebooted)
    (sameHeap : retryHeap = failed.reached)
    (frame : (observedFiles names bytes rebooted).Frames
      (checkpointSurvivorPath current.state.session.directory current.state.writer current.state.writer.target.pair.manifest)
      (observedFiles names bytes failed.reached))
    (sameWorker : failed.recover = fun resolved lock cache => do
      let state ← calls.recoverMarkedWithCacheRefs raw.fileCalls raw.directoryCalls raw.callbacks failed.seed.directoryRef
        failed.seed.activeRef failed.seed.pendingRef remove write rename bootstrap resolved cache
      installReady state.installed allocatePhase allocateToken
        (fun phase token => pure (assemble resolved lock cache phase token))) :
    let recover := fun resolved lock cache => do
      let state ← calls.recoverMarkedWithCacheRefs raw.fileCalls raw.directoryCalls raw.callbacks failed.seed.directoryRef
        failed.seed.activeRef failed.seed.pendingRef remove write rename bootstrap resolved cache
      installReady state.installed allocatePhase allocateToken
        (fun phase token => pure (assemble resolved lock cache phase token))
    failed.disposed.Finalized recover failed.cause failed.finalized ∧
    (view.descriptors retryHeap, view.files retryHeap) = (view.descriptors rebooted, view.files rebooted) ∧
    (∀ path payload,
      checkpointSurvivorPath current.state.session.directory current.state.writer current.state.writer.target.pair.manifest path →
      reader.ReadsSurvivor path payload →
      ∃ read : reader.opening.reads.reads.ObservesFile path payload,
        names retryHeap path = some read.object ∧ bytes retryHeap read.object = payload) ∧
    (∃ next : NativeReadPosition history log, next.reads = current.reads ∧ next.opened = reader.run ∧
      reader.ReachedSession next.state history log current.reads ∧
      Nonempty (raw.ReturnedAt next remove write rename bootstrap assemble get set ptrEq)) := by
  intro recover
  refine ⟨?_, (Prod.ext raw.raw.entryCensus raw.raw.entryFiles).trans booted.symm, ?_,
    raw.reopensQuietSelection current remove write rename bootstrap assemble ptrEq target keeper
      descriptors offsets prepared constructs effects⟩
  · rw [show recover = failed.recover from sameWorker.symm]
    exact failed.disposed.returnsAfterLockFinalization failed.recover failed.cause failed.rejected failed.finalized
  · intro path payload selectedPath observed
    rw [sameHeap]
    exact entry.readsAfterOpenFrame frame selectedPath observed

/-- Follow the same file, directory, repair and allocation callbacks
through a read-only manifest stat rejection and an aligned retry. Each
attempt allocates its own cache. The retry starts at the actual final
lock-drop heap and reads from the framed selected objects there. -/
theorem RawQuietRebootEntry.reopensAfterManifestRejection
    (entry : RawQuietRebootEntry crash view names bytes before rebooted beforeCensus)
    (booted : (view.descriptors rebooted, view.files rebooted) = (crash.reboot, crash.retry))
    (raw : RawAlignedCheckpointReopenEffects reader.opening reader.capturedChronology view calls init retryHeap
      phaseIdentity tokenIdentity allocatePhase allocateToken stream)
    (seen : RawManifestStatError (admitted := admitted) seed raw.fileCalls)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed seen.reached)
    (finalized : RawOpenErrorLockFinalization view current.state.session.directory release admitted.lock
      admission.owner disposal.reached)
    (sameHeap : retryHeap = finalized.reached)
    (frames : seen.FileFrames disposal finalized (observedFiles names bytes)
      (checkpointSurvivorPath current.state.session.directory current.state.writer current.state.writer.target.pair.manifest))
    :
    let install := fun resolved lock cache (opened : Reopened) =>
      installReady opened.installed allocatePhase allocateToken
        (fun phase token => pure (assemble resolved lock cache phase token))
    let failed := seen.finalizedAttempt disposal raw.directoryCalls raw.callbacks remove write rename bootstrap install finalized
    disposal.Finalized failed.recover failed.cause finalized ∧
    (view.descriptors retryHeap, view.files retryHeap) = (view.descriptors rebooted, view.files rebooted) ∧
    (∀ path payload,
      checkpointSurvivorPath current.state.session.directory current.state.writer current.state.writer.target.pair.manifest path →
      reader.ReadsSurvivor path payload →
      ∃ read : reader.opening.reads.reads.ObservesFile path payload,
        names retryHeap path = some read.object ∧ bytes retryHeap read.object = payload) ∧
    (∃ next : NativeReadPosition history log, next.reads = current.reads ∧ next.opened = reader.run ∧
      reader.ReachedSession next.state history log current.reads ∧
      Nonempty (raw.ReturnedAt next remove write rename bootstrap assemble get set ptrEq)) := by
  intro install failed
  exact entry.reopensAfterReadOnlyRejection current remove write rename bootstrap assemble ptrEq target keeper descriptors offsets prepared constructs effects
    booted raw failed sameHeap frames.preserves rfl

/-- Reopen after a positive short run chunk and a reached read error.
The issuing descriptor belongs to the selected run. Its scope drop,
cache disposal and lock drop all precede the same worker's next open. -/
theorem RawQuietRebootEntry.reopensAfterRunChunkRejection
    (entry : RawQuietRebootEntry crash view names bytes before rebooted beforeCensus)
    (booted : (view.descriptors rebooted, view.files rebooted) = (crash.reboot, crash.retry))
    (raw : RawAlignedCheckpointReopenEffects reader.opening reader.capturedChronology view calls init retryHeap
      phaseIdentity tokenIdentity allocatePhase allocateToken stream)
    {run : RawSelectedCheckpointRunStat (admitted := admitted) seed raw.fileCalls}
    (seen : RawCheckpointChunkReadError run)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed seen.reached)
    (finalized : RawOpenErrorLockFinalization view current.state.session.directory release admitted.lock
      admission.owner disposal.reached)
    (sameHeap : retryHeap = finalized.reached)
    (frames : disposal.ScopeFileFrames finalized (observedFiles names bytes)
      (checkpointSurvivorPath current.state.session.directory current.state.writer current.state.writer.target.pair.manifest))
    (readLaws : raw.fileCalls.FileFrames (observedFiles names bytes)
      (checkpointSurvivorPath current.state.session.directory current.state.writer current.state.writer.target.pair.manifest))
    (child : CheckpointCrashChild (names seed.afterPending) admission
      (current.state.session.directory.file (.run run.reads.manifest.header.generation run.index))
      (renderRunFileName run.reads.manifest.header.generation run.index))
    (issuedBytes : bytes seen.opened ((view.handle seen.opened seen.handle).1.inode
      (view.handle seen.opened seen.handle).2.1.description) = seen.bytes)
    :
    let install := fun resolved lock cache (opened : Reopened) =>
      installReady opened.installed allocatePhase allocateToken
        (fun phase token => pure (assemble resolved lock cache phase token))
    let failed := seen.finalizedAttempt disposal raw.directoryCalls raw.callbacks remove write rename bootstrap install finalized
    let inode := (view.handle seen.opened seen.handle).1.inode (view.handle seen.opened seen.handle).2.1.description
    let path := current.state.session.directory.file (.run run.reads.manifest.header.generation run.index)
    (view.descriptors retryHeap).references seen.slot.description = [] ∧
    crash.names path = some inode ∧ crash.contents inode = seen.bytes ∧
    names retryHeap path = some inode ∧ bytes retryHeap inode = seen.bytes ∧
    disposal.Finalized failed.recover failed.cause finalized ∧
    (view.descriptors retryHeap, view.files retryHeap) = (view.descriptors rebooted, view.files rebooted) ∧
    (∀ path payload,
      checkpointSurvivorPath current.state.session.directory current.state.writer current.state.writer.target.pair.manifest path →
      reader.ReadsSurvivor path payload →
      ∃ read : reader.opening.reads.reads.ObservesFile path payload,
        names retryHeap path = some read.object ∧ bytes retryHeap read.object = payload) ∧
    (∃ next : NativeReadPosition history log, next.reads = current.reads ∧ next.opened = reader.run ∧
      reader.ReachedSession next.state history log current.reads ∧
      Nonempty (raw.ReturnedAt next remove write rename bootstrap assemble get set ptrEq)) := by
  intro install failed inode path
  have frame := frames.preserves (seen.preservesSelectedFiles readLaws)
  have selectedManifest : current.state.writer.target.pair.manifest = some run.reads.bytes := by
    have bound := run.reads.bound
    have sameFileState : view.files rebooted = crash.retry := congrArg Prod.snd booted
    exact (congrArg (fun state => state.image.directory.active.manifest) sameFileState).symm.trans bound
  have selectedPath : checkpointSurvivorPath current.state.session.directory current.state.writer
      current.state.writer.target.pair.manifest path :=
    .inr (.inr ⟨run.reads.bytes, run.reads.manifest, run.index, selectedManifest, run.reads.decoded, run.within, rfl⟩)
  have parentBinding := run.child.binds
  rw [run.child.atRoot, run.child.atName] at parentBinding
  have binding : crash.names path = some inode := by
    have sameChild := entry.childAfterOpenFrame frames.reachesWorker selectedPath child
    unfold CheckpointCrashChild at sameChild
    rw [parentBinding, Option.map_some] at sameChild
    exact sameChild.symm.trans (congrArg some seen.releasesSelected.inode.symm)
  have survived : names rebooted path = some inode :=
    (entry.survivorNames path (.inr (.inr selectedPath))).trans binding
  have earlier := frames.reachesWorker.trans (run.reads.preservesSelectedFiles readLaws (Nat.le_refl run.index))
  have opened := readLaws.openRead path (run.reads.atRun run.index)
  have actualOpen : raw.fileCalls.openRead path (run.reads.atRun run.index) = .ok seen.handle seen.opened := seen.openRaw
  rw [actualOpen] at opened
  have bytesOnIssue := ((earlier.trans opened) path selectedPath).2 inode survived
  have bytesAtReboot : bytes rebooted inode = seen.bytes :=
    (List.cons.inj bytesOnIssue).1.symm.trans issuedBytes
  have remains := frame path selectedPath
  have closed : (view.descriptors finalized.reached).references seen.slot.description = [] := by
    rw [finalized.census, disposal.returnedCensus, disposal.census, DescriptorInventory.afterDrops_append,
      DescriptorInventory.references_afterDrops, seen.releasesSelected.retired]
    rfl
  have durable := (entry.survivorBytes path selectedPath inode binding).symm.trans bytesAtReboot
  refine ⟨?_, binding, durable, ?_, ?_, entry.reopensAfterReadOnlyRejection current remove write rename bootstrap assemble ptrEq target keeper descriptors offsets prepared constructs effects
    booted raw failed sameHeap frame rfl⟩
  · simpa only [sameHeap] using closed
  · rw [sameHeap]
    exact remains.1.trans survived
  · exact (congrArg (fun atHeap => bytes atHeap inode) sameHeap).trans
      ((List.cons.inj (remains.2 inode survived)).1.trans bytesAtReboot)

end

end Alvoki.Storage.DiskSession
