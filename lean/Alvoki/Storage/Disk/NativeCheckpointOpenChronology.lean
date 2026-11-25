import Alvoki.Storage.Disk.NativeQuietPowerLossTableOpen
import Alvoki.Storage.Disk.NativeRawManifestStatError
import Alvoki.Storage.Disk.NativeRawCheckpointChunkError

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting

private def observedFiles {heap : Type} (names : heap → FilePath → Option Nat)
    (bytes : heap → Nat → ByteArray) (atHeap : heap) : CheckpointSurvivingFiles :=
  ⟨names atHeap, fun inode => [bytes atHeap inode]⟩

section SelectedReadFiles

variable {heap : Type} {files : heap → CheckpointSurvivingFiles} {selectedPath : FilePath → Prop}

private theorem frameRefl (atHeap : heap) : (files atHeap).Frames selectedPath (files atHeap) :=
  fun _ _ => ⟨rfl, fun _ _ => rfl⟩

/-- Record read-only file effects at each primitive's actual return.
The frame stays on the selected names and their bound inode bytes. -/
structure MarkedTemporaryReadCalls.FileFrames (calls : MarkedTemporaryReadCalls heap)
    (files : heap → CheckpointSurvivingFiles) (selectedPath : FilePath → Prop) : Prop where
  openRead : ∀ path entry,
    (files entry).Frames selectedPath (files (reachedState (calls.openRead path entry)))
  readChunk : ∀ file count entry,
    (files entry).Frames selectedPath (files (reachedState (calls.readChunk file count entry)))
  release : ∀ file entry,
    (files entry).Frames selectedPath (files (dataErrorDropState calls.release file entry))

private theorem exactReadFrames (mismatch : IO.Error) (read : USize → EStateM IO.Error heap ByteArray)
    (keeps : ∀ count entry, (files entry).Frames selectedPath (files (reachedState (read count entry))))
    (remaining : Nat) (buffer : ByteArray) (entry : heap) :
    (files entry).Frames selectedPath
      (files (reachedState (readExactPrefixWith mismatch read remaining buffer entry))) := by
  by_cases empty : remaining = 0
  · rw [readExactPrefixWith]
    simpa only [empty, ↓reduceIte, Pure.pure, EStateM.pure, reachedState] using
      (frameRefl (files := files) (selectedPath := selectedPath) entry)
  · rw [readExactPrefixWith]
    simp only [empty, ↓reduceIte, Bind.bind, EStateM.bind]
    have first := keeps remaining.toUSize entry
    cases issued : read remaining.toUSize entry with
    | error =>
      simpa only [issued, reachedState] using first
    | ok chunk reached =>
      have upToRead : (files entry).Frames selectedPath (files reached) := by
        simpa only [issued, reachedState] using first
      by_cases valid : 0 < chunk.size ∧ chunk.size ≤ remaining
      · simp only [valid]
        exact upToRead.trans (exactReadFrames mismatch read keeps (remaining - chunk.size)
          (if buffer.isEmpty then chunk else buffer ++ chunk) reached)
      · simpa only [issued, valid, ↓reduceDIte, throw, throwThe, MonadExceptOf.throw, EStateM.throw,
          reachedState] using upToRead
termination_by remaining
decreasing_by omega

private theorem manifestReadFrames (read : USize → EStateM IO.Error heap ByteArray)
    (keeps : ∀ count entry, (files entry).Frames selectedPath (files (reachedState (read count entry))))
    (extent : Nat) (entry : heap) :
    (files entry).Frames selectedPath
      (files (reachedState (readIntegrityManifestPrefixWith read extent entry))) := by
  let mismatch := IO.userError "integrity manifest extent changed while reading"
  have first := exactReadFrames mismatch read keeps (min 48 extent) .empty entry
  unfold readIntegrityManifestPrefixWith
  cases issued : readExactPrefixWith mismatch read (min 48 extent) ByteArray.empty entry with
  | error =>
    simpa only [mismatch, Bind.bind, EStateM.bind, issued, reachedState] using first
  | ok header reached =>
    have upToRead : (files entry).Frames selectedPath (files reached) := by
      simpa only [issued, reachedState] using first
    let rest := min (extent - 48) (Manifest.IntegrityCheckpoint.declaredStampBytes header + 1)
    by_cases short : header.size < 48
    · simpa [mismatch, Bind.bind, EStateM.bind, issued, short, Pure.pure, EStateM.pure, reachedState] using upToRead
    · by_cases fits : 48 + rest < USize.size
      · simpa [mismatch, Bind.bind, EStateM.bind, issued, short, rest, fits, Pure.pure, EStateM.pure] using
          upToRead.trans (exactReadFrames mismatch read keeps rest header reached)
      · simpa [mismatch, Bind.bind, EStateM.bind, issued, short, rest, fits, throw, throwThe,
          MonadExceptOf.throw, EStateM.throw, reachedState] using upToRead

private theorem MarkedTemporaryReadCalls.readWithFrames (calls : MarkedTemporaryReadCalls heap)
    (laws : calls.FileFrames files selectedPath) (path : FilePath)
    (read : IO.FS.Handle → EStateM IO.Error heap ByteArray)
    (keeps : ∀ file entry, (files entry).Frames selectedPath (files (reachedState (read file entry))))
    (entry : heap) :
    (files entry).Frames selectedPath (files (reachedState (calls.readWith path read entry))) := by
  have opened := laws.openRead path entry
  cases ran : calls.openRead path entry with
  | error =>
    simpa only [MarkedTemporaryReadCalls.readWith, ran, reachedState] using opened
  | ok file openedAt =>
    have same : reachedState (calls.readWith path read entry) =
        dataErrorDropState calls.release file (reachedState (read file openedAt)) := by
      rw [MarkedTemporaryReadCalls.readWith, ran]
      cases returned : read file openedAt <;> simp [returned, reachedState]
    rw [same]
    rw [ran] at opened
    exact opened.trans ((keeps file openedAt).trans (laws.release file _))

private theorem MarkedTemporaryReadCalls.runPrefixFrames (calls : MarkedTemporaryReadCalls heap)
    (laws : calls.FileFrames files selectedPath) (path : FilePath) (count : Nat) (entry : heap) :
    (files entry).Frames selectedPath (files (reachedState (calls.runPrefix path count entry))) :=
  calls.readWithFrames laws path _ (fun file => exactReadFrames (IO.userError checkpointIntegrityMismatch)
    (calls.readChunk file) (laws.readChunk file) count ByteArray.empty) entry

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
    have frame := fileCalls.readWithFrames laws (directory.file .manifest)
      (fun file => readIntegrityManifestPrefixWith (fileCalls.readChunk file) seen.file.calls.metadata.byteSize.toNat)
      (fun file => manifestReadFrames (fileCalls.readChunk file) (laws.readChunk file) seen.file.calls.metadata.byteSize.toNat)
      seed.afterPending
    simpa only [seen.manifestRead.returns.1, reachedState] using frame
  | succ index prior =>
    have inside := Nat.lt_of_succ_le within
    let path := directory.file (.run seen.manifest.header.generation index)
    have kept := fileCalls.runPrefixFrames laws path (seen.run index inside).stamp.byteCount.toNat (seen.atRun index)
    have read := (seen.readsRun inside).2.1
    rw [read] at kept
    exact (prior (Nat.le_of_lt inside)).trans kept

/-- A short chunk followed by the read error keeps the exact selected
objects, including before the temporary handle's scope drop. -/
theorem RawCheckpointChunkReadError.preservesSelectedFiles
    {selected : RawSelectedCheckpointRunStat (admitted := admitted) seed fileCalls}
    (seen : RawCheckpointChunkReadError selected) (laws : fileCalls.FileFrames files selectedPath) :
    (files seed.afterPending).Frames selectedPath (files seen.reached) := by
  have earlier := selected.reads.preservesSelectedFiles laws (Nat.le_refl selected.index)
  have later := fileCalls.runPrefixFrames laws
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
  frames.lockOpen.trans frames.flock
    |>.trans frames.openDirectory
    |>.trans frames.directoryRef
    |>.trans frames.activeRef
    |>.trans frames.pendingRef

/-- Read-only rejectors share the surrounding admission and drops. -/
theorem RawOpenCacheDisposal.ScopeFileFrames.preserves
    (frames : disposal.ScopeFileFrames finalized files selectedPath)
    (worker : (files seed.afterPending).Frames selectedPath (files workerReached)) :
    (files entry).Frames selectedPath (files finalized.reached) :=
  frames.reachesWorker.trans worker
    |>.trans frames.dispose
    |>.trans frames.unlock
    |>.trans frames.releaseLock

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

/-- A finalized read-only failure and its successor use one native
program. Only the cache references are allocated per attempt. -/
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
    (child : CheckpointCrashChild crash.names admission
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
    unfold CheckpointCrashChild at child
    rw [parentBinding, Option.map_some] at child
    exact child.symm.trans (congrArg some seen.releasesSelected.inode.symm)
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
  refine ⟨?_, ?_, ?_, entry.reopensAfterReadOnlyRejection current remove write rename bootstrap assemble ptrEq target keeper descriptors offsets prepared constructs effects
    booted raw failed sameHeap frame rfl⟩
  · simpa only [sameHeap] using closed
  · rw [sameHeap]
    exact remains.1.trans survived
  · exact (congrArg (fun atHeap => bytes atHeap inode) sameHeap).trans
      ((List.cons.inj (remains.2 inode survived)).1.trans bytesAtReboot)

end

end Alvoki.Storage.DiskSession
