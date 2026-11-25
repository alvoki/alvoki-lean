import Alvoki.Storage.Disk.NativeQuietPowerLossTableOpen
import Alvoki.Storage.Disk.NativeRawManifestStatError

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

private def observedFiles {heap : Type} (names : heap → FilePath → Option Nat)
    (bytes : heap → Nat → ByteArray) (atHeap : heap) : CheckpointSurvivingFiles :=
  ⟨names atHeap, fun inode => [bytes atHeap inode]⟩

section

variable {heap : Type} {input : FilePath} {directory : DiskDirectory}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {admission : CensusOpenAdmissionReports input directory (view.descriptors entry) (view.files entry)}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {fileCalls : MarkedTemporaryReadCalls heap} {release : IO.FS.Handle → heap → heap}

variable (seen : RawManifestStatError (admitted := admitted) seed fileCalls)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed seen.reached)
    (finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner disposal.reached)
    (files : heap → CheckpointSurvivingFiles) (selectedPath : FilePath → Prop)

/-- Each step of the failed lookup has its own protected filesystem
footprint. Earlier probes return at their entry, so only the
append-open of the existing lock, lock acquisition, cache allocation,
failed stat, and cleanup can advance the heap. -/
structure RawManifestStatError.FileFrames : Prop where
  lockOpen : (files entry).Frames selectedPath (files admitted.afterAppend)
  flock : (files admitted.afterAppend).Frames selectedPath (files admitted.afterFlock)
  openDirectory : (files admitted.afterFlock).Frames selectedPath (files seed.afterOpen)
  directoryRef : (files seed.afterOpen).Frames selectedPath (files seed.afterDirectory)
  activeRef : (files seed.afterDirectory).Frames selectedPath (files seed.afterActive)
  pendingRef : (files seed.afterActive).Frames selectedPath (files seed.afterPending)
  stat : (files seed.afterPending).Frames selectedPath (files seen.reached)
  dispose : (files seen.reached).Frames selectedPath (files disposal.afterDisposal)
  unlock : (files disposal.afterDisposal).Frames selectedPath (files disposal.reached)
  releaseLock : (files disposal.reached).Frames selectedPath (files finalized.reached)

variable {seen disposal finalized files selectedPath}

/-- Preserve only the selected names and their bound inode bytes
through the reached callback heaps of a caller-visible rejection. -/
theorem RawManifestStatError.FileFrames.preserves
    (frames : seen.FileFrames disposal finalized files selectedPath) :
    (files entry).Frames selectedPath (files finalized.reached) :=
  frames.lockOpen.trans frames.flock
    |>.trans frames.openDirectory
    |>.trans frames.directoryRef
    |>.trans frames.activeRef
    |>.trans frames.pendingRef
    |>.trans frames.stat
    |>.trans frames.dispose
    |>.trans frames.unlock
    |>.trans frames.releaseLock

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
      names finalized.reached path = some read.object ∧ bytes finalized.reached read.object = payload := by
  obtain ⟨read, object, contents⟩ := entry.readsSurvivingFile selectedPath observed
  obtain ⟨sameObject, sameBytes⟩ := frames.preserves path selectedPath
  exact ⟨read, sameObject.trans object, (List.cons.inj (sameBytes read.object object)).1.trans contents⟩

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

/-- Follow the same file, directory, repair and allocation callbacks
through a read-only manifest stat rejection and an aligned retry. Each
attempt allocates its own cache. The retry starts at the actual final
lock-drop heap and reads from the framed selected objects there. -/
theorem RawQuietRebootEntry.reopensAfterManifestRejection
    (entry : RawQuietRebootEntry crash view names bytes before rebooted beforeCensus)
    (raw : RawAlignedCheckpointReopenEffects reader.opening reader.capturedChronology view calls init retryHeap
      phaseIdentity tokenIdentity allocatePhase allocateToken stream)
    (seen : RawManifestStatError (admitted := admitted) seed raw.fileCalls)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed seen.reached)
    (finalized : RawOpenErrorLockFinalization view current.state.session.directory release admitted.lock
      admission.owner disposal.reached)
    (sameHeap : retryHeap = finalized.reached)
    (frames : seen.FileFrames disposal finalized (observedFiles names bytes)
      (checkpointSurvivorPath current.state.session.directory current.state.writer current.state.writer.target.pair.manifest))
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)
    (target : layout.target = current.state.writer.target) (keeper : layout.keeper = current.state.writer.wal.active)
    (descriptors : layout.sealed ++ [layout.keeper] = current.state.writer.wal.readDescriptors layout.range.watermark)
    (offsets : selectWalSegmentReads (current.state.writer.wal.segments.map WalSegment.first) layout.range.watermark =
      some (layout.first, (current.state.writer.wal.readDescriptors layout.range.watermark).map WalSegment.first))
    (prepared : Prepared crash.retry.image layout.target layout.plan)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files))
    (effects : OpenPhaseCellEffects view.phase get set) :
    let install := fun resolved lock cache (opened : Reopened) =>
      installReady opened.installed allocatePhase allocateToken
        (fun phase token => pure (assemble resolved lock cache phase token))
    let failed := seen.finalizedAttempt disposal raw.directoryCalls raw.callbacks remove write rename bootstrap install finalized
    (∃ makeCache,
      finishFailedOpen (calls.runOpen input init makeCache (disposal.errorScope failed.recover)) release admitted.lock rebooted =
        .error failed.diagnostic retryHeap) ∧
    (∀ path payload,
      checkpointSurvivorPath current.state.session.directory current.state.writer current.state.writer.target.pair.manifest path →
      reader.ReadsSurvivor path payload →
      ∃ read : reader.opening.reads.reads.ObservesFile path payload,
        names retryHeap path = some read.object ∧ bytes retryHeap read.object = payload) ∧
    (∃ next : NativeReadPosition history log, next.reads = current.reads ∧ next.opened = reader.run ∧
      reader.ReachedSession next.state history log current.reads ∧
      Nonempty (raw.ReturnedAt next remove write rename bootstrap assemble get set ptrEq)) := by
  intro install failed
  obtain ⟨_, makeCache, _, _, returned, _⟩ := failed.returns
  refine ⟨⟨makeCache, ?_⟩, ?_, raw.reopensQuietSelection current remove write rename bootstrap assemble ptrEq target keeper
    descriptors offsets prepared constructs effects⟩
  · exact returned.trans (congrArg (EStateM.Result.error failed.diagnostic) sameHeap.symm)
  · intro path payload selectedPath observed
    rw [sameHeap]
    exact entry.readsAfterManifestRejection seen disposal finalized frames selectedPath observed

end

end Alvoki.Storage.DiskSession
