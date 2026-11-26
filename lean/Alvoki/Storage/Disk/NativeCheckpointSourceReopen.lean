import Alvoki.Storage.Disk.NativeCheckpointStopContinuation
import Alvoki.Storage.Disk.NativeCheckpointOpenChronology
import Alvoki.Storage.Disk.NativeMarkedOpenInterpreter

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair

variable {heap stream : Type} {opened : NativeOpenedHandle heap} {current : NativeOpenedPosition opened}
  {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap} {fsync : CheckpointFsync heap}
  {stage : CheckpointPublication.Step} {reason : FilePath} {reached : CheckpointWorld heap}
  {view : OpenCloseHeapView heap FileImage} {storage : heap → CheckpointStorageObservation}
  {bytes : heap → Nat → ByteArray} {rebooted : heap}

local notation "ready" => current.current.ready
local notation "state" => current.current.ready.state
local notation "dir" => current.current.ready.state.session.directory
local notation "footprint" => checkpointSurvivorPath dir current.current.ready.state.writer
  current.current.ready.state.writer.target.pair.manifest
local notation "liveNames" => fun atHeap => CheckpointSurvivingFiles.names (CheckpointStorageObservation.files (storage atHeap))
local notation "readFiles" => fun atHeap => CheckpointSurvivingFiles.mk (liveNames atHeap) (fun inode => [bytes atHeap inode])

variable (stable : NativeReadyStorage current.current.ready.state (storage reached.2))
  (names : FilePath → Option Nat) (chosen : names ∈ (storage reached.2).crashNames)
  (contents : Nat → ByteArray)
  (durable : ∀ path, checkpointSurvivorPath current.current.ready.state.session.directory
      current.current.ready.state.writer current.current.ready.state.writer.target.pair.manifest path →
    ∀ inode, names path = some inode → contents inode ∈ (storage reached.2).files.bytes inode)
  (rebootObjects : Nat → Nat)

local notation "crash" => NativeReadyStorage.observeCrash stable names chosen contents durable rebootObjects

include durable

/-- Start from the source checkpoint stop's protected storage. The one
reported survivor gives both the reboot entries and the layout of the
later aligned read. A finalized manifest rejection leaves those same
objects at the entry of the successful source open. -/
theorem NativeCheckpointSourceStop.reopensQuietAfterManifestRejection
    (stop : NativeCheckpointSourceStop current primitives fsync stage reason reached)
    (survivorNames : ∀ path, (state).crashPath path → liveNames rebooted path = names path)
    (survivorBytes : ∀ path, footprint path →
      ∀ inode, names path = some inode → bytes rebooted inode = contents inode)
    (booted : (view.descriptors rebooted, view.files rebooted) = ((crash).reboot, (crash).retry))
    {input retryInput : FilePath} {calls : RawOpenAdmissionCallbacks heap} {init : OpenSyncCacheCallbacks heap}
    {admission : CensusOpenAdmissionReports input dir (view.descriptors rebooted) (view.files rebooted)}
    {admitted : RawOpenAdmissionReport admission view calls rebooted}
    {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
    {fileCalls : MarkedTemporaryReadCalls heap} {release : IO.FS.Handle → heap → heap}
    (seen : RawManifestStatError (admitted := admitted) seed fileCalls)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed seen.reached)
    (finalized : RawOpenErrorLockFinalization view dir release admitted.lock admission.owner disposal.reached)
    (frames : seen.FileFrames disposal finalized readFiles footprint)
    {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
    {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
    {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
    (observe : ∀ layout : CanonicalKeeperLayout (crash).retry.image (state).writer.history,
      layout.target = (state).writer.target → Prepared (crash).retry.image layout.target layout.plan →
      ∀ selected : SelectedIntegrityCheckpoint (state).writer.published.durable
        (crash).retry.image.directory.active.manifest (state).writer.checkpoint,
      ∃ (reader : NativeReadyRestartReads crash retryInput layout selected)
        (raw : RawAlignedCheckpointReopenEffects reader.opening reader.capturedChronology view calls init
          finalized.reached phaseIdentity tokenIdentity allocatePhase allocateToken stream),
        raw.fileCalls = fileCalls)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects view.phase get set) (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    RawQuietRebootEntry crash view liveNames bytes reached.2 rebooted (view.descriptors reached.2) ∧
    ∃ (layout : CanonicalKeeperLayout (crash).retry.image (state).writer.history)
      (selected : SelectedIntegrityCheckpoint (state).writer.published.durable
        (crash).retry.image.directory.active.manifest (state).writer.checkpoint)
      (reader : NativeReadyRestartReads crash retryInput layout selected)
      (raw : RawAlignedCheckpointReopenEffects reader.opening reader.capturedChronology view calls init
        finalized.reached phaseIdentity tokenIdentity allocatePhase allocateToken stream),
      let install := fun resolved lock cache (result : Reopened) =>
        installReady result.installed allocatePhase allocateToken
          (fun phase token => pure (RawMarkedOpenInterpreter.assemble resolved lock cache phase token))
      let failed := seen.finalizedAttempt disposal raw.directoryCalls raw.callbacks remove write rename bootstrap install finalized
      raw.fileCalls = fileCalls ∧ disposal.Finalized failed.recover failed.cause finalized ∧
      (view.descriptors finalized.reached, view.files finalized.reached) = (view.descriptors rebooted, view.files rebooted) ∧
      (∀ path payload, footprint path → reader.ReadsSurvivor path payload →
        ∃ read : reader.opening.reads.reads.ObservesFile path payload,
          liveNames finalized.reached path = some read.object ∧ bytes finalized.reached read.object = payload) ∧
      ∃ next : NativeReadPosition current.current.history current.current.submissions,
        next.reads = (ready).reads ∧ next.opened = reader.run ∧
        reader.ReachedSession next.state current.current.history current.current.submissions (ready).reads ∧
        Nonempty (raw.ReturnedAt next remove write rename bootstrap RawMarkedOpenInterpreter.assemble get set ptrEq) := by
  have reboot := (stop.observesReboot (view := view) (storage := storage) (bytes := bytes) (rebooted := rebooted)
    stable names chosen contents durable rebootObjects survivorNames survivorBytes).2
  have retained := (ready).readPrefix.refines.1.retained
  obtain ⟨layout, target, keeper, descriptors, offsets, prepared⟩ := retained.powerLossLayout
  let selected : SelectedIntegrityCheckpoint (state).writer.published.durable
      (crash).retry.image.directory.active.manifest (state).writer.checkpoint := retained.resumed.selected
  generalize retryAt : finalized.reached = retryHeap at observe ⊢
  obtain ⟨reader, raw, sameCalls⟩ := observe layout target prepared selected
  subst fileCalls
  obtain ⟨failed, sameCensusAndFiles, selectedBytes, returned⟩ :=
    reboot.reopensAfterManifestRejection ready remove write rename bootstrap RawMarkedOpenInterpreter.assemble ptrEq
      target keeper descriptors offsets prepared RawMarkedOpenInterpreter.assembles effects booted raw seen disposal finalized retryAt.symm frames
  exact ⟨reboot, layout, selected, reader, raw, rfl, failed, sameCensusAndFiles, selectedBytes, returned⟩

end Alvoki.Storage.DiskSession
