import Alvoki.Storage.Disk.NativeFreshOpenedSessions
import Alvoki.Storage.Disk.NativeCheckpointSampledTableOpen

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

/-- Start at the actual fresh return and follow the supported calls on
its handle to the final checkpoint stop. The subsequently selected
recovery, write and snapshot extend that same client ledger. -/
theorem FreshBootstrapOpenHeap.Returned.recoversFinalCheckpoint
    {heap stream : Type} {call : EStateM IO.Error heap DiskTable} {initial : heap}
    (fresh : FreshBootstrapOpenHeap.Returned call initial)
    {instructions : List NativeOpenedInstruction} {earlier : List NativeExecutionEvent}
    {current : NativeOpenedPosition fresh.handle} (prior : NativeOpenedTrace fresh.start instructions earlier current)
    (view : OpenCloseHeapView heap FileImage)
    (refs : OpenSyncCacheRefs fresh.handle.files fresh.handle.directory.path)
    (cacheAt : view.cacheAt current.reached refs.directory refs.active refs.pending = current.current.ready.state.cache)
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap) (fsync : CheckpointFsync heap)
    {reason : FilePath} {reached : CheckpointWorld heap}
    (stopped : (runCheckpointOnOpenPhaseUntilSyncStop fresh.handle.directory fresh.handle.phase
      fresh.handle.get fresh.handle.set primitives fsync).run
      (view.cacheAt current.reached refs.directory refs.active refs.pending, current.reached) =
        .error (.manifest .syncDirectory, reason) reached)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView current.current.ready.state.session.directory (inodes atHeap) (runs atHeap))
    (names : FilePath → Option Nat) (chosen : names ∈ (observe reached.2).crashBindings) (contents : Nat → ByteArray)
    (storage : ∀ stop : NativeCheckpointSourceStop current primitives fsync (.manifest .syncDirectory) reason reached,
      ∃ effect : FinalCheckpointStorageEffects stop inodes runs observe,
        ∀ path, path = current.current.ready.state.session.directory.file .manifest ∨ effect.scope path →
          ∀ inode, names path = some inode → contents inode ∈ (inodes reached.2).crashBytes inode)
    {rebooted entry : heap} {input : FilePath} {source : RawMarkedOpenInterpreter heap stream}
    (resetCensus : (view.descriptors rebooted).slots = [])
    (resetLock : (view.files rebooted).owners (current.current.ready.state.session.directory.file .lock) = none)
    {errors : List (FilePath × IO.Error)} (attempts : source.FailedCalls rebooted errors entry)
    {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
    {write : FilePath → ByteArray → EStateM IO.Error heap Unit}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    {ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool}
    (effects : OpenPhaseCellEffects view.phase get set) :
    ∃ stop : NativeCheckpointSourceStop current primitives fsync (.manifest .syncDirectory) reason reached,
      call initial = .ok fresh.handle.table fresh.start.reached ∧
      fresh.start.current.history = [] ∧ fresh.start.current.submissions = [] ∧ fresh.start.current.ready.reads = [] ∧
      fresh.handle.contents stop.poisoned fresh.handle.phase = some .poisoned ∧
      fresh.start.current.LedgerSuffix earlier current.current ∧
      NativeOpenedPosition.SampledCheckpointRecovery (view := view) (source := source) (input := input)
        (rebooted := rebooted) (entry := entry) (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity)
        (write := write) (get := get) (set := set) (ptrEq := ptrEq)
        current inodes observe names contents fresh.start.current earlier errors := by
  have exactStop : (runCheckpointOnOpenPhaseUntilSyncStop current.current.ready.state.session.directory
      fresh.handle.phase fresh.handle.get fresh.handle.set primitives fsync).run
      (current.current.ready.state.cache, current.reached) = .error (.manifest .syncDirectory, reason) reached := by
    simpa only [current.directory, cacheAt] using stopped
  obtain ⟨stop⟩ := current.checkpointStopsFromWhole primitives fsync exactStop
  obtain ⟨effect, sampled⟩ := storage stop
  have ledger := prior.common.ledgerSuffix
  exact ⟨stop, fresh.opened, fresh.emptyHistory, fresh.emptySubmissions, fresh.emptyReads, stop.poisonStored, ledger,
    stop.reopensSampledFinalCheckpoint inodes runs observe effect names chosen contents sampled
      resetCensus resetLock attempts effects ledger⟩

end Alvoki.Storage.DiskSession
