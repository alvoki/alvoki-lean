import Alvoki.Storage.Disk.NativeCheckpointRawSyncStop
import Alvoki.Storage.Disk.NativeFreshOpenedSessions
import Alvoki.Storage.Disk.NativeCheckpointSampledTableOpen

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

/-- Locate the first uncertain return using only public responses. -/
private theorem readyOrFirstUnknown {heap : Type} {opened : NativeOpenedHandle heap}
    (calls : List (NativeReturnedCall opened)) :
    NativeReturnedCalls.ReadyResponses calls ∨
      ∃ prior request cause later, calls = prior ++ .write request (.error (.commitUnknown cause)) :: later ∧
        NativeReturnedCalls.ReadyResponses prior := by
  induction calls with
  | nil => exact .inl (by simp [NativeReturnedCalls.ReadyResponses])
  | cons call rest ih =>
    by_cases first : call.ReadyResponse
    · rcases ih with tail | ⟨prior, request, cause, later, rfl, prefixReady⟩
      · exact .inl (by simpa [NativeReturnedCalls.ReadyResponses] using And.intro first tail)
      · exact .inr ⟨call :: prior, request, cause, later, rfl,
          by simpa [NativeReturnedCalls.ReadyResponses] using And.intro first prefixReady⟩
    · cases call with
      | acquire result => exact (first trivial).elim
      | read pin request result => exact (first trivial).elim
      | write request result =>
        cases result with
        | ok => exact (first trivial).elim
        | error failure =>
          cases failure with
          | rejected => exact (first trivial).elim
          | commitUnknown cause =>
            exact .inr ⟨[], request, cause, rest, rfl, by simp [NativeReturnedCalls.ReadyResponses]⟩

/-- Follow a returned ready prefix with an interrupted checkpoint on
the same public handle. The next call starts with the observed cache
at that exact heap. The checkpoint schedule supplies the stop witness. -/
theorem NativeReturnedCalls.refinesReadyBeforeCheckpointStop
    {heap image : Type} {opened : NativeOpenedHandle heap}
    {writes : NativeReadyWriteCalls opened} {issuer : opened.LatestIssuer}
    {entry checkpointEntry : heap} {known : List DiskSnapshotPin} {calls : List (NativeReturnedCall opened)}
    (executed : NativeReturnedCalls writes issuer entry known calls checkpointEntry)
    (view : OpenCloseHeapView heap image) (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (storage : heap → CheckpointStorageObservation) (inode : IO.FS.Handle → Nat)
    (buffered : heap → IO.FS.Handle → ByteArray)
    (effects : writes.ReturnEffects view inodes runs storage inode buffered)
    (start : NativeOpenedPosition opened) (sameEntry : start.reached = entry)
    (samePins : start.pins.map NativeOpenedPin.raw = known)
    (initial : writes.StorageAt view storage (fun atHeap => (inodes atHeap).visible) start)
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap) (fsync : CheckpointFsync heap)
    {stage : CheckpointPublication.Step} {reason : FilePath} {reached : CheckpointWorld heap}
    (stopped : (runCheckpointOnOpenPhaseUntilSyncStop opened.directory opened.phase opened.get opened.set
      primitives fsync).run
        (view.cacheAt checkpointEntry writes.cache.directory writes.cache.active writes.cache.pending, checkpointEntry) =
          .error (stage, reason) reached) :
    ∃ (last : NativeOpenedPosition opened) (events : List NativeExecutionEvent),
      last.reached = checkpointEntry ∧
      last.pins.map NativeOpenedPin.raw = calls.foldl (fun pins call => call.pinsAfter pins) known ∧
      writes.StorageAt view storage (fun atHeap => (inodes atHeap).visible) last ∧
      events.length = calls.length ∧ (∀ pair ∈ calls.zip events, pair.1.Records pair.2) ∧
      start.current.LedgerSuffix events last.current ∧
      (∀ {first}, writes.WalWindowEffects storage first
          (start.current.history.length + (calls.map NativeReturnedCall.requestedRows).sum) →
        start.WalWindowAt storage first (start.current.history.length + (calls.map NativeReturnedCall.requestedRows).sum) →
        last.WalWindowAt storage first last.current.history.length) ∧
      Nonempty (NativeCheckpointSourceStop last primitives fsync stage reason reached) := by
  have covered : NativeReturnedCalls.ReadyResponses calls := by
    obtain covered | ⟨prior, request, cause, later, rfl, prefixReady⟩ := readyOrFirstUnknown calls
    · exact covered
    obtain ⟨middle, ran, remaining⟩ := executed.splitAppend
    obtain ⟨position, _, atMiddle, _, _, _⟩ := ran.refinesReady prefixReady view inodes runs
      storage inode buffered effects start sameEntry samePins initial
    cases remaining with
    | cons unknown suffix =>
      have poisoned := writes.commitUnknownPoisons position (atMiddle.symm ▸ unknown) effects.writePhase
      have stored := (suffix.fromPoisoned poisoned).2
      have refused := runCheckpointOnOpenPhaseUntilSyncStop_rejectsPhase opened.directory opened.phase
        opened.get opened.set primitives fsync (cache := view.cacheAt checkpointEntry writes.cache.directory
          writes.cache.active writes.cache.pending) (opened.phaseEffects.reads _ _ _ stored) .poisoned
      rw [refused] at stopped
      contradiction
  obtain ⟨last, events, atCheckpoint, pins, physical, length, records, ledger, budget, frames⟩ :=
    executed.refinesReadyFramed covered view inodes runs storage inode buffered effects start sameEntry samePins initial
  have cacheAt : view.cacheAt checkpointEntry writes.cache.directory writes.cache.active writes.cache.pending =
      last.current.ready.state.cache := atCheckpoint ▸ physical.cacheAt
  exact ⟨last, events, atCheckpoint, pins, physical, length, records, ledger,
    fun names window => (frames names window).restrictUpper budget,
    last.checkpointStopsAtReachedCache primitives fsync last.directory cacheAt atCheckpoint stopped⟩

/-- Extend the fresh ledger with the returned calls on the current
handle, which may itself have come from a reopen. The actual checkpoint
call derives its source stop at the last returned heap. Its local
publication and recovery effects can be supplied at that stop. -/
theorem FreshBootstrapOpenHeap.Returned.recoversFinalCheckpoint
    {heap stream : Type} {call : EStateM IO.Error heap DiskTable} {initial : heap}
    (fresh : FreshBootstrapOpenHeap.Returned call initial)
    {earlier : List NativeExecutionEvent} {opened : NativeOpenedHandle heap}
    (start : NativeOpenedPosition opened)
    (ledger : fresh.start.current.LedgerSuffix earlier start.current)
    (sameDirectory : opened.directory = fresh.handle.directory)
    (view : OpenCloseHeapView heap FileImage)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView opened.directory (inodes atHeap) (runs atHeap))
    (writes : NativeReadyWriteCalls opened) (issuer : opened.LatestIssuer)
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    (readyEffects : writes.ReturnEffects view inodes runs (fun atHeap => (observe atHeap).storageObservation) inode buffered)
    (readyEntry : writes.StorageAt view (fun atHeap => (observe atHeap).storageObservation)
      (fun atHeap => (inodes atHeap).visible) start)
    {calls : List (NativeReturnedCall opened)} {atCheckpoint : heap}
    (executed : NativeReturnedCalls writes issuer start.reached (start.pins.map NativeOpenedPin.raw) calls atCheckpoint)
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap) (fsync : CheckpointFsync heap)
    {reason : FilePath} {reached : CheckpointWorld heap}
    (stopped : (runCheckpointOnOpenPhaseUntilSyncStop opened.directory opened.phase
      opened.get opened.set primitives fsync).run
      (view.cacheAt atCheckpoint writes.cache.directory writes.cache.active writes.cache.pending, atCheckpoint) =
        .error (.manifest .syncDirectory, reason) reached)
    {rebooted entry : heap} {input : FilePath} {source : RawMarkedOpenInterpreter heap stream}
    {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
    {write : FilePath → ByteArray → EStateM IO.Error heap Unit}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    {ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool} :
    call initial = .ok fresh.handle.table fresh.start.reached ∧
    fresh.start.current.history = [] ∧ fresh.start.current.submissions = [] ∧ fresh.start.current.ready.reads = [] ∧
    ∃ (current : NativeOpenedPosition opened) (events : List NativeExecutionEvent)
      (stop : NativeCheckpointSourceStop current primitives fsync (.manifest .syncDirectory) reason reached),
      current.reached = atCheckpoint ∧
      current.pins.map NativeOpenedPin.raw = calls.foldl (fun pins request => request.pinsAfter pins)
        (start.pins.map NativeOpenedPin.raw) ∧
      writes.StorageAt view (fun atHeap => (observe atHeap).storageObservation)
        (fun atHeap => (inodes atHeap).visible) current ∧
      events.length = calls.length ∧ (∀ pair ∈ calls.zip events, pair.1.Records pair.2) ∧
      current.current.ready.state.session.directory = fresh.handle.directory ∧
      opened.contents stop.poisoned opened.phase = some .poisoned ∧
      fresh.start.current.LedgerSuffix (earlier ++ events) current.current ∧
      (let storage := fun atHeap => (observe atHeap).storageObservation
       let through := start.current.history.length + (calls.map NativeReturnedCall.requestedRows).sum
       ∀ {first}, writes.WalWindowEffects storage first through →
         start.WalWindowAt storage first through → current.WalWindowAt storage first current.current.history.length) ∧
      let files := fun atHeap => current.directory.symm ▸ observe atHeap
      let cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path :=
        { writes.cache with atRoot := current.directory.symm ▸ writes.cache.atRoot }
      ∀ (names : FilePath → Option Nat), names ∈ (files reached.2).crashBindings → ∀ (contents : Nat → ByteArray),
        ∀ (publication : RenamedCheckpointStorageEffects stop inodes runs files) (effective : Bool)
          (sync : CheckpointRawSyncCalls heap),
          stop.toNativeCheckpointSourcePrefix.DirectoryProjectionEffects view cache.directory →
          sync.DirectoryAt view cache.directory fsync stop.atIssue.2 →
          (∀ literal, view.directory stop.atIssue.2 cache.directory = some literal →
            current.current.ready.state.cache.directory = some (view.handle stop.atIssue.2 literal) →
            RawFsyncTarget view stop.atIssue.2 stop.atIssue.2 literal →
            sync.fsync literal stop.atIssue.2 = .error reason reached.2 →
            CheckpointManifestDirectoryEffect current.current.ready.state.session.directory effective publication.scope
              (files stop.atIssue.2).storageObservation (files reached.2).storageObservation) →
          (∀ path, path = current.current.ready.state.session.directory.file .manifest ∨ publication.scope path →
            ∀ inode, names path = some inode → contents inode ∈ (inodes reached.2).crashBytes inode) →
          (view.descriptors rebooted).slots = [] →
          (view.files rebooted).owners (opened.directory.file .lock) = none →
          ∀ {errors : List (FilePath × IO.Error)}, source.FailedCalls rebooted errors entry →
            OpenPhaseCellEffects view.phase get set →
            NativeOpenedPosition.SampledCheckpointRecovery (view := view) (source := source) (input := input)
              (rebooted := rebooted) (entry := entry) (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity)
              (write := write) (get := get) (set := set) (ptrEq := ptrEq)
              current inodes files stop.manifest names contents fresh.start.current (earlier ++ events) errors := by
  obtain ⟨current, events, atStop, pins, physical, length, records, suffix, wal, ⟨stop⟩⟩ :=
    executed.refinesReadyBeforeCheckpointStop view inodes runs
      (fun atHeap => (observe atHeap).storageObservation) inode buffered readyEffects start rfl rfl readyEntry
      primitives fsync stopped
  have together := ledger.append suffix
  refine ⟨fresh.opened, fresh.emptyHistory, fresh.emptySubmissions, fresh.emptyReads,
    current, events, stop, atStop, pins, physical, length, records, current.directory.trans sameDirectory,
    stop.poisonStored, together, wal, ?_⟩
  intro files cache names chosen contents publication effective sync frames routing durability sampled
    resetCensus resetLock errors attempts effects
  have initialDirectory := congrArg Cache.directory physical.cacheAt
  have projected := stop.toNativeCheckpointSourcePrefix.projectsDirectoryAtIssue view cache.directory initialDirectory frames
  obtain ⟨literal, found, retained, target, issued, _⟩ := stop.manifestDirectoryIssuesRawSync sync cache projected routing
  exact stop.reopensSampledFinalCheckpoint inodes runs files publication effective
    (durability literal found retained target issued) names chosen contents sampled
    resetCensus (current.directory.symm ▸ resetLock) attempts effects together

end Alvoki.Storage.DiskSession
