import Alvoki.Storage.Disk.NativeExecutionTrace
import Alvoki.Storage.Disk.NativeAlignedMarkedReady

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- Assemble the next write entry from the table and references returned
by the actual installer. The repaired writer and its physical storage
already refer to the same heap. Only the two reached allocation effects
are needed to carry that state to the caller. -/
theorem OpenReferenceAllocations.opensReadyWriter
    {heap : Type} {view : OpenCloseHeapView heap FileImage}
    {state : NativeReadyState} (valid : state.Valid)
    {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
    {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
    {repaired : heap}
    (allocation : OpenReferenceAllocations allocatePhase allocateToken view.phase state.writer.installed repaired)
    {lock : IO.FS.Handle} {files : DiskTable.OpenSyncFiles}
    {assemble : IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable}
    (constructor : DiskTable.OpenReferenceAssembly state.session.directory lock files assemble)
    (cache : OpenSyncCacheRefs files state.session.directory.path)
    {outcome : EStateM.Result IO.Error heap DiskTable}
    (returned : outcome = .ok (assemble allocation.phase allocation.token) allocation.afterToken)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (phaseEffects : OpenPhaseCellEffects view.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)
    {log : List DatabaseSubmissions} {reads : List RecordedSnapshotRead}
    (replay : PendingClientReplay log reads state.writer.history)
    (bounded : ∀ read ∈ reads, read.BoundedBy state.writer.history.length)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (ready : NativeReadyStorage state (observe repaired))
    (keeper : ∀ inode, (observe repaired).files.names
      (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some inode →
      visible repaired inode = state.writer.wal.active.bytes)
    (censusAtRepair : view.descriptors repaired = state.census)
    (ownerAtRepair : (view.handle repaired lock).2.1 = state.owner)
    (cacheAtRepair : view.cacheAt repaired cache.directory cache.active cache.pending = state.cache)
    (cachePhase : CacheAllocationFrame view cache.directory cache.active cache.pending repaired allocation.afterPhase)
    (cacheToken : CacheAllocationFrame view cache.directory cache.active cache.pending allocation.afterPhase allocation.afterToken)
    (rootInode : ∀ captured, state.cache.directory = some (captured, state.directorySlot, 0) →
      captured.inode state.directorySlot.description = state.census.inode state.directorySlot.description)
    (phaseFrame : (observe repaired).Frames state.crashPath (observe allocation.afterPhase))
    (tokenFrame : (observe allocation.afterPhase).Frames state.crashPath (observe allocation.afterToken))
    (phaseKeeper : ∀ inode, (observe repaired).files.names
      (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some inode →
      visible allocation.afterPhase inode = visible repaired inode)
    (tokenKeeper : ∀ inode, (observe allocation.afterPhase).files.names
      (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some inode →
      visible allocation.afterToken inode = visible allocation.afterPhase inode) :
    ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle)
      (nextCache : OpenSyncCacheRefs handle.files start.current.ready.state.session.directory.path),
      outcome = .ok handle.table start.reached ∧
      start.reached = allocation.afterToken ∧
      (handle.phase, handle.token) = (allocation.phase, allocation.token) ∧
      (nextCache.directory, nextCache.active, nextCache.pending) = (cache.directory, cache.active, cache.pending) ∧
      start.current.history = state.writer.history ∧ start.current.submissions = log ∧
      start.current.ready.state = state ∧ start.current.ready.reads = reads ∧
      attachedReadSlot view handle.lock state.owner (state.census.inode state.owner.description) start.reached ∧
      start.WriteStorageEntry view nextCache (observe start.reached) (visible start.reached) := by
  obtain ⟨_, references, stored⟩ := allocation.installs constructor
  let next : NativeReadPosition state.writer.history log :=
    ⟨.ok state.session (state.census, state.files), state, state, reads, .installed rfl valid rfl replay bounded⟩
  let handle : NativeOpenedHandle heap :=
    ⟨_, _, lock, files, allocation.phase, allocation.token, references, view.phase, get, set, phaseEffects, ptrEq⟩
  let start := NativeOpenedPosition.fromOpen handle ⟨state.writer.history, log, next⟩ allocation.afterToken
    rfl (valid.phase.symm ▸ stored)
  have census := cacheToken.census.trans (cachePhase.census.trans censusAtRepair)
  have cacheAt := cacheToken.cache.trans (cachePhase.cache.trans cacheAtRepair)
  have ownerHandle := (cacheToken.handles lock).trans (cachePhase.handles lock)
  have owner : attachedReadSlot view lock state.owner (state.census.inode state.owner.description) allocation.afterToken :=
    ⟨(congrArg (fun handle => handle.2.1) ownerHandle).trans ownerAtRepair,
      census.symm ▸ valid.ownerLive, congrFun (congrArg DescriptorInventory.inode census) _⟩
  obtain ⟨physical, live⟩ := allocation.framesReadyStorage observe visible ready keeper phaseFrame tokenFrame phaseKeeper tokenKeeper
  refine ⟨handle, start, cache, returned, rfl, rfl, rfl, rfl, rfl, rfl, rfl, owner, census, cacheAt, physical, live, ?_⟩
  intro literal found
  change view.directory allocation.afterToken cache.directory = some literal at found
  obtain ⟨captured, atOpen⟩ := valid.captured
  exact physical.bindsOpenCacheDirectory view cacheAt atOpen (rootInode captured atOpen) found

/-- The old target fixes the previously committed history even when
the keeper's physical bytes extend past its marker. -/
theorem NativeReadPosition.SelectedWritePlan.oldHistory
    {history : List WAL.Write} {log : List DatabaseSubmissions}
    {current : NativeReadPosition history log} {batch : List WAL.Write} {image : FileImage}
    (plan : current.SelectedWritePlan batch current.state.writer.target image) :
    plan.history = history := by
  obtain ⟨valid, original, _⟩ := current.readPrefix.refines
  have oldLength := valid.retained.resumed.through.trans (congrArg List.length original)
  have sameLength : plan.history.length = history.length :=
    plan.layout.through.symm.trans ((congrArg (fun target : Target => target.range.through) plan.targetEq).trans oldLength)
  rcases plan.allowed with previous | whole
  · exact previous
  · rw [whole, List.length_append] at sameLength
    have empty : batch = [] := List.length_eq_zero_iff.mp (by omega)
    simpa only [empty, List.append_nil] using whole

/-- The reopened ready position yields the existing replay event directly
from the selected old-or-whole history and the carried snapshot ledger. -/
theorem NativeReadPosition.SelectedWritePlan.ledgerAfterReopen
    {history : List WAL.Write} {log : List DatabaseSubmissions}
    {current : NativeReadPosition history log} {batch : List WAL.Write} {target : Target} {image : FileImage}
    (plan : current.SelectedWritePlan batch target image)
    (next : NativeExecutionPosition) (historyAtReturn : next.history = plan.history)
    (submissionsAtReturn : next.submissions = log ++ [.uncertainBatch batch])
    (kept : next.ready.reads = current.reads)
    (request : WriteRequest) (input : FilePath) (cause : IO.Error) :
    ∃ retained, (⟨history, log, current⟩ : NativeExecutionPosition).LedgerSuffix
      [.uncertainWriteCrashRecovered request input cause batch retained]
      next := by
  obtain ⟨retained, allowed, selected⟩ : ∃ retained : List WAL.Write,
      (retained = [] ∨ retained = batch) ∧ plan.history = history ++ retained := by
    rcases plan.allowed with previous | whole
    · exact ⟨[], .inl rfl, by simpa using previous⟩
    · exact ⟨batch, .inr rfl, whole⟩
  refine ⟨retained, ?_, submissionsAtReturn, ?_, ?_⟩
  · simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, NativeExecutionEvent.writes]
      using historyAtReturn.trans selected
  · simpa [NativeExecutionEvent.reads] using kept
  · intro event member
    obtain rfl := List.mem_singleton.mp member
    exact allowed

/-- The actual source return installs the selected history and exposes the
corresponding uncertain submission and snapshot ledger. -/
def NativeReadPosition.ReopenedLedger
    {heap : Type} {prior : List WAL.Write} {log : List DatabaseSubmissions}
    (current : NativeReadPosition prior log) (history batch retained : List WAL.Write)
    (request : WriteRequest) (input : FilePath) (cause : IO.Error)
    (returned : EStateM.Result IO.Error heap DiskTable) : Prop :=
    ∃ (next : NativeReadPosition history (log ++ [.uncertainBatch batch]))
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      returned = .ok handle.table start.reached ∧
      start.current = ⟨history, log ++ [.uncertainBatch batch], next⟩ ∧
      (⟨prior, log, current⟩ : NativeExecutionPosition).LedgerSuffix
        [.uncertainWriteCrashRecovered request input cause batch retained] start.current ∧
      InstalledClientReplay start.current.submissions start.current.ready.reads start.current.history
        start.current.ready.state.writer.installed start.current.ready.state.session

section

variable {heap stream : Type} {input : FilePath} {view : OpenCloseHeapView heap FileImage}
    {returns : List (FilePath × IO.Error)}
    {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
    {prior : List WAL.Write} {log : List DatabaseSubmissions} {batch : List WAL.Write}
    {current : NativeReadPosition prior log} {first reached : heap}
    {source : RawMarkedOpenInterpreter heap stream}
    {names : heap → FilePath → Option Nat} {visible : heap → Nat → ByteArray}
    {vacant : TryLockObserves (view.files reached).owners current.state.session.directory (.ok true)}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    {ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool}

/-- The actual source return carries the selected history, one uncertain
submission, and the earlier snapshot ledger into the installed table. -/
theorem NativeReadPosition.SelectedWriteRecovery.replaysSelectedLedger
    {target : Target}
    (recovered : current.SelectedWriteRecovery (returns := returns) (input := input) (view := view)
      (batch := batch) (target := target) (reached := reached)
      (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity) source names visible first vacant get set ptrEq)
    (request : WriteRequest) (cause : IO.Error) :
    ∃ (plan : current.SelectedWritePlan batch target (view.files reached).image)
      (retained : List WAL.Write),
      current.ReopenedLedger plan.history batch retained request input cause (source.openTable input reached) := by
  obtain ⟨_, _, _, _, plan, opening, raw, _, _, _, _, _, _, _, _, _, _, returned⟩ := recovered
  obtain ⟨_, next, _, handle, start, _, _, success, atStart, reads, _⟩ := returned
  obtain ⟨retained, ledger⟩ := plan.ledgerAfterReopen start.current
    (congrArg NativeExecutionPosition.history atStart) (congrArg NativeExecutionPosition.submissions atStart)
    ((congrArg (fun position => position.ready.reads) atStart).trans reads) request input cause
  exact ⟨plan, retained, next, handle, start, success, atStart, ledger,
    start.current.ready.readPrefix.guardedReplay⟩

/-- At the old marker the selected history has the original length,
even if additional WAL bytes survived. The very table returned by the
source open carries that history and records the uncertain submission. -/
theorem NativeReadPosition.SelectedWriteRecovery.replaysOldTarget
    (recovered : current.SelectedWriteRecovery (returns := returns) (input := input) (view := view)
      (batch := batch) (target := current.state.writer.target) (reached := reached)
      (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity) source names visible first vacant get set ptrEq)
    (request : WriteRequest) (cause : IO.Error) :
    current.ReopenedLedger prior batch [] request input cause (source.openTable input reached) := by
  obtain ⟨plan, retained, next, handle, start, success, atStart, ledger, replay⟩ :=
    recovered.replaysSelectedLedger request cause
  have history : plan.history = prior ++ retained := by
    simpa only [atStart, List.flatMap_cons, List.flatMap_nil, List.append_nil, NativeExecutionEvent.writes]
      using ledger.history
  have old := plan.oldHistory
  have empty : retained = [] := List.append_cancel_left (by
    simpa only [List.append_nil] using history.symm.trans old)
  have castPosition {before after : List WAL.Write} (eq : before = after)
      (ready : NativeReadPosition before (log ++ [.uncertainBatch batch])) :
      (⟨before, log ++ [.uncertainBatch batch], ready⟩ : NativeExecutionPosition) =
        ⟨after, log ++ [.uncertainBatch batch], eq ▸ ready⟩ := by
    cases eq
    rfl
  exact ⟨old ▸ next, handle, start, success, atStart.trans (castPosition old next), empty ▸ ledger, replay⟩

end

end Alvoki.Storage.DiskSession
