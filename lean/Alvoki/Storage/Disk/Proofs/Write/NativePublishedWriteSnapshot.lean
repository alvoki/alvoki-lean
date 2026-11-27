import Alvoki.Storage.Disk.Proofs.Write.NativeReadyWriteStorage
import Alvoki.Storage.Disk.NativeOpenSnapshotTrace

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)
open Sequential (SnapshotPin SnapshotTable)

/-- The raw write primitives and synchronization references used throughout
an opened handle's sequence of public calls. -/
structure NativeReadyWriteCalls {heap : Type} (opened : NativeOpenedHandle heap) where
  cache : OpenSyncCacheRefs opened.files opened.directory.path
  appender : RawWalAppendCalls heap
  stager : RawWalStageCalls heap
  syncer : RawSyncCalls heap
  lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata
  rename : FilePath → FilePath → EStateM IO.Error heap Unit

abbrev NativeOpenedPosition.readyWriteCalls {heap : Type} {opened : NativeOpenedHandle heap}
    (current : NativeOpenedPosition opened)
    (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
    (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
    (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) : NativeReadyWriteCalls opened :=
  ⟨⟨cache.directory, cache.active, cache.pending, cache.references,
    (congrArg DiskDirectory.path current.directory) ▸ cache.atRoot⟩, appender, stager, syncer, lookup, rename⟩

/-- Public calls and their observed responses. Each constructor has the
error and success types of that method. -/
inductive NativeReturnedCall {heap : Type} (opened : NativeOpenedHandle heap) where
  | write (request : WriteRequest) (result : Except DiskWriteError UInt64)
  | acquire (result : Except IO.Error DiskSnapshotPin)
  | read (pin : NativeOpenedPin opened) (request : SnapshotReadRequest α) (result : Except IO.Error (Option α))

namespace NativeReturnedCall

variable {heap : Type} {opened : NativeOpenedHandle heap}

def pinsAfter (call : NativeReturnedCall opened) (pins : List DiskSnapshotPin) : List DiskSnapshotPin :=
  match call with
  | .acquire (.ok pin) => pins ++ [pin]
  | _ => pins

private def atReturn {ε α : Type} (result : Except ε α) (reached : heap) : EStateM.Result ε heap α :=
  match result with
  | .ok value => .ok value reached
  | .error cause => .error cause reached

/-- Dispatch the request through the same opened phase and fixed primitive
schedules. A read uses a pin issued earlier in the sequence or supplied
at its entry. The reached table still decides whether that pin is active. -/
def Reaches (call : NativeReturnedCall opened) (writes : NativeReadyWriteCalls opened)
    (issuer : opened.LatestIssuer) (pins : List DiskSnapshotPin) (entry reached : heap) : Prop :=
  match call with
  | .write request result =>
    let cache := writes.cache
    request.runOnRawOpenPhase opened.directory writes.lookup (writes.appender.run cache.active)
      (writes.stager.run cache.pending)
      (writes.syncer.group opened.directory.path cache.directory cache.active cache.pending)
      writes.rename opened.phase opened.get opened.set entry = atReturn result reached
  | .acquire result => opened.acquireLatestRaw issuer.val entry = atReturn result reached
  | .read pin request result =>
    pin.raw ∈ pins ∧ opened.readPinRaw pin request entry = atReturn result reached

/-- A public return on this poisoned handle reaches only its ready-phase
guard. The write metadata, snapshot setter and token comparison are
all bypassed. -/
theorem Reaches.heapOfPoisoned {call : NativeReturnedCall opened}
    {writes : NativeReadyWriteCalls opened} {issuer : opened.LatestIssuer}
    {pins : List DiskSnapshotPin} {entry reached : heap}
    (returned : call.Reaches writes issuer pins entry reached)
    (stored : opened.contents entry opened.phase = some .poisoned) : reached = entry := by
  have loaded := opened.phaseEffects.reads entry opened.phase .poisoned stored
  have atError {ε α : Type} {result : Except ε α} {cause : ε}
      (same : EStateM.Result.error cause entry = atReturn result reached) : reached = entry := by
    cases result with
    | error _ => exact (EStateM.Result.error.inj same).2.symm
    | ok _ => cases same
  cases call with
  | write request result =>
    simp only [Reaches] at returned
    rw [request.runOnRawOpenPhase_rejectsPhase _ _ _ _ _ _ _ _ _ loaded rfl] at returned
    exact atError returned
  | acquire result =>
    simp only [Reaches, NativeOpenedHandle.acquireLatestRaw, acquireLatestWith, Bind.bind, EStateM.bind, loaded,
      Phase.installed, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at returned
    exact atError returned
  | read pin request result =>
    obtain ⟨_, read⟩ := returned
    simp only [NativeOpenedHandle.readPinRaw, readSnapshotWith, withLocalHandle, Bind.bind, EStateM.bind, loaded,
      Phase.installed, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at read
    exact atError read

/-- A write that reaches success or reports uncertainty cannot have
entered the phase guard with the handle poisoned. -/
theorem Reaches.writeNotPoisoned
    {writes : NativeReadyWriteCalls opened} {issuer : opened.LatestIssuer}
    {pins : List DiskSnapshotPin} {entry reached : heap}
    {request : WriteRequest} {response : Except DiskWriteError UInt64}
    (returned : (NativeReturnedCall.write request response).Reaches writes issuer pins entry reached)
    (nonRejected : ∀ cause, response ≠ .error (.rejected cause)) :
    opened.contents entry opened.phase ≠ some .poisoned := by
  intro stored
  have loaded := opened.phaseEffects.reads entry opened.phase .poisoned stored
  simp only [Reaches] at returned
  rw [request.runOnRawOpenPhase_rejectsPhase _ _ _ _ _ _ _ _ _ loaded rfl] at returned
  cases response with
  | ok => cases returned
  | error failure =>
    cases failure with
    | rejected cause => exact nonRejected cause rfl
    | commitUnknown => cases returned

end NativeReturnedCall

/-- A returned preflight records the response on the same model table and
pins. If the no-follow check was reached, keep the actual returned heap
and use only that metadata call's local phase-cell frame. -/
theorem NativeOpenedPosition.preflightsReturnedWrite
    {heap : Type} {opened : NativeOpenedHandle heap} (start : NativeOpenedPosition opened)
    (writes : NativeReadyWriteCalls opened) (issuer : opened.LatestIssuer) (pins : List DiskSnapshotPin)
    {request : WriteRequest} (seen : NativeWritePreflightObservation start.current.ready.state request)
    (observes : seen.lookup = fun path => (nativeWriteLookupAt writes.lookup start.reached path).1)
    {reached : heap}
    (returned : (NativeReturnedCall.write (opened := opened) request
      (seen.response.mapError DiskWriteError.rejected)).Reaches writes issuer pins start.reached reached)
    (keepsPhase : let state := start.current.ready.state
      let checkedAt := (nativeWriteLookupAt writes.lookup start.reached
        (opened.directory.file (.walSegment state.writer.installed.activeFirst))).2
      reached ≠ start.reached → seen.ReturnHeap start.reached checkedAt reached →
        opened.contents reached opened.phase = opened.contents start.reached opened.phase) :
    let state := start.current.ready.state
    let checkedAt := (nativeWriteLookupAt writes.lookup start.reached
      (opened.directory.file (.walSegment state.writer.installed.activeFirst))).2
    ∃ next : NativeOpenedPosition opened,
      next.reached = reached ∧ next.current = start.current ∧ next.pins = start.pins ∧
      start.current.LedgerSuffix [.writePreflight request seen.response] next.current ∧
      seen.ReturnHeap start.reached checkedAt reached := by
  intro state checkedAt
  have valid : state.Valid := start.current.ready.readPrefix.refines.1
  have loaded : opened.get opened.phase start.reached = .ok (.ready state.writer.installed) start.reached := by
    have read := opened.phaseEffects.reads start.reached opened.phase state.session.phase start.stored
    simpa only [valid.phase] using read
  obtain ⟨actual, path, preflight⟩ := request.runOnRawOpenPhase_preflight opened.directory writes.lookup
    (writes.appender.run writes.cache.active) (writes.stager.run writes.cache.pending)
    (writes.syncer.group opened.directory.path writes.cache.directory writes.cache.active writes.cache.pending)
    writes.rename opened.phase opened.get opened.set valid seen loaded start.directory observes
  have sameHeap : reached = actual := by
    simp only [NativeReturnedCall.Reaches, preflight] at returned
    cases response : seen.response <;>
      simp only [NativeWritePreflightObservation.resultAt, response, Except.mapError, NativeReturnedCall.atReturn,
        EStateM.Result.ok.injEq, EStateM.Result.error.injEq, true_and] at returned <;>
      exact returned.symm
  have path : seen.ReturnHeap start.reached checkedAt reached := sameHeap.symm ▸ path
  have stored : opened.contents reached opened.phase = some state.session.phase := by
    by_cases same : reached = start.reached
    · exact same.symm ▸ start.stored
    · exact (keepsPhase same path).symm ▸ start.stored
  exact ⟨⟨start.current, reached, start.directory, stored, start.pins⟩, rfl, rfl, rfl,
    (NativeExecutionStep.writePreflight start.current seen (start.current.ready.preflightsWrite seen)).ledgerSuffix,
    path⟩

/-- An ordered sequence of source returns. Each call starts with the
actual preceding heap and the pin values the preceding calls returned. -/
inductive NativeReturnedCalls {heap : Type} {opened : NativeOpenedHandle heap}
    (writes : NativeReadyWriteCalls opened) (issuer : opened.LatestIssuer) :
    heap → List DiskSnapshotPin → List (NativeReturnedCall opened) → heap → Prop where
  | empty : NativeReturnedCalls writes issuer entry pins [] entry
  | cons (returned : call.Reaches writes issuer pins entry next)
      (later : NativeReturnedCalls writes issuer next (call.pinsAfter pins) calls last) :
      NativeReturnedCalls writes issuer entry pins (call :: calls) last

/-- Every return in a sequence on the same poisoned handle preserves
the precise heap and the original poisoned phase cell. -/
theorem NativeReturnedCalls.fromPoisoned {heap : Type} {opened : NativeOpenedHandle heap}
    {writes : NativeReadyWriteCalls opened} {issuer : opened.LatestIssuer}
    {entry last : heap} {pins : List DiskSnapshotPin} {calls : List (NativeReturnedCall opened)}
    (returned : NativeReturnedCalls writes issuer entry pins calls last)
    (stored : opened.contents entry opened.phase = some .poisoned) :
    last = entry ∧ opened.contents last opened.phase = some .poisoned := by
  induction returned with
  | empty => exact ⟨rfl, stored⟩
  | cons call _ rest =>
    have same := call.heapOfPoisoned stored
    obtain ⟨lastAtNext, lastPoisoned⟩ := rest (same.symm ▸ stored)
    exact ⟨lastAtNext.trans same, lastPoisoned⟩

theorem NativeReturnedCalls.append {heap : Type} {opened : NativeOpenedHandle heap}
    {writes : NativeReadyWriteCalls opened} {issuer : opened.LatestIssuer}
    {entry middle last : heap} {pins : List DiskSnapshotPin}
    {earlier later : List (NativeReturnedCall opened)}
    (first : NativeReturnedCalls writes issuer entry pins earlier middle)
    (second : NativeReturnedCalls writes issuer middle
      (earlier.foldl (fun known call => call.pinsAfter known) pins) later last) :
    NativeReturnedCalls writes issuer entry pins (earlier ++ later) last := by
  induction first with
  | empty => exact second
  | cons returned _ ih => exact .cons returned (ih second)

/-- Splitting a source run retains the actual intervening heap and
the pins passed to the next public call. -/
theorem NativeReturnedCalls.splitAppend {heap : Type} {opened : NativeOpenedHandle heap}
    {writes : NativeReadyWriteCalls opened} {issuer : opened.LatestIssuer}
    {entry reached : heap} {pins : List DiskSnapshotPin}
    {earlier later : List (NativeReturnedCall opened)}
    (executed : NativeReturnedCalls writes issuer entry pins (earlier ++ later) reached) :
    ∃ middle, NativeReturnedCalls writes issuer entry pins earlier middle ∧
      NativeReturnedCalls writes issuer middle
        (earlier.foldl (fun known call => call.pinsAfter known) pins) later reached := by
  induction earlier generalizing entry pins with
  | nil => exact ⟨entry, .empty, executed⟩
  | cons _ _ ih =>
    cases executed with
    | cons returned remainder =>
      obtain ⟨middle, before, after⟩ := ih remainder
      exact ⟨middle, .cons returned before, after⟩

/-- Follow the already prescribed public calls with a latest acquisition
and a read of precisely that return, on the same opened handle. -/
def NativeOpenedHandle.ReturnsLatestAfter {heap : Type} (opened : NativeOpenedHandle heap)
    (writes : NativeReadyWriteCalls opened) (prior : List (NativeReturnedCall opened))
    (request : SnapshotReadRequest α) (sequence : UInt64) (response : Option α) (entry reached : heap) : Prop :=
  ∃ (issuer : opened.LatestIssuer) (pin : NativeOpenedPin opened),
    pin.raw.sequence = sequence ∧
    NativeReturnedCalls writes issuer entry [] (prior ++ [.acquire (.ok pin.raw), .read pin request (.ok response)])
      reached

/-- Derive the client ledger of an observed write and snapshot on the same
table. The write's reached position supplies the phase and token that the
snapshot calls actually use. The existing ledger may already include a
recovery on an earlier handle. -/
theorem NativeOpenedPosition.acknowledgesAndReadsLatest
    {heap image : Type} {opened : NativeOpenedHandle heap} (current : NativeOpenedPosition opened)
    {origin : NativeExecutionPosition} {earlier : List NativeExecutionEvent}
    (incoming : origin.LedgerSuffix earlier current.current)
    (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
    (view : OpenCloseHeapView heap image)
    (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : heap → CheckpointStorageObservation)
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {sequence : UInt64} {reached : heap}
    (nonempty : request.rows ≠ [])
    (entry : current.WriteStorageEntry view cache (observe current.reached) (inodes current.reached).visible)
    (seen : current.ObservesPublishedWrite appender stager syncer view cache inodes runs observe
      inode buffered request lookup rename sequence reached)
    (read : SnapshotReadRequest α)
    (token : opened.ObservesSnapshotToken reached) :
    let directory := current.current.ready.state.session.directory
    opened.table.UsesOpenWriteSchedules directory opened.files opened.phase ∧
    request.runOnRawOpenPhase directory lookup (appender.run cache.active) (stager.run cache.pending)
      (syncer.group directory.path cache.directory cache.active cache.pending)
      rename opened.phase opened.get opened.set current.reached = .ok sequence reached ∧
    ∃ (batch : List WAL.Write) (table : PackedTable) (written last : NativeOpenedPosition opened) (reference : SnapshotTable UInt64)
      (events : List NativeExecutionEvent),
      prepareBatch current.current.ready.state.writer.installed.table request.rows = some (batch, table) ∧
      sequence = table.committed ∧ written.reached = reached ∧
      NativeOpenedTrace written [.acquire, .readAt written.pins.length read] events last ∧
      origin.LedgerSuffix (earlier ++ .acknowledged request batch :: events) last.current ∧
      SnapshotWalReplay .empty (current.current.history ++ batch) reference ∧
      (∀ observation ∈ last.current.ready.reads, observation.agrees reference) ∧
      opened.ReturnsLatestAfter (current.readyWriteCalls cache appender stager syncer lookup rename)
        [.write request (.ok sequence)] read sequence (some (read.replay reference sequence))
        current.reached last.reached := by
  obtain ⟨issuer⟩ := opened.hasLatestIssuer
  obtain ⟨schedule, returned, batch, table, written, _, prepared, number, reachedWrite, _, installed, wrote, _, _, _, _⟩ :=
    current.acknowledgesObservedWrite appender stager syncer view cache inodes runs observe inode buffered
      request lookup rename nonempty entry seen
  obtain ⟨pin, acquired, last, reference, _, _, _, readReturned, calls, _, replay, agrees, acquire, pinSequence⟩ :=
    written.acquiresAndReadsLatest issuer rfl read (reachedWrite ▸ token)
  have history : written.current.history = current.current.history ++ batch := by
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, NativeExecutionEvent.writes] using wrote.history
  refine ⟨schedule, returned, batch, table, written, last, reference, _, prepared, number, reachedWrite, calls,
    incoming.append (wrote.append calls.common.ledgerSuffix), history ▸ replay, agrees, ?_⟩
  obtain ⟨_, response, _, raw, event, _, _⟩ := readReturned
  cases event
  refine ⟨issuer, pin, ?_, ?_⟩
  · simpa only [installed, ← number] using pinSequence
  · let writes := current.readyWriteCalls cache appender stager syncer lookup rename
    have wrote : NativeReturnedCalls writes issuer current.reached [] [.write request (.ok sequence)] reached := by
      refine .cons ?_ .empty
      simpa only [writes, NativeReturnedCall.Reaches, NativeReturnedCall.atReturn, NativeOpenedPosition.readyWriteCalls,
        ← current.directory] using returned
    refine wrote.append (.cons (next := acquired.reached) (reachedWrite ▸ acquire)
      (.cons (next := last.reached) ⟨by simp [NativeReturnedCall.pinsAfter], ?_⟩ .empty))
    simpa only [NativeReturnedCall.atReturn, NativeOpenedHandle.readPinRaw, installed, ← number] using raw

end Alvoki.Storage.DiskSession
