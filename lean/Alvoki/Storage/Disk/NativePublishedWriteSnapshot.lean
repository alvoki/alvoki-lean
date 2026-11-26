import Alvoki.Storage.Disk.NativeReadyWriteStorage
import Alvoki.Storage.Disk.NativeOpenSnapshotTrace

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)
open Sequential (SnapshotPin SnapshotTable)

/-- One source call with its actual public response. Its interpretation
does not refer to a native writer, a replay, or a correctness report. -/
structure NativeReturnedCall (heap : Type) where
  Error : Type
  Value : Type
  run : EStateM Error heap Value
  result : Except Error Value

def NativeReturnedCall.Reaches {heap : Type} (call : NativeReturnedCall heap)
    (entry reached : heap) : Prop :=
  call.run entry = match call.result with
    | .ok value => .ok value reached
    | .error cause => .error cause reached

/-- An ordered sequence of source returns. A later call starts at the
exact returned heap, including when the preceding call returned an error. -/
inductive NativeReturnedCalls {heap : Type} : heap → List (NativeReturnedCall heap) → heap → Prop where
  | empty : NativeReturnedCalls entry [] entry
  | cons (returned : call.Reaches entry next) (later : NativeReturnedCalls next calls last) :
      NativeReturnedCalls entry (call :: calls) last

theorem NativeReturnedCalls.append {heap : Type} {entry middle last : heap}
    {earlier later : List (NativeReturnedCall heap)} (first : NativeReturnedCalls entry earlier middle)
    (second : NativeReturnedCalls middle later last) : NativeReturnedCalls entry (earlier ++ later) last := by
  induction first with
  | empty => exact second
  | cons returned _ ih => exact .cons returned (ih second)

abbrev NativeOpenedHandle.acquireLatestRaw {heap : Type} (opened : NativeOpenedHandle heap)
    (issue : SnapshotPin → DiskSnapshotPin) : EStateM IO.Error heap DiskSnapshotPin :=
  let load : EStateM IO.Error heap Installed := do (← opened.get opened.phase).installed
  acquireLatestWith load (acquireSnapshotWith load (opened.set opened.phase) issue)

abbrev NativeOpenedHandle.readPinRaw {heap : Type} (opened : NativeOpenedHandle heap)
    (pin : NativeOpenedPin opened) (request : SnapshotReadRequest α) :
    EStateM IO.Error heap (Option α) :=
  readSnapshotWith (do (← opened.get opened.phase).installed)
    (opened.ptrEq opened.token opened.token) (request.read pin.localPin.handle)

noncomputable abbrev NativeReturnedCall.writeOnPhase {heap : Type} (opened : NativeOpenedHandle heap)
    (directory : DiskDirectory) (cache : OpenSyncCacheRefs opened.files directory.path)
    (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
    (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) (result : Except DiskWriteError UInt64) :
    NativeReturnedCall heap :=
  ⟨DiskWriteError, UInt64, request.runOnRawOpenPhase directory lookup (appender.run cache.active)
    (stager.run cache.pending) (syncer.group directory.path cache.directory cache.active cache.pending)
    rename opened.phase opened.get opened.set, result⟩

/-- Extend a sequence of source returns with an acquisition and a read
using that exact returned pin. The response and sequence here are
observed public values. -/
def NativeOpenedHandle.ReturnsLatestAfter {heap : Type} (opened : NativeOpenedHandle heap)
    (prior : List (NativeReturnedCall heap)) (request : SnapshotReadRequest α)
    (sequence : UInt64) (response : Option α) (entry reached : heap) : Prop :=
  ∃ (issue : SnapshotPin → DiskSnapshotPin) (pin : NativeOpenedPin opened),
    opened.table.acquire = acquireLatestWith (m := IO) (do (← opened.phase.get).installed)
      (acquireSnapshotWith (do (← opened.phase.get).installed) opened.phase.set issue) ∧
    (match request with
      | .lookup key => opened.table.lookup pin.raw.handle key = readSnapshotWith (m := IO)
          (do (← opened.phase.get).installed) (opened.token.ptrEq opened.token)
          (fun table => table.lookup pin.localPin.handle key)
      | .range lo hi => opened.table.range pin.raw.handle lo hi = readSnapshotWith (m := IO)
          (do (← opened.phase.get).installed) (opened.token.ptrEq opened.token)
          (fun table => table.range pin.localPin.handle lo hi)) ∧
    pin.raw.sequence = sequence ∧
    NativeReturnedCalls entry (prior ++ [⟨IO.Error, DiskSnapshotPin, opened.acquireLatestRaw issue, .ok pin.raw⟩,
      ⟨IO.Error, Option α, opened.readPinRaw pin request, .ok response⟩]) reached

/-- The token comparison is observed after the actual acquisition call
on this handle's phase cell. -/
def NativeOpenedHandle.ObservesSnapshotToken {heap : Type}
    (opened : NativeOpenedHandle heap) (start : heap) : Prop :=
  ∀ (issue : SnapshotPin → DiskSnapshotPin),
    opened.table.acquire = acquireLatestWith (m := IO) (do (← opened.phase.get).installed)
      (acquireSnapshotWith (do (← opened.phase.get).installed) opened.phase.set issue) →
    ∀ {pin : DiskSnapshotPin} {reached : heap},
      opened.acquireLatestRaw issue start = .ok pin reached →
      opened.ptrEq opened.token opened.token reached = .ok true reached

/-- Derive the client ledger of an observed write and snapshot on the same
table. The write's reached position supplies the phase and token that the
snapshot calls actually use. -/
theorem NativeOpenedPosition.acknowledgesAndReadsLatest
    {heap image : Type} {opened : NativeOpenedHandle heap} (current : NativeOpenedPosition opened)
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
      current.current.LedgerSuffix (.acknowledged request batch :: events) last.current ∧
      SnapshotWalReplay .empty (current.current.history ++ batch) reference ∧
      (∀ observation ∈ last.current.ready.reads, observation.agrees reference) ∧
      opened.ReturnsLatestAfter
        [.writeOnPhase opened directory cache appender stager syncer request lookup rename (.ok sequence)]
        read sequence (some (read.replay reference sequence)) current.reached last.reached := by
  obtain ⟨schedule, returned, batch, table, written, _, prepared, number, reachedWrite, _, installed, wrote, _, _⟩ :=
    current.acknowledgesObservedWrite appender stager syncer view cache inodes runs observe inode buffered
      request lookup rename nonempty entry seen
  obtain ⟨pin, acquired, last, reference, issued, compared, acquireReturned, readReturned, calls, _, replay, agrees⟩ :=
    written.acquiresAndReadsLatest read (fun acquired => by
      obtain ⟨issue, pin, _, source, _, _, returned, _⟩ := acquired.returned
      exact token issue source (reachedWrite ▸ returned))
  have history : written.current.history = current.current.history ++ batch := by
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, NativeExecutionEvent.writes] using wrote.history
  refine ⟨schedule, returned, batch, table, written, last, reference, _, prepared, number, reachedWrite, calls,
    wrote.append calls.common.ledgerSuffix, history ▸ replay, agrees, ?_⟩
  obtain ⟨issue, actual, _, source, _, _, acquire, _, _, _, _, pinSequence, _, _, pins, _⟩ := acquireReturned
  have pinEq : actual = pin := by
    simpa [pins] using issued
  subst actual
  obtain ⟨readSource, response, _, raw, event, _, _⟩ := readReturned
  cases event
  refine ⟨issue, pin, source, ?_, ?_, ?_⟩
  · cases read <;> exact readSource
  · simpa only [installed, ← number] using pinSequence
  · have wrote : NativeReturnedCalls current.reached
        [.writeOnPhase opened current.current.ready.state.session.directory cache appender stager syncer
          request lookup rename (.ok sequence)] reached := .cons returned .empty
    refine wrote.append
      (.cons (next := acquired.reached) (reachedWrite ▸ acquire) (.cons (next := last.reached) ?_ .empty))
    simpa only [NativeReturnedCall.Reaches, NativeOpenedHandle.readPinRaw, installed, ← number] using raw

end Alvoki.Storage.DiskSession
