import Alvoki.Storage.Disk.NativeReadyWriteStorage
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

end NativeReturnedCall

/-- An ordered sequence of source returns. Each call starts with the
actual preceding heap and the pin values the preceding calls returned. -/
inductive NativeReturnedCalls {heap : Type} {opened : NativeOpenedHandle heap}
    (writes : NativeReadyWriteCalls opened) (issuer : opened.LatestIssuer) :
    heap → List DiskSnapshotPin → List (NativeReturnedCall opened) → heap → Prop where
  | empty : NativeReturnedCalls writes issuer entry pins [] entry
  | cons (returned : call.Reaches writes issuer pins entry next)
      (later : NativeReturnedCalls writes issuer next (call.pinsAfter pins) calls last) :
      NativeReturnedCalls writes issuer entry pins (call :: calls) last

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
      opened.ReturnsLatestAfter (current.readyWriteCalls cache appender stager syncer lookup rename)
        [.write request (.ok sequence)] read sequence (some (read.replay reference sequence))
        current.reached last.reached := by
  obtain ⟨issuer⟩ := opened.hasLatestIssuer
  obtain ⟨schedule, returned, batch, table, written, _, prepared, number, reachedWrite, _, installed, wrote, _, _⟩ :=
    current.acknowledgesObservedWrite appender stager syncer view cache inodes runs observe inode buffered
      request lookup rename nonempty entry seen
  obtain ⟨pin, acquired, last, reference, _, _, _, readReturned, calls, _, replay, agrees, acquire, pinSequence⟩ :=
    written.acquiresAndReadsLatest issuer rfl read (reachedWrite ▸ token)
  have history : written.current.history = current.current.history ++ batch := by
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, NativeExecutionEvent.writes] using wrote.history
  refine ⟨schedule, returned, batch, table, written, last, reference, _, prepared, number, reachedWrite, calls,
    wrote.append calls.common.ledgerSuffix, history ▸ replay, agrees, ?_⟩
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
