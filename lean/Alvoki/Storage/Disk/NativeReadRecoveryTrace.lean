import Alvoki.Storage.Disk.NativeReadyPowerLoss
import Alvoki.Storage.Disk.NativeReadyWrite

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open Sequential (SnapshotPin)
open scoped List

/-- The normalized state from a successful open or acknowledged write,
with the reads since that state. The committed history stays fixed
through this local read prefix. -/
structure NativeReadPosition (history : List WAL.Write) (log : List DatabaseSubmissions) where
  opened : EStateM.Result IO.Error CensusOpenState SegmentedSession
  initial : NativeReadyState
  state : NativeReadyState
  reads : List RecordedSnapshotRead
  readPrefix : NativeReadyReadPrefix opened initial history log reads state

namespace NativeReadPosition

private def afterRead (current : NativeReadPosition history log) (table : PackedTable)
    (response : RecordedSnapshotRead)
    (readPrefix : NativeReadyReadPrefix current.opened current.initial history log (current.reads ++ [response]) (current.state.withTable table)) :
    NativeReadPosition history log :=
  { current with state := current.state.withTable table, reads := current.reads ++ [response], readPrefix := readPrefix }

private def afterRestart (current : NativeReadPosition history log)
    (result : EStateM.Result IO.Error CensusOpenState SegmentedSession)
    (next : NativeReadyState) (readPrefix : NativeReadyReadPrefix result next history log current.reads next) :
    NativeReadPosition history log :=
  ⟨result, next, next, current.reads, readPrefix⟩

end NativeReadPosition

inductive NativeReadRecoveryEvent where
  | read (response : RecordedSnapshotRead)
  | restart (input : FilePath)

def NativeReadRecoveryEvent.responses : NativeReadRecoveryEvent → List RecordedSnapshotRead
  | .read response => [response]
  | .restart _ => []

/-- The directory, lock object and selected checkpoint stay fixed
through local reads and each admitted quiet restart. -/
structure NativeReadRecoveryFrame (before after : NativeReadyState) : Prop where
  directory : after.session.directory = before.session.directory
  directoryInode : after.census.inode after.directorySlot.description =
    before.census.inode before.directorySlot.description
  lockInode : after.census.inode after.owner.description = before.census.inode before.owner.description
  target : after.writer.target = before.writer.target
  checkpoint : after.writer.checkpoint = before.writer.checkpoint
  durable : after.writer.published.durable = before.writer.published.durable

private theorem NativeReadRecoveryFrame.trans (earlier : NativeReadRecoveryFrame first middle)
    (later : NativeReadRecoveryFrame middle last) : NativeReadRecoveryFrame first last :=
  ⟨later.directory.trans earlier.directory, later.directoryInode.trans earlier.directoryInode,
    later.lockInode.trans earlier.lockInode, later.target.trans earlier.target,
    later.checkpoint.trans earlier.checkpoint, later.durable.trans earlier.durable⟩

/-- A read uses the exact local session and adds its observed response.
A restart uses the selected checkpoint/WAL image from one crash and the
same chronological installer that supplies the fresh ready prefix. -/
inductive NativeReadRecoveryStep : NativeReadPosition history log → NativeReadRecoveryEvent → NativeReadPosition history log → Prop where
  | read (current : NativeReadPosition history log) (request : SnapshotReadRequest α)
      (snapshot : UInt64) (pin : SnapshotPin) (table : PackedTable) (response : α)
      (acquired : current.state.session.runAcquireAt snapshot =
        .ok (some (current.state.session.sessionRef, pin)) (current.state.withTable table).session)
      (returned : (current.state.withTable table).session.runSnapshotRead true (request.read pin.handle) =
        .ok (some response) (current.state.withTable table).session)
      (readPrefix : NativeReadyReadPrefix current.opened current.initial history log
        (current.reads ++ [request.record snapshot response]) (current.state.withTable table)) :
      NativeReadRecoveryStep current (.read (request.record snapshot response))
        (current.afterRead table (request.record snapshot response) readPrefix)
  | restart (current : NativeReadPosition history log) (crash : NativeReadyQuietCrash current.state)
      (lost : BoundedReopenTrace current.state.session.directory (· = current.state.writer.target) current.state.files crash.retry)
      {input : FilePath} (layout : CanonicalKeeperLayout crash.retry.image current.state.writer.history)
      (selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
        crash.retry.image.directory.active.manifest current.state.writer.checkpoint)
      (observed : NativeReadyRestartReads crash input layout selected) (next : NativeReadyState)
      (readPrefix : NativeReadyReadPrefix observed.run next history log current.reads next)
      (owner : next.owner = observed.opening.admission.owner)
      (directorySlot : next.directorySlot = observed.opening.admission.cached)
      (cache : next.cache = observed.opening.admission.cache)
      (census : next.census = observed.opening.finish.census)
      (sessionRef : next.session.sessionRef ≠ current.state.session.sessionRef)
      (phaseRef : next.session.phaseRef ≠ current.state.session.phaseRef)
      (frame : NativeReadRecoveryFrame current.state next) :
      NativeReadRecoveryStep current (.restart input) (current.afterRestart observed.run next readPrefix)

/-- The next supported acquisition and read derive an actual result and
extend the reached ready prefix. -/
theorem NativeReadPosition.readAt (current : NativeReadPosition history log) (snapshot : UInt64)
    (floor : current.state.writer.installed.table.pins.floor ≤ snapshot)
    (committed : snapshot ≤ current.state.writer.installed.table.committed)
    (request : SnapshotReadRequest α) : ∃ next response,
      NativeReadRecoveryStep current (.read (request.record snapshot response)) next := by
  obtain ⟨reference, pin, table, _, acquired, returned, readPrefix, _⟩ :=
    current.readPrefix.readAt snapshot floor committed request
  exact ⟨_, _, .read current request snapshot pin table (request.replay reference snapshot) acquired returned readPrefix⟩

/-- Report the primitive events of one healthy aligned reopen against
the observed quiet power-loss image. The existing replay derives the
selected layout and checkpoint before the native callbacks are used. -/
theorem NativeReadPosition.restart (current : NativeReadPosition history log) (crash : NativeReadyQuietCrash current.state)
    {input : FilePath}
    (observe : ∀ layout : CanonicalKeeperLayout crash.retry.image current.state.writer.history,
      layout.target = current.state.writer.target → Prepared crash.retry.image layout.target layout.plan →
      ∀ selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
        crash.retry.image.directory.active.manifest current.state.writer.checkpoint,
      Nonempty (NativeReadyRestartReads crash input layout selected)) :
    ∃ next, NativeReadRecoveryStep current (.restart input) next := by
  obtain ⟨lost, _, layout, selected, observed, next, readPrefix, directory, owner, directorySlot, cache, census,
    sessionRef, phaseRef, lockObject, directoryObject, _, target, checkpoint, durable, _⟩ :=
    current.readPrefix.restartsAfterPowerLoss crash observe
  exact ⟨_, .restart current crash lost layout selected observed next readPrefix owner directorySlot cache census
    sessionRef phaseRef ⟨directory, directoryObject, lockObject, target, checkpoint, durable⟩⟩

theorem NativeReadRecoveryStep.frames
    (step : NativeReadRecoveryStep (history := history) (log := log) before event after) :
    after.reads = before.reads ++ event.responses ∧ NativeReadRecoveryFrame before.state after.state := by
  cases step with
  | read => exact ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  | restart _ _ _ _ _ _ _ _ _ _ _ _ _ _ frame =>
    exact ⟨by simp [NativeReadRecoveryEvent.responses, NativeReadPosition.afterRestart], frame⟩

/-- Arbitrary finite interleavings in this scoped execution share one
history and accumulate one ordered read ledger across all sessions. -/
inductive NativeReadRecoveryTrace (start : NativeReadPosition history log) :
    List NativeReadRecoveryEvent → NativeReadPosition history log → Prop where
  | empty : NativeReadRecoveryTrace start [] start
  | step (prior : NativeReadRecoveryTrace start events before) (reached : NativeReadRecoveryStep before event after) :
      NativeReadRecoveryTrace start (events ++ [event]) after

theorem NativeReadRecoveryTrace.frames
    (run : NativeReadRecoveryTrace (history := history) (log := log) start events last) :
    last.reads = start.reads ++ events.flatMap NativeReadRecoveryEvent.responses ∧
    NativeReadRecoveryFrame start.state last.state := by
  induction run with
  | empty => exact ⟨by simp, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  | step _ reached ih =>
    obtain ⟨observedReads, frame⟩ := reached.frames
    refine ⟨?_, ih.2.trans frame⟩
    rw [observedReads, ih.1]
    simp [List.append_assoc]

/-- One abstract replay accounts for the accumulated native responses
and supported reads in the last returned session. -/
theorem NativeReadRecoveryTrace.keyValueRefinement
    (run : NativeReadRecoveryTrace (history := history) (log := log) start events last) :
    last.reads = start.reads ++ events.flatMap NativeReadRecoveryEvent.responses ∧
    NativeReadRecoveryFrame start.state last.state ∧
    InstalledClientReplay log last.reads history last.state.writer.installed last.state.session :=
  ⟨run.frames.1, run.frames.2, last.readPrefix.guardedReplay⟩

/-- A confirmed native write advances the history and preserves every
previously recorded read at its original committed snapshot. Project its
actual reached ready state to the next read and recovery trace. -/
theorem NativeReadPosition.acknowledgesWrite (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} (observed : NativeReadyWriteReport prepared)
    (request : WriteRequest) (rows : request.rows = prepared.rows) :
    ∃ target, ∃ next : NativeReadPosition (history ++ prepared.batch) (log ++ [.acknowledgedBatch prepared.batch]),
      let reached := observed.next target
      observed.calls.run request current.state.session.directory current.state.writer =
        .ok prepared.table.committed (reached.session.phase, ⟨(reached.cache, prepared.settled), reached.files.owners⟩) ∧
      next.state = reached ∧ next.initial = reached ∧ next.reads = current.reads ∧
      next.opened = .ok reached.session (reached.census, reached.files) ∧
      next.state.session.sessionRef = current.state.session.sessionRef ∧
      next.state.writer.history = history ++ prepared.batch ∧
      InstalledClientReplay (log ++ [.acknowledgedBatch prepared.batch]) current.reads
        (history ++ prepared.batch) next.state.writer.installed next.state.session := by
  obtain ⟨valid, beforeHistory, pending⟩ := current.readPrefix.refines
  obtain ⟨target, _, ready, returned, extended, _, sameToken, _, _⟩ := observed.acknowledges valid request rows
  let reached := observed.next target
  have nextHistory : reached.writer.history = history ++ prepared.batch :=
    extended.trans (congrArg (· ++ prepared.batch) beforeHistory)
  have ordered : WAL.OrdinalsFrom 1 (history ++ prepared.batch) :=
    nextHistory ▸ ready.retained.resumed.ordered
  obtain ⟨replayed, bounded⟩ := pending.appendAcknowledged current.readPrefix.readsBounded ordered
  let next : NativeReadPosition (history ++ prepared.batch) (log ++ [.acknowledgedBatch prepared.batch]) :=
    ⟨.ok reached.session (reached.census, reached.files), reached, reached, current.reads,
      .installed rfl ready nextHistory replayed bounded⟩
  exact ⟨target, next, returned, rfl, rfl, rfl, rfl, sameToken, nextHistory, next.readPrefix.guardedReplay⟩

end Alvoki.Storage.DiskSession
