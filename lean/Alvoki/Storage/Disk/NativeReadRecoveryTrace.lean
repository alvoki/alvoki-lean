import Alvoki.Storage.Disk.NativeReadyPowerLoss

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open Sequential (SnapshotPin)
open scoped List

/-- The exact open that started the current session and its reached read
prefix. The acknowledged history stays fixed throughout this trace. -/
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
  | restart

def NativeReadRecoveryEvent.responses : NativeReadRecoveryEvent → List RecordedSnapshotRead
  | .read response => [response]
  | .restart => []

/-- A read uses the exact local session and adds its observed response.
A restart uses the selected checkpoint/WAL image from one crash and the
same chronological installer that supplies the fresh ready readPrefix. -/
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
      (target : next.writer.target = current.state.writer.target)
      (checkpoint : next.writer.checkpoint = current.state.writer.checkpoint)
      (durable : next.writer.published.durable = current.state.writer.published.durable) :
      NativeReadRecoveryStep current .restart (current.afterRestart observed.run next readPrefix)

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
    ∃ next, NativeReadRecoveryStep current .restart next := by
  obtain ⟨lost, _, layout, selected, observed, next, readPrefix, _, _, _, _, _, _, _, _, _, _, target, checkpoint, durable, _⟩ :=
    current.readPrefix.restartsAfterPowerLoss crash observe
  exact ⟨_, .restart current crash lost layout selected observed next readPrefix target checkpoint durable⟩

theorem NativeReadRecoveryStep.frames
    (step : NativeReadRecoveryStep (history := history) (log := log) before event after) :
    after.reads = before.reads ++ event.responses ∧ after.state.writer.target = before.state.writer.target ∧
    after.state.writer.checkpoint = before.state.writer.checkpoint ∧
    after.state.writer.published.durable = before.state.writer.published.durable := by
  cases step with
  | read => exact ⟨rfl, rfl, rfl, rfl⟩
  | restart _ _ _ _ _ _ _ _ target checkpoint durable => exact ⟨by simp [NativeReadRecoveryEvent.responses,
      NativeReadPosition.afterRestart], target, checkpoint, durable⟩

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
    last.state.writer.target = start.state.writer.target ∧
    last.state.writer.checkpoint = start.state.writer.checkpoint ∧
    last.state.writer.published.durable = start.state.writer.published.durable := by
  induction run with
  | empty => exact ⟨by simp, rfl, rfl, rfl⟩
  | step _ reached ih =>
    obtain ⟨observedReads, target, checkpoint, durable⟩ := reached.frames
    refine ⟨?_, target.trans ih.2.1, checkpoint.trans ih.2.2.1, durable.trans ih.2.2.2⟩
    rw [observedReads, ih.1]
    simp [List.append_assoc]

/-- One abstract replay accounts for the accumulated native responses
and supported reads in the last returned session. -/
theorem NativeReadRecoveryTrace.keyValueRefinement
    (run : NativeReadRecoveryTrace (history := history) (log := log) start events last) :
    last.reads = start.reads ++ events.flatMap NativeReadRecoveryEvent.responses ∧
    InstalledClientReplay log last.reads history last.state.writer.installed last.state.session :=
  ⟨run.frames.1, last.readPrefix.guardedReplay⟩

end Alvoki.Storage.DiskSession
