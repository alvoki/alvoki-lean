import Alvoki.Storage.Disk.NativeExecutionPendingClose

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WAL.Boundary

/-- A local unlock returned an error at the exact poisoned write
state. By the close schedule, no cache clear happened in that call. -/
structure NativePendingCloseError {history : List WAL.Write} {log : List DatabaseSubmissions}
    {current : NativeReadPosition history log} (pending : NativePendingWrite current) where
  close : NativePendingClose pending
  cause : IO.Error
  failed : close.report.result = .error cause

namespace NativePendingCloseError

variable {current : NativeReadPosition history log} {pending : NativePendingWrite current}

theorem returns (attempt : NativePendingCloseError pending) :
    attempt.close.report.run = .error attempt.cause pending.poisoned ∧
    attempt.close.reached = pending.poisoned ∧ attempt.close.files = pending.files ∧
    ¬ TryLockObserves attempt.close.files.owners current.state.session.directory (.ok true) := by
  have returned := attempt.close.returns
  rw [attempt.failed] at returned
  exact ⟨by simpa only [returned.2.1] using returned.1,
    returned.2.1, returned.2.2.2.1, returned.2.2.2.2.2⟩

/-- Reports are supplied in attempted order. Each exact reached error
state is the start of the next call, with no intervening release. -/
theorem trace (attempts : List (NativePendingCloseError pending)) :
    CachedCloseFailureTrace current.state.session.directory current.state.session.descriptor pending.poisoned
      (attempts.map (·.cause)) pending.poisoned := by
  induction attempts with
  | nil => exact .nil
  | cons attempt _ prior => exact .cons attempt.close.report attempt.returns.1 prior

end NativePendingCloseError

/-- Primitive callbacks for a successful explicit close after the
reported failures, followed by one admitted marked open. The open
uses the census left by that close and the same released write files. -/
structure NativePendingCloseRetryOpen {history : List WAL.Write} {log : List DatabaseSubmissions}
    {current : NativeReadPosition history log} (pending : NativePendingWrite current) (input : FilePath) where
  attempts : List (NativePendingCloseError pending)
  close : NativePendingClose pending
  unlocked : close.report.result = .ok ()
  observe : pending.write.ReleasedMarkedReports input close.report.finished.descriptors
    (close.report.bindings (current.state.session.directory.file .lock))

namespace NativePendingCloseRetryOpen

variable {current : NativeReadPosition history log} {pending : NativePendingWrite current} {input : FilePath}

/-- The observed successful retry clears exactly the three cache roles.
It releases the same failed write projection used for admission. -/
theorem releases (seen : NativePendingCloseRetryOpen pending input) :
    CachedCloseFailureTrace current.state.session.directory current.state.session.descriptor pending.poisoned
      (seen.attempts.map (·.cause)) pending.poisoned ∧
    seen.close.report.run = .ok () seen.close.report.finished ∧
    seen.close.report.finished.phase = .closed ∧
    seen.close.report.finished.files =
      ⟨(⟨none, none, []⟩, pending.write.failure.failed), pending.write.failure.released.owners⟩ ∧
    seen.close.report.finished.descriptors = pending.poisoned.descriptors.afterDrops
      (seen.close.report.drops .active ++ seen.close.report.drops .pending ++ seen.close.report.drops .directory) ∧
    seen.close.files = pending.write.failure.released ∧
    TryLockObserves seen.close.files.owners current.state.session.directory (.ok true) := by
  have returned := seen.close.returns
  rw [seen.unlocked] at returned
  exact ⟨NativePendingCloseError.trace seen.attempts, by
    simpa only [NativePendingClose.reached, seen.unlocked] using returned⟩

end NativePendingCloseRetryOpen

/-- The exact successor uses the original diagnostic and one uncertain
write receipt. A close failure is a separate response and adds no write
or read to that ledger. -/
structure NativePendingCloseRetryContinuation {history : List WAL.Write} {log : List DatabaseSubmissions}
    {current : NativeReadPosition history log} {pending : NativePendingWrite current} {input : FilePath}
    (seen : NativePendingCloseRetryOpen pending input) (retained : List WAL.Write)
    (next : NativeReadPosition (history ++ retained) pending.submissions) : Prop where
  writeReturned : pending.write.returnedAt pending.cache
  failed : CachedCloseFailureTrace current.state.session.directory current.state.session.descriptor pending.poisoned
    (seen.attempts.map (·.cause)) pending.poisoned
  closed : seen.close.report.run = .ok () seen.close.report.finished
  released : seen.close.files = pending.write.failure.released
  wholeOrNone : retained = [] ∨ retained = pending.write.failure.batch
  reads : next.reads = current.reads
  sameDirectory : next.state.session.directory = current.state.session.directory
  phaseFresh : next.state.session.phaseRef ≠ current.state.session.phaseRef
  sessionFresh : next.state.session.sessionRef ≠ current.state.session.sessionRef
  checkpoint : next.state.writer.checkpoint = current.state.writer.checkpoint
  durable : next.state.writer.published.durable = current.state.writer.published.durable
  marker : next.state.files.image.directory.active.walBoundary =
    some (WAL.Boundary.encode (WAL.encode (history ++ retained)).size.toUInt64)
  exactOpen :
    ∃ (layout : CanonicalKeeperLayout pending.write.failure.released.image (history ++ retained))
      (selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
        pending.write.failure.released.image.directory.active.manifest current.state.writer.checkpoint)
      (vacant : TryLockObserves pending.write.failure.released.owners current.state.session.directory (.ok true))
      (report : MarkedReadyOpenObservations input current.state.session.directory
        seen.close.report.finished.descriptors pending.write.failure.released layout
        current.state.writer.published vacant selected),
      next.opened = report.finish.run report.chronology ∧
      next.opened = .ok next.state.session (next.state.census, next.state.files) ∧ next.initial = next.state ∧
      next.state.cache = report.admission.cache ∧ next.state.census = report.finish.census ∧
      next.state.owner = report.admission.owner ∧ next.state.directorySlot = report.admission.cached ∧
      report.reads.bindings (current.state.session.directory.file .lock) =
        seen.close.report.bindings (current.state.session.directory.file .lock) ∧
      report.reads.bindings current.state.session.directory.path =
        pending.observed.bindings current.state.session.directory.path ∧
      report.reads.reads.ObservesSelected current.state.session.directory
        pending.write.failure.released.image.directory.active.manifest current.state.writer.published.durable

/-- The actual open begins at the successfully released census after
any finite sequence of failed unlocks on the same pending write. -/
theorem NativePendingWrite.recoversAfterCloseRetries {current : NativeReadPosition history log}
    (pending : NativePendingWrite current)
    {input : FilePath} (seen : NativePendingCloseRetryOpen pending input) :
    ∃ retained next, NativePendingCloseRetryContinuation seen retained next := by
  let lockIdentity := seen.close.binding.trans pending.custody.2.2.2.1
  have reopened := current.readPrefix.reopensReleasedUncertainWrite pending.write lockIdentity seen.observe
  obtain ⟨chosen, layout, selected, vacant, report, state, allowed, marker, opened, path, phaseFresh, sessionFresh,
    cache, census, owner, directorySlot, pair, checkpoint, durable, lock, root, reads, seed⟩ := reopened
  obtain ⟨retained, branch, rfl⟩ : ∃ retained : List WAL.Write,
      (retained = [] ∨ retained = pending.write.failure.batch) ∧ chosen = history ++ retained := by
    rcases allowed with old | whole
    · exact ⟨[], .inl rfl, by simpa only [List.append_nil] using old⟩
    · exact ⟨pending.write.failure.batch, .inr rfl, whole⟩
  let next : NativeReadPosition (history ++ retained) pending.submissions :=
    ⟨report.finish.run report.chronology, state, state, current.reads, seed⟩
  obtain ⟨failed, closed, _, _, _, released, _⟩ := seen.releases
  exact ⟨retained, next, pending.returned, failed, closed, released, branch, rfl, path, phaseFresh, sessionFresh,
    checkpoint, durable, (congrArg DirectoryPublication.Bindings.walBoundary pair).trans marker,
    layout, selected, vacant, report, rfl, opened, rfl, cache, census, owner, directorySlot,
    lock.trans lockIdentity.symm, root.trans pending.custody.2.2.2.2.symm, reads⟩

end Alvoki.Storage.DiskSession
