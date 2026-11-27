import Alvoki.Storage.Disk.Proofs.Native.Execution.NativeInactiveSessionCalls
import Alvoki.Storage.Disk.Proofs.Native.Execution.NativeReadyProcessExit

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WAL.Boundary

/-- After the actual uncertain return and any rejected requests, the
reported descriptor interval contains only slot activity. The writer
exits with its lock slot still live. Later drops can remove inherited
aliases that survive its exit. -/
structure NativePendingWriteProcessExit {current : NativeReadPosition history log}
    (pending : NativePendingWrite current) where
  requests : List NativeInactiveRequest
  beforeExit : DescriptorInventory
  filesBeforeExit : LockedFileState FileImage
  observed : LockCensusTrace current.state.session.directory current.state.session.descriptor
    pending.poisoned.descriptors pending.files beforeExit filesBeforeExit
  writerLive : current.state.owner ∈ beforeExit.slots
  later : List LockReferenceDrop
  last : (beforeExit.afterDrops (.exited current.state.owner.reference.process :: later)).references
    current.state.session.descriptor = []

namespace NativePendingWriteProcessExit

variable {current : NativeReadPosition history log} {pending : NativePendingWrite current}

private def writerExit (seen : NativePendingWriteProcessExit pending) :
    NativeWriterProcessExit current.state pending.poisoned.descriptors pending.files :=
  ⟨seen.beforeExit, seen.filesBeforeExit, seen.observed, seen.writerLive, seen.later, seen.last⟩

def afterExit (seen : NativePendingWriteProcessExit pending) : DescriptorInventory :=
  seen.writerExit.afterExit

def filesAfterExit (seen : NativePendingWriteProcessExit pending) : LockedFileState FileImage :=
  seen.writerExit.filesAfterExit

def census (seen : NativePendingWriteProcessExit pending) : DescriptorInventory :=
  seen.writerExit.census

def files (seen : NativePendingWriteProcessExit pending) : LockedFileState FileImage :=
  seen.writerExit.files

structure Released (seen : NativePendingWriteProcessExit pending) : Prop where
  returned : pending.write.returnedAt pending.cache
  rejected : NativeInactiveTrace pending.inactive seen.requests
    (seen.requests.map (NativeInactiveRequest.response .poisoned))
  sameBeforeExit : seen.filesBeforeExit = pending.files
  heldBeforeExit : ¬ TryLockObserves seen.filesBeforeExit.owners current.state.session.directory (.ok true)
  afterExit : TryLockObserves seen.filesAfterExit.owners current.state.session.directory (.ok true) ↔
    seen.afterExit.references current.state.session.descriptor = []
  noWriterSlots : ∀ slot ∈ seen.census.slots, slot.reference.process ≠ current.state.owner.reference.process
  trace : LockCensusTrace current.state.session.directory current.state.session.descriptor
    pending.poisoned.descriptors pending.files seen.census seen.files
  exactFiles : seen.files = pending.write.failure.released
  vacant : TryLockObserves seen.files.owners current.state.session.directory (.ok true)
  inodeMap : seen.census.inode = pending.poisoned.descriptors.inode
  retry : ReportedReopenPrefix current.state.session.directory current.state.writer.wal.active.first pending.files seen.files

/-- The writer's actual exit drops all its slots. The lock becomes
available exactly when the last observed alias disappears. -/
theorem releases (seen : NativePendingWriteProcessExit pending) : seen.Released := by
  have dropped := seen.writerExit.releases current.readPrefix.refines.1.owner
  exact ⟨pending.returned, pending.inactive.executes seen.requests, dropped.sameBeforeExit, dropped.heldBeforeExit,
    dropped.afterExit, dropped.noWriterSlots, dropped.trace, dropped.exactFiles, dropped.vacant, dropped.inodeMap,
    dropped.trace.reopenTrace .start⟩

end NativePendingWriteProcessExit

/-- Reopening uses the file image and census reached by the slot
events, including any aliases left behind by the writer. -/
structure NativePendingWriteExitReopened {current : NativeReadPosition history log}
    {pending : NativePendingWrite current} (seen : NativePendingWriteProcessExit pending)
    (input : FilePath) (retained : List WAL.Write) (next : NativeReadPosition (history ++ retained) pending.submissions) :
    Prop where
  released : seen.Released
  wholeOrNone : retained = [] ∨ retained = pending.write.failure.batch
  reads : next.reads = current.reads
  directory : next.state.session.directory = current.state.session.directory
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
      (report : MarkedReadyOpenObservations input current.state.session.directory seen.census
        pending.write.failure.released layout current.state.writer.published vacant selected),
      next.opened = report.finish.run report.chronology ∧
      next.opened = .ok next.state.session (next.state.census, next.state.files) ∧ next.initial = next.state ∧
      next.state.cache = report.admission.cache ∧ next.state.census = report.finish.census ∧
      next.state.owner = report.admission.owner ∧ next.state.directorySlot = report.admission.cached ∧
      report.reads.bindings (current.state.session.directory.file .lock) =
        pending.observed.bindings (current.state.session.directory.file .lock) ∧
      report.reads.bindings current.state.session.directory.path =
        pending.observed.bindings current.state.session.directory.path ∧
      report.reads.reads.ObservesSelected current.state.session.directory
        pending.write.failure.released.image.directory.active.manifest current.state.writer.published.durable

/-- Use the exact selected reader in the process-exit continuation.
The same reached session seeds any following raw table proof. -/
theorem NativePendingWrite.recoversAfterProcessExitFrom {current : NativeReadPosition history log}
    (pending : NativePendingWrite current) {input : FilePath} (seen : NativePendingWriteProcessExit pending)
    {chosen : List WAL.Write} {layout : CanonicalKeeperLayout pending.write.failure.released.image chosen}
    {selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
      pending.write.failure.released.image.directory.active.manifest current.state.writer.checkpoint}
    {vacant : TryLockObserves pending.write.failure.released.owners current.state.session.directory (.ok true)}
    (report : MarkedReadyOpenObservations input current.state.session.directory seen.census
      pending.write.failure.released layout current.state.writer.published vacant selected)
    {state : NativeReadyState} (recovered : pending.write.ReleasedReadResult history log current.reads report state) :
    ∃ (retained : List WAL.Write) (next : NativeReadPosition (history ++ retained) pending.submissions),
      NativePendingWriteExitReopened seen input retained next ∧ chosen = history ++ retained ∧
      next.opened = report.finish.run report.chronology ∧ next.opened = .ok next.state.session (next.state.census, next.state.files) ∧
      next.state.cache = report.admission.cache ∧ next.state.owner = report.admission.owner ∧
      next.state.directorySlot = report.admission.cached := by
  obtain ⟨allowed, marker, opened, path, phaseFresh, sessionFresh, cache, census, owner, directorySlot,
    pair, checkpoint, durable, lock, root, reads, seed⟩ := recovered
  obtain ⟨retained, branch, rfl⟩ : ∃ retained : List WAL.Write,
      (retained = [] ∨ retained = pending.write.failure.batch) ∧ chosen = history ++ retained := by
    rcases allowed with old | whole
    · exact ⟨[], .inl rfl, by simpa only [List.append_nil] using old⟩
    · exact ⟨pending.write.failure.batch, .inr rfl, whole⟩
  let next : NativeReadPosition (history ++ retained) pending.submissions :=
    ⟨report.finish.run report.chronology, state, state, current.reads, seed⟩
  exact ⟨retained, next, ⟨seen.releases, branch, rfl, path, phaseFresh, sessionFresh,
    checkpoint, durable, (congrArg DirectoryPublication.Bindings.walBoundary pair).trans marker,
    layout, selected, vacant, report, rfl, opened, rfl, cache, census, owner, directorySlot,
    lock.trans pending.custody.2.2.2.1.symm, root.trans pending.custody.2.2.2.2.symm, reads⟩,
    rfl, rfl, opened, cache, owner, directorySlot⟩

/-- The marked opener takes the exact census after the reported exit
and later drops. Its live marker chooses the old history or the full
uncertain group, and the earlier read responses stay in the ledger. -/
theorem NativePendingWrite.recoversAfterProcessExit {current : NativeReadPosition history log}
    (pending : NativePendingWrite current) {input : FilePath} (seen : NativePendingWriteProcessExit pending)
    (observe : pending.write.ReleasedMarkedReports input seen.census
      (pending.observed.bindings (current.state.session.directory.file .lock))) :
    ∃ retained next, NativePendingWriteExitReopened seen input retained next := by
  obtain ⟨_, _, _, _, report, state, recovered⟩ :=
    current.readPrefix.reopensReleasedUncertainWrite pending.write pending.custody.2.2.2.1 observe
  obtain ⟨retained, next, reopened, _⟩ := pending.recoversAfterProcessExitFrom seen report (state := state) recovered
  exact ⟨retained, next, reopened⟩

end Alvoki.Storage.DiskSession
