import Alvoki.Storage.Disk.Proofs.Write.NativeReadyUncertainWrite
import Alvoki.Storage.Disk.Proofs.Read.NativeReadRecoveryTrace

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WAL.Boundary

/-- The primitive census at the returned write error. The live lock and
cached directory still refer to their original objects under the held
namespace. The write's cache is the one returned by its shared schedule. -/
structure NativePendingWriteCensus (state : NativeReadyState) (cache : CensusDirectoryCache) where
  reached : DescriptorInventory
  ownerLive : state.owner ∈ reached.slots
  directoryLive : state.directorySlot ∈ reached.slots
  lockInode : reached.inode state.owner.description = state.census.inode state.owner.description
  cachedAt : DescriptorInventory
  cachedDirectory : cache.directory = some (cachedAt, state.directorySlot, 0)
  directoryInode : cachedAt.inode state.directorySlot.description = reached.inode state.directorySlot.description
  sameDirectory : reached.inode state.directorySlot.description = state.census.inode state.directorySlot.description
  bindings : FilePath → Option Nat
  lockBound : bindings (state.session.directory.file .lock) = some (reached.inode state.owner.description)
  directoryBound : bindings state.session.directory.path = some (reached.inode state.directorySlot.description)

/-- A reached uncertain write is an execution endpoint in its own right.
It retains the returned error, poisoned phase, cache and exact files.
The introduced submission still has its reported survivor alternatives. -/
structure NativePendingWrite (before : NativeReadPosition history log) where
  write : NativeReadyWriteFailure before.state
  cache : CensusDirectoryCache
  returned : write.returnedAt cache
  observed : NativePendingWriteCensus before.state cache

namespace NativePendingWrite

variable {history : List WAL.Write} {log : List DatabaseSubmissions}
  {before : NativeReadPosition history log}

def poisoned (pending : NativePendingWrite before) : CachedCloseState CheckpointOpenHandle WriteFiles :=
  ObservedBatchFailure.closeState pending.write.failure pending.cache pending.observed.reached

def session (pending : NativePendingWrite before) : SegmentedSession :=
  { before.state.session with phase := pending.poisoned.phase }

/-- Project the same failed bytes used by recovery, while retaining the
owner that is still held at the write return. -/
def files (pending : NativePendingWrite before) : LockedFileState FileImage :=
  ⟨pending.write.failure.released.image, pending.poisoned.files.owners⟩

def submissions (pending : NativePendingWrite before) : List DatabaseSubmissions :=
  log ++ [.uncertainBatch pending.write.failure.batch]

theorem holds (pending : NativePendingWrite before) :
    pending.files.owners.Owns before.state.session.directory before.state.session.descriptor :=
  before.readPrefix.refines.1.retained.held

/-- The reached phase rejects acquisition and reads on the same session
references, including a request using a previously issued local handle. -/
theorem rejectsReads (pending : NativePendingWrite before) (sequence : UInt64)
    (sameSession : Bool) (read : PackedTable → Option α) :
    pending.session.sessionRef = before.state.session.sessionRef ∧
    pending.session.phaseRef = before.state.session.phaseRef ∧
    pending.session.runAcquireAt sequence = .error (IO.userError "publication failed; reopen the database") pending.session ∧
    pending.session.runSnapshotRead sameSession read =
      .error (IO.userError "publication failed; reopen the database") pending.session :=
  ⟨rfl, rfl, rfl, SegmentedSession.runSnapshotRead_poisoned rfl sameSession read⟩

/-- The lock still rejects a competing acquisition at this endpoint.
Both live descriptions remain associated with their original objects. -/
theorem custody (pending : NativePendingWrite before) :
    (¬ TryLockObserves pending.files.owners before.state.session.directory (.ok true)) ∧
    before.state.owner ∈ pending.poisoned.descriptors.slots ∧
    before.state.directorySlot ∈ pending.poisoned.descriptors.slots ∧
    pending.observed.bindings (before.state.session.directory.file .lock) =
      some (before.state.census.inode before.state.owner.description) ∧
    pending.observed.bindings before.state.session.directory.path =
      some (before.state.census.inode before.state.directorySlot.description) := by
  refine ⟨?_, pending.observed.ownerLive, pending.observed.directoryLive,
    pending.observed.lockBound.trans (congrArg some pending.observed.lockInode),
    pending.observed.directoryBound.trans (congrArg some pending.observed.sameDirectory)⟩
  intro vacant
  have held := pending.holds
  change pending.files.owners (before.state.session.directory.file .lock) = some before.state.session.descriptor at held
  rw [vacant rfl] at held
  contradiction

/-- Before any successful reopen, arbitrary reported retry prefixes can
carry the held failed-file projection through release or power loss.
Their selected marker fixes an old or whole-batch history. Each selected
history preserves the previous read responses and committed bounds. -/
theorem selectsReportedSurvivor (pending : NativePendingWrite before)
    {retry : LockedFileState FileImage}
    (reported : ReportedReopenPrefix before.state.session.directory before.state.writer.wal.active.first pending.files retry) :
    BoundedReopenTrace before.state.session.directory
      (BatchRetryTarget before.state.writer.history pending.write.failure.batch before.state.writer.wal.active.first)
      pending.files retry ∧
    retry.image.kept = pending.files.image.kept ∧
    retry.image.directory.active.manifest = before.state.writer.target.pair.manifest ∧
    ∃ chosen,
      (chosen = history ∨ chosen = history ++ pending.write.failure.batch) ∧
      retry.image.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode chosen).size.toUInt64) ∧
      PendingClientReplay pending.submissions before.reads chosen ∧
      ∀ read ∈ before.reads, read.BoundedBy chosen.length := by
  obtain ⟨valid, earlierHistory, earlierReads⟩ := before.readPrefix.refines
  obtain ⟨trace, kept, manifest, chosen, allowed, marker, _, _, _, _, _, _, _, _, ordered⟩ :=
    pending.write.failure.refinesReopenPrefixWithWal valid.retained reported
  have selected : chosen = history ∨ chosen = history ++ pending.write.failure.batch := by
    rcases allowed with old | whole
    · exact .inl (old.trans earlierHistory)
    · exact .inr (whole.trans (congrArg (· ++ pending.write.failure.batch) earlierHistory))
  obtain ⟨continued, bounded⟩ := earlierReads.appendUncertain before.readPrefix.readsBounded selected ordered
  exact ⟨trace, kept, manifest.trans (congrArg DirectoryPublication.Bindings.manifest valid.retained.walPair),
    chosen, selected, marker, continued, bounded⟩

/-- The live reached marker has a valid selection even when execution
stops at the returned error. The original crash alternatives stay in
the projected image for later reports. -/
theorem selectsAtReturn (pending : NativePendingWrite before) :
    ∃ chosen,
      (chosen = history ∨ chosen = history ++ pending.write.failure.batch) ∧
      pending.files.image.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode chosen).size.toUInt64) ∧
      PendingClientReplay pending.submissions before.reads chosen ∧
      ∀ read ∈ before.reads, read.BoundedBy chosen.length :=
  (pending.selectsReportedSurvivor .start).2.2.2

end NativePendingWrite

/-- Derive the exact returned write failure and preserve its observed
authority. The execution can stop here with no request to reopen. -/
theorem NativeReadPosition.stopsAtUncertainWrite (before : NativeReadPosition history log)
    (write : NativeReadyWriteFailure before.state)
    (inspect : ∀ cache, write.returnedAt cache → Nonempty (NativePendingWriteCensus before.state cache)) :
    ∃ pending : NativePendingWrite before, pending.write = write ∧
      pending.poisoned.phase = .poisoned ∧
      pending.poisoned.files = ⟨(pending.cache, write.failure.failed), before.state.files.owners⟩ ∧
      pending.poisoned.descriptors = pending.observed.reached ∧
      pending.files.image = write.failure.released.image ∧
      pending.files.owners.Owns before.state.session.directory before.state.session.descriptor ∧
      pending.submissions = log ++ [.uncertainBatch write.failure.batch] := by
  obtain ⟨cache, returned⟩ := write.returnsUnknown before.readPrefix.refines.1
  obtain ⟨census⟩ := inspect cache returned
  let pending : NativePendingWrite before := ⟨write, cache, returned, census⟩
  exact ⟨pending, rfl, rfl, rfl, rfl, rfl, pending.holds, rfl⟩

end Alvoki.Storage.DiskSession
