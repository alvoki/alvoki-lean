import Alvoki.Storage.Disk.Proofs.Native.Execution.NativePendingCloseRetries

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WAL.Boundary

/-- At least one reported poisoned close returned an unlock error. Slot
events can follow the last failed call, but its owner stays live until
the final reported event removes all remaining references. -/
structure NativePendingCloseReferenceDrop {history : List WAL.Write} {log : List DatabaseSubmissions}
    {current : NativeReadPosition history log} (pending : NativePendingWrite current) where
  prior : List (NativePendingCloseError pending)
  failed : NativePendingCloseError pending
  beforeDrop : DescriptorInventory
  beforeFiles : LockedFileState FileImage
  observed : LockCensusTrace current.state.session.directory current.state.session.descriptor
    pending.poisoned.descriptors pending.files beforeDrop beforeFiles
  live : beforeDrop.references current.state.session.descriptor ≠ []
  drop : LockReferenceDrop
  gone : (beforeDrop.afterDrops [drop]).references current.state.session.descriptor = []

namespace NativePendingCloseReferenceDrop

variable {current : NativeReadPosition history log} {pending : NativePendingWrite current}

def attempts (seen : NativePendingCloseReferenceDrop pending) : List (NativePendingCloseError pending) :=
  seen.prior ++ [seen.failed]

def census (seen : NativePendingCloseReferenceDrop pending) : DescriptorInventory :=
  seen.beforeDrop.afterDrops [seen.drop]

def files (seen : NativePendingCloseReferenceDrop pending) : LockedFileState FileImage :=
  seen.beforeDrop.dropLockState current.state.session.descriptor [seen.drop] current.state.session.directory seen.beforeFiles

/-- The final reported reference drop releases exactly this owner. All
earlier close errors preserve the poisoned state and the held image. -/
structure Released (seen : NativePendingCloseReferenceDrop pending) : Prop where
  writeReturned : pending.write.returnedAt pending.cache
  failedCloses : CachedCloseFailureTrace current.state.session.directory current.state.session.descriptor pending.poisoned
    (seen.attempts.map (·.cause)) pending.poisoned
  lastError : seen.failed.close.report.run = .error seen.failed.cause pending.poisoned
  sameFiles : seen.beforeFiles = pending.files
  held : ¬ TryLockObserves seen.beforeFiles.owners current.state.session.directory (.ok true)
  removes : ∀ reference ∈ seen.beforeDrop.references current.state.session.descriptor, seen.drop.removes reference = true
  exactFiles : seen.files = pending.write.failure.released
  vacant : TryLockObserves seen.files.owners current.state.session.directory (.ok true)
  inodeMap : seen.census.inode = pending.poisoned.descriptors.inode
  retry : ReportedReopenPrefix current.state.session.directory current.state.writer.wal.active.first pending.files seen.files

theorem releases (seen : NativePendingCloseReferenceDrop pending) : seen.Released := by
  have completed := LockCensusTrace.drops seen.observed [seen.drop]
  have sameFiles : seen.beforeFiles = pending.files := by
    simpa only [ite_eq_right seen.live] using seen.observed.reached.2.2
  have held := fun available => seen.live (seen.observed.freshFlockAllowed.mp available)
  have removes : ∀ reference ∈ seen.beforeDrop.references current.state.session.descriptor,
      seen.drop.removes reference = true := by
    intro reference present
    by_cases dropped : seen.drop.removes reference = true
    · exact dropped
    · have survives : reference ∈ (seen.beforeDrop.afterDrops [seen.drop]).references current.state.session.descriptor := by
        rw [DescriptorInventory.references_afterDrops]
        exact List.mem_filter.mpr ⟨present, by simp [Bool.eq_false_iff.mpr dropped]⟩
      simp only [seen.gone, List.not_mem_nil] at survives
  have released : seen.files = pending.write.failure.released := by
    simpa only [files, seen.gone, ite_true, NativePendingWrite.files, NativePendingWrite.poisoned,
      ObservedBatchFailure.closeState, SegmentedBatchFailure.released] using completed.reached.2.2
  exact ⟨pending.returned, NativePendingCloseError.trace seen.attempts, seen.failed.returns.1, sameFiles,
    held, removes, released, completed.freshFlockAllowed.mpr seen.gone, completed.reached.2.1, completed.reopenTrace .start⟩

end NativePendingCloseReferenceDrop

/-- The next held marked open after the reported final slot event uses
the released write image and that exact descriptor inventory. -/
structure NativePendingCloseDropReopened {history : List WAL.Write} {log : List DatabaseSubmissions}
    {current : NativeReadPosition history log} {pending : NativePendingWrite current} {input : FilePath}
    (seen : NativePendingCloseReferenceDrop pending) (retained : List WAL.Write)
    (next : NativeReadPosition (history ++ retained) pending.submissions) : Prop where
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
      (report : MarkedReadyOpenObservations input current.state.session.directory seen.census pending.write.failure.released
        layout current.state.writer.published vacant selected),
      next.opened = report.finish.run report.chronology ∧
      next.opened = .ok next.state.session (next.state.census, next.state.files) ∧ next.initial = next.state ∧
      next.state.cache = report.admission.cache ∧ next.state.census = report.finish.census ∧
      next.state.owner = report.admission.owner ∧ next.state.directorySlot = report.admission.cached ∧
      report.reads.bindings (current.state.session.directory.file .lock) =
        seen.failed.close.report.bindings (current.state.session.directory.file .lock) ∧
      report.reads.bindings current.state.session.directory.path =
        pending.observed.bindings current.state.session.directory.path ∧
      report.reads.reads.ObservesSelected current.state.session.directory
        pending.write.failure.released.image.directory.active.manifest current.state.writer.published.durable

/-- A reported reference drop can permit recovery after returned unlock
errors without a successful explicit close. Recovery derives the
selected prefix before taking the reported marked-open callbacks. -/
theorem NativePendingWrite.recoversAfterFailedClosesAndDrop {current : NativeReadPosition history log}
    (pending : NativePendingWrite current) {input : FilePath} (seen : NativePendingCloseReferenceDrop pending)
    (observe : pending.write.ReleasedMarkedReports input seen.census
      (seen.failed.close.report.bindings (current.state.session.directory.file .lock))) :
    ∃ retained next, NativePendingCloseDropReopened (input := input) seen retained next := by
  let lockIdentity := seen.failed.close.binding.trans pending.custody.2.2.2.1
  have reopened := current.readPrefix.reopensReleasedUncertainWrite pending.write lockIdentity observe
  obtain ⟨chosen, layout, selected, vacant, report, state, allowed, marker, opened, path, phaseFresh, sessionFresh,
    cache, census, owner, directorySlot, pair, checkpoint, durable, lock, root, reads, seed⟩ := reopened
  obtain ⟨retained, branch, rfl⟩ : ∃ retained : List WAL.Write,
      (retained = [] ∨ retained = pending.write.failure.batch) ∧ chosen = history ++ retained := by
    rcases allowed with old | whole
    · exact ⟨[], .inl rfl, by simpa only [List.append_nil] using old⟩
    · exact ⟨pending.write.failure.batch, .inr rfl, whole⟩
  let next : NativeReadPosition (history ++ retained) pending.submissions :=
    ⟨report.finish.run report.chronology, state, state, current.reads, seed⟩
  exact ⟨retained, next, seen.releases, branch, rfl, path, phaseFresh, sessionFresh,
    checkpoint, durable, (congrArg DirectoryPublication.Bindings.walBoundary pair).trans marker,
    layout, selected, vacant, report, rfl, opened, rfl, cache, census, owner, directorySlot,
    lock.trans lockIdentity.symm, root.trans pending.custody.2.2.2.2.symm, reads⟩

end Alvoki.Storage.DiskSession
