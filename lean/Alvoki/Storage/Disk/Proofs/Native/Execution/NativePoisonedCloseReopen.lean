import Alvoki.Storage.Disk.Proofs.Native.Execution.NativeInterruptedCloseReopen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WAL.Boundary

variable {history : List WAL.Write} {log : List DatabaseSubmissions} {current : NativeReadPosition history log}

/-- The cut starts at an actual returned uncertain write. The original
issuer then exits and the reported descriptor interval reaches vacancy,
using the explicit unlock effect or the last surviving reference drop.
The next marked open uses that precise census at the supplied input. -/
structure NativePoisonedCloseReopenObservation (pending : NativePendingWrite current) (input : FilePath) where
  cut : NativeCloseUnlockInterruption current.state.session.directory current.state.session.descriptor pending.poisoned
  owner : cut.slot = current.state.owner
  drops : List LockReferenceDrop
  exited : LockReferenceDrop.exited cut.slot.reference.process ∈ drops
  released : cut.effective = true ∨ (cut.afterDrops drops).descriptors.references current.state.session.descriptor = []
  observe : pending.write.ReleasedMarkedReports input (cut.afterDrops drops).descriptors
    (cut.bindings (current.state.session.directory.file .lock))

namespace NativePoisonedCloseReopenObservation

variable {pending : NativePendingWrite current} {input : FilePath}

/-- The old phase and exact returned write cache remain at the
interruption. Later exit and drop reports determine the available
owner and the same physical failed-write image for the next open. -/
structure Reached (seen : NativePoisonedCloseReopenObservation pending input) : Prop where
  written : pending.write.returnedAt pending.cache
  stopped : ∀ clear, seen.cut.run clear = .error current.state.owner seen.cut.atCut
  phase : seen.cut.atCut.phase = .poisoned
  cacheAndFiles : seen.cut.atCut.files.image = (pending.cache, pending.write.failure.failed)
  census : seen.cut.atCut.descriptors = seen.cut.issueCensus
  issuing : current.state.owner ∈ seen.cut.atCut.descriptors.slots
  absent : ∀ slot ∈ (seen.cut.afterDrops seen.drops).descriptors.slots,
    slot.reference.process ≠ current.state.owner.reference.process
  inodes : (seen.cut.afterDrops seen.drops).descriptors.inode = pending.observed.reached.inode
  lock : seen.cut.bindings (current.state.session.directory.file .lock) =
    some (current.state.census.inode current.state.owner.description)
  released : seen.cut.reopenFiles seen.drops = ⟨pending.write.failure.failed, pending.write.failure.released.owners⟩
  projected : (⟨pending.files.image, (seen.cut.reopenFiles seen.drops).owners⟩ : LockedFileState FileImage) =
    pending.write.failure.released
  vacant : TryLockObserves (seen.cut.reopenFiles seen.drops).owners current.state.session.directory (.ok true)

theorem reached (seen : NativePoisonedCloseReopenObservation pending input) : seen.Reached := by
  let stopped := pending.stopsDuringClose seen.cut seen.owner
  obtain ⟨_, phase, cache, census, owner, inodes, lock, _⟩ := stopped (fun _ => pure ())
  have identity := pending.custody.2.2.2.1
  have released : seen.cut.reopenFiles seen.drops =
      ⟨pending.write.failure.failed, pending.write.failure.released.owners⟩ :=
    seen.cut.releasedReopenFiles seen.drops seen.released
  have projected : (⟨pending.files.image, (seen.cut.reopenFiles seen.drops).owners⟩ : LockedFileState FileImage) =
      pending.write.failure.released := by rw [released]; rfl
  exact ⟨pending.returned, fun clear => (stopped clear).1, phase, cache, census, owner,
    seen.owner ▸ seen.cut.excludesExitedProcess seen.exited, inodes, lock.trans identity, released, projected,
    (seen.cut.admitsAfterDrops seen.drops).mpr seen.released⟩

end NativePoisonedCloseReopenObservation

/-- The same exact uncertain-write state, issued unlock and reported
exit reach the captured marked schedule. Its marker selects one
history and its actual returned session supplies all later reads. -/
theorem NativePendingWrite.reopensAfterInterruptedClose (pending : NativePendingWrite current)
    (seen : NativePoisonedCloseReopenObservation pending input) :
    seen.Reached ∧
    pending.write.ReleasedReopenResult input (seen.cut.afterDrops seen.drops).descriptors history log current.reads := by
  have reached := seen.reached
  exact ⟨reached, current.readPrefix.reopensReleasedUncertainWrite pending.write reached.lock seen.observe⟩

/-- The pending group is recorded once. Its selected extension and the
same native open result determine the next reached client position. -/
structure NativePoisonedCloseReopenContinuation (pending : NativePendingWrite current) {input : FilePath}
    (seen : NativePoisonedCloseReopenObservation pending input) (retained : List WAL.Write)
    (next : NativeReadPosition (history ++ retained) pending.submissions) : Prop where
  reached : seen.Reached
  exited : LockReferenceDrop.exited current.state.owner.reference.process ∈ seen.drops
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
        (seen.cut.afterDrops seen.drops).descriptors pending.write.failure.released layout
        current.state.writer.published vacant selected),
      next.opened = report.finish.run report.chronology ∧
      next.opened = .ok next.state.session (next.state.census, next.state.files) ∧ next.initial = next.state ∧
      next.state.cache = report.admission.cache ∧ next.state.census = report.finish.census ∧
      next.state.owner = report.admission.owner ∧ next.state.directorySlot = report.admission.cached ∧
      report.reads.bindings (current.state.session.directory.file .lock) =
        seen.cut.bindings (current.state.session.directory.file .lock) ∧
      report.reads.bindings current.state.session.directory.path = pending.observed.bindings current.state.session.directory.path ∧
      report.reads.reads.ObservesSelected current.state.session.directory
        pending.write.failure.released.image.directory.active.manifest current.state.writer.published.durable

theorem NativePendingWrite.recoversInterruptedClose (pending : NativePendingWrite current)
    (seen : NativePoisonedCloseReopenObservation pending input) :
    ∃ retained next, NativePoisonedCloseReopenContinuation pending seen retained next := by
  obtain ⟨reached, reopened⟩ := pending.reopensAfterInterruptedClose seen
  obtain ⟨chosen, layout, selected, vacant, report, state, allowed, marker, opened, path, phaseFresh, sessionFresh,
    cache, census, owner, directorySlot, pair, checkpoint, durable, lock, root, reads, seed⟩ := reopened
  obtain ⟨retained, branch, rfl⟩ : ∃ retained : List WAL.Write,
      (retained = [] ∨ retained = pending.write.failure.batch) ∧ chosen = history ++ retained := by
    rcases allowed with old | whole
    · exact ⟨[], .inl rfl, by simpa only [List.append_nil] using old⟩
    · exact ⟨pending.write.failure.batch, .inr rfl, whole⟩
  let next : NativeReadPosition (history ++ retained) pending.submissions :=
    ⟨report.finish.run report.chronology, state, state, current.reads, seed⟩
  exact ⟨retained, next, reached, seen.owner ▸ seen.exited, branch, rfl, path, phaseFresh, sessionFresh,
    checkpoint, durable, (congrArg DirectoryPublication.Bindings.walBoundary pair).trans marker,
    layout, selected, vacant, report, rfl, opened, rfl, cache, census, owner, directorySlot,
    lock.trans reached.lock.symm, root.trans pending.custody.2.2.2.2.symm, reads⟩

end Alvoki.Storage.DiskSession
