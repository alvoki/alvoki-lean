import Alvoki.Storage.Disk.Proofs.Read.NativeReadRecoveryTrace
import Alvoki.Storage.Disk.Proofs.Write.NativeReadyUncertainWrite

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- Primitive observations for a write with an uncertain response, the
caller closing that poisoned session, and a healthy open at `input`. -/
structure NativeUncertainWriteObservation (state : NativeReadyState) where
  write : NativeReadyWriteFailure state
  input : FilePath
  close : ∀ cache, write.returnedAt cache → Nonempty (write.CloseObservation cache)
  reopen : ∀ cache, ∀ close : write.CloseObservation cache,
    ∀ chosen, ∀ layout : CanonicalKeeperLayout write.failure.released.image chosen,
    (chosen = state.writer.history ∨ chosen = state.writer.history ++ write.failure.batch) →
    Prepared write.failure.released.image layout.target layout.plan →
    ∀ selected : SelectedIntegrityCheckpoint state.writer.published.durable
        write.failure.released.image.directory.active.manifest state.writer.checkpoint,
    ∀ vacant : TryLockObserves write.failure.released.owners state.session.directory (.ok true),
    ∃ report : MarkedReadyOpenObservations input state.session.directory close.close.finished.descriptors
        write.failure.released layout state.writer.published vacant selected,
      report.reads.bindings (state.session.directory.file .lock) = close.close.bindings (state.session.directory.file .lock) ∧
      report.reads.bindings state.session.directory.path = some (state.census.inode state.directorySlot.description) ∧
      state.session.phaseRef ∈ report.callbacks.liveRefs ∧ state.session.sessionRef ∈ report.callbacks.liveRefs

/-- A scoped execution edge records the original write via its report and
appends one uncertain submission. The committed extension is the group
selected by the reached marker. The close and reopen are exact callbacks
over the same returned cache, files, and reached descriptor census. -/
structure NativeUncertainWriteContinuation (before : NativeReadPosition history log)
    (observed : NativeUncertainWriteObservation before.state) (retained : List WAL.Write)
    (after : NativeReadPosition (history ++ retained) (log ++ [.uncertainBatch observed.write.failure.batch])) : Prop where
  wholeOrNone : retained = [] ∨ retained = observed.write.failure.batch
  earlierReads : after.reads = before.reads
  initial : after.initial = after.state
  sameDirectory : after.state.session.directory = before.state.session.directory
  newPhaseRef : after.state.session.phaseRef ≠ before.state.session.phaseRef
  newSessionRef : after.state.session.sessionRef ≠ before.state.session.sessionRef
  checkpoint : after.state.writer.checkpoint = before.state.writer.checkpoint
  durable : after.state.writer.published.durable = before.state.writer.published.durable
  marker : after.state.files.image.directory.active.walBoundary =
    some (WAL.Boundary.encode (WAL.encode (history ++ retained)).size.toUInt64)
  execution :
    ∃ cache, observed.write.returnedAt cache ∧ ∃ close : observed.write.CloseObservation cache,
      close.close.run = .ok () close.close.finished ∧
      close.close.finished.files = ⟨(⟨none, none, []⟩, observed.write.failure.failed), observed.write.failure.released.owners⟩ ∧
      ∃ (layout : CanonicalKeeperLayout observed.write.failure.released.image (history ++ retained))
        (selected : SelectedIntegrityCheckpoint before.state.writer.published.durable
          observed.write.failure.released.image.directory.active.manifest before.state.writer.checkpoint)
        (vacant : TryLockObserves observed.write.failure.released.owners before.state.session.directory (.ok true))
        (report : MarkedReadyOpenObservations observed.input before.state.session.directory close.close.finished.descriptors
          observed.write.failure.released layout before.state.writer.published vacant selected),
        after.opened = report.finish.run report.chronology ∧
        after.opened = .ok after.state.session (after.state.census, after.state.files) ∧
        after.state.cache = report.admission.cache ∧ after.state.census = report.finish.census ∧
        after.state.owner = report.admission.owner ∧ after.state.directorySlot = report.admission.cached ∧
        after.state.files.image.directory.active = observed.write.failure.released.image.directory.active ∧
        report.reads.bindings (before.state.session.directory.file .lock) = some (before.state.census.inode before.state.owner.description) ∧
        report.reads.bindings before.state.session.directory.path = some (before.state.census.inode before.state.directorySlot.description) ∧
        report.reads.reads.ObservesSelected before.state.session.directory
          observed.write.failure.released.image.directory.active.manifest before.state.writer.published.durable

/-- Derive an exact next position from the prepared write, close, and
healthy open observations. The existing prefix carries both the earlier
read ledger and its bounds into the marker-selected history. -/
theorem NativeReadPosition.recoversUncertainWrite (current : NativeReadPosition history log)
    (observed : NativeUncertainWriteObservation current.state) :
    ∃ retained after, NativeUncertainWriteContinuation current observed retained after := by
  obtain ⟨cache, returned, close, closed, closedFiles, chosen, layout, selected, vacant, report, state, allowed,
    marker, opened, path, phaseRef, sessionRef, installedCache, census, owner, directorySlot, pair, checkpoint,
    durable, lock, root, reads, seed⟩ :=
    current.readPrefix.reopensUncertainWrite observed.write observed.close observed.reopen
  obtain ⟨retained, branch, rfl⟩ : ∃ retained : List WAL.Write,
      (retained = [] ∨ retained = observed.write.failure.batch) ∧ chosen = history ++ retained := by
    rcases allowed with old | whole
    · exact ⟨[], .inl rfl, by simpa only [List.append_nil] using old⟩
    · exact ⟨observed.write.failure.batch, .inr rfl, whole⟩
  let after : NativeReadPosition (history ++ retained) (log ++ [.uncertainBatch observed.write.failure.batch]) :=
    ⟨report.finish.run report.chronology, state, state, current.reads, seed⟩
  exact ⟨retained, after, branch, rfl, rfl, path, phaseRef, sessionRef, checkpoint, durable,
    (congrArg DirectoryPublication.Bindings.walBoundary pair).trans marker,
    cache, returned, close, closed, closedFiles, layout, selected, vacant, report, rfl, opened,
    installedCache, census, owner, directorySlot, pair, lock, root, reads⟩

end Alvoki.Storage.DiskSession
