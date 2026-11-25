import Alvoki.Storage.Disk.NativeMarkedReadPrefix
import Alvoki.Storage.Disk.PoisonedBatchClose

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WAL.Boundary SyncHandleRouting

/-- The reported publication of a nonempty single write or batch begins
with the cache of the reached ready session. -/
structure NativeReadyWriteFailure (state : NativeReadyState) where
  request : WriteRequest
  failure : SegmentedBatchFailure state.session.directory state.writer
  observed : ObservedBatchFailure failure (DescriptorInventory × DescriptorSlot × Nat)
  rows : request.rows = failure.rows
  cache : observed.cache = state.cache

namespace NativeReadyWriteFailure

variable {state : NativeReadyState}

def returnedAt (seen : NativeReadyWriteFailure state) (cache : CensusDirectoryCache) : Prop :=
  let calls := { WriteRequest.Calls.ofFailure seen.observed with cache := state.cache }
  calls.run seen.request state.session.directory state.writer =
    .error (.commitUnknown seen.failure.cause) (.poisoned, ⟨(cache, seen.failure.failed), state.writer.owners⟩)

/-- The actual single or batch schedule returns its reported publication
error and reached poisoned cache. -/
theorem returnsUnknown (seen : NativeReadyWriteFailure state) (valid : state.Valid) :
    ∃ cache, seen.returnedAt cache := by
  obtain ⟨cache, returned⟩ := seen.observed.commitUnknown
  refine ⟨cache, ?_⟩
  unfold returnedAt
  rw [← seen.cache]
  change (WriteRequest.Calls.ofFailure seen.observed).run seen.request state.session.directory state.writer = _
  unfold WriteRequest.Calls.run
  rw [seen.request.runReported_eq_batch valid.retained, seen.rows, valid.retained.directoryFiles]
  exact returned

/-- The raw postwrite inventory and unlock are observed at the returned
poisoned cache. The original lock slot and its inode are still in use. -/
structure CloseObservation (seen : NativeReadyWriteFailure state) (cache : CensusDirectoryCache) where
  descriptors : DescriptorInventory
  close : CachedCloseReports state.session.directory state.session.descriptor
    (ObservedBatchFailure.closeState seen.failure cache descriptors)
  owner : close.slot = state.owner
  lockInode : descriptors.inode state.owner.description = state.census.inode state.owner.description
  successful : close.result = .ok ()

end NativeReadyWriteFailure

/-- A returned uncertain write, the successful close of its exact poisoned
cache, and an immediate healthy marked reopen continue the existing native
client ledger. The reached marker selects the old history or the whole
batch. Earlier read snapshots remain bounded in either selection. The raw
postwrite descriptor inventory and stable lock/directory bindings are
reported at the close and open. The reported reference registry keeps
the old session and phase references while the reopen allocates its own. -/
theorem NativeReadyReadPrefix.reopensUncertainWrite
    (prior : NativeReadyReadPrefix opened initial history log recorded state)
    (seen : NativeReadyWriteFailure state)
    (closeReported : ∀ cache, seen.returnedAt cache → Nonempty (seen.CloseObservation cache))
    {input : FilePath}
    (observe : ∀ cache, ∀ close : seen.CloseObservation cache,
      ∀ chosen, ∀ layout : CanonicalKeeperLayout seen.failure.released.image chosen,
      (chosen = state.writer.history ∨ chosen = state.writer.history ++ seen.failure.batch) →
      Prepared seen.failure.released.image layout.target layout.plan →
      ∀ selected : SelectedIntegrityCheckpoint state.writer.published.durable
          seen.failure.released.image.directory.active.manifest state.writer.checkpoint,
      ∀ vacant : TryLockObserves seen.failure.released.owners state.session.directory (.ok true),
      ∃ report : MarkedReadyOpenObservations input state.session.directory close.close.finished.descriptors
          seen.failure.released layout state.writer.published vacant selected,
        report.reads.bindings (state.session.directory.file .lock) = close.close.bindings (state.session.directory.file .lock) ∧
        report.reads.bindings state.session.directory.path = some (state.census.inode state.directorySlot.description) ∧
        state.session.phaseRef ∈ report.callbacks.liveRefs ∧ state.session.sessionRef ∈ report.callbacks.liveRefs) :
    ∃ cache, seen.returnedAt cache ∧ ∃ close : seen.CloseObservation cache,
      close.close.run = .ok () close.close.finished ∧
      close.close.finished.files = ⟨(⟨none, none, []⟩, seen.failure.failed), seen.failure.released.owners⟩ ∧
      ∃ (chosen : List WAL.Write) (layout : CanonicalKeeperLayout seen.failure.released.image chosen)
        (selected : SelectedIntegrityCheckpoint state.writer.published.durable
          seen.failure.released.image.directory.active.manifest state.writer.checkpoint)
        (vacant : TryLockObserves seen.failure.released.owners state.session.directory (.ok true))
        (report : MarkedReadyOpenObservations input state.session.directory close.close.finished.descriptors
          seen.failure.released layout state.writer.published vacant selected) (next : NativeReadyState),
        (chosen = history ∨ chosen = history ++ seen.failure.batch) ∧
        seen.failure.released.image.directory.active.walBoundary =
          some (WAL.Boundary.encode (WAL.encode chosen).size.toUInt64) ∧
        report.finish.run report.chronology = .ok next.session (next.census, next.files) ∧
        next.session.directory = state.session.directory ∧
        next.session.phaseRef ≠ state.session.phaseRef ∧ next.session.sessionRef ≠ state.session.sessionRef ∧
        next.cache = report.admission.cache ∧ next.census = report.finish.census ∧
        next.owner = report.admission.owner ∧ next.directorySlot = report.admission.cached ∧
        next.files.image.directory.active = seen.failure.released.image.directory.active ∧
        next.writer.checkpoint = state.writer.checkpoint ∧ next.writer.published.durable = state.writer.published.durable ∧
        report.reads.bindings (state.session.directory.file .lock) = some (state.census.inode state.owner.description) ∧
        report.reads.bindings state.session.directory.path = some (state.census.inode state.directorySlot.description) ∧
        report.reads.reads.ObservesSelected state.session.directory seen.failure.released.image.directory.active.manifest
          state.writer.published.durable ∧
        NativeReadyReadPrefix (report.finish.run report.chronology) next chosen
          (log ++ [.uncertainBatch seen.failure.batch]) recorded next := by
  obtain ⟨valid, oldHistory, priorReplay⟩ := prior.refines
  obtain ⟨cache, returned⟩ := seen.returnsUnknown valid
  obtain ⟨close⟩ := closeReported cache returned
  have closed := close.close.outcome rfl
  rw [close.successful] at closed
  have closedFiles := close.close.finishedFiles valid.retained.held
  have lockAtClose := close.close.lockObject
  rw [close.owner] at lockAtClose
  have sameLock := lockAtClose.trans (congrArg some close.lockInode)
  have vacant : TryLockObserves seen.failure.released.owners state.session.directory (.ok true) := by
    simp [SegmentedBatchFailure.released, TryLockObserves, LockOwners.set]
  have started : ReportedReopenPrefix state.session.directory state.writer.wal.active.first
      ⟨seen.failure.released.image, seen.failure.released.owners⟩ seen.failure.released := .start
  obtain ⟨_, kept, manifest, chosen, allowed, marker, walLayout, walValid, layout, first, descriptors, offsets,
    prepared, accepted, ordered⟩ := seen.failure.refinesReopenPrefixWithWal valid.retained started
  have sameManifest := manifest.trans (congrArg DirectoryPublication.Bindings.manifest valid.retained.walPair)
  let selected : SelectedIntegrityCheckpoint state.writer.published.durable
      seen.failure.released.image.directory.active.manifest state.writer.checkpoint :=
    sameManifest.symm ▸ valid.retained.resumed.selected
  obtain ⟨report, lock, directory, oldPhaseRef, oldSessionRef⟩ := observe cache close chosen layout allowed prepared selected vacant
  have allowedFromTrace : chosen = history ∨ chosen = history ++ seen.failure.batch := oldHistory ▸ allowed
  obtain ⟨pending, bounded⟩ := priorReplay.appendUncertain prior.readsBounded allowedFromTrace ordered
  obtain ⟨next, seed, cacheIdentity, census, owner, directorySlot, pair, durable, checkpoint, path, _, _,
    phaseFresh, sessionFresh⟩ :=
    report.finish.startsNativeReadPrefix report.chronology report.markerFound prepared
      (report.reads.walReads.selectedAfterWatermark offsets descriptors) accepted ordered walLayout walValid
      valid.retained.spans prepared.pair first kept pending bounded
  exact ⟨cache, returned, close, closed, closedFiles, chosen, layout, selected, vacant, report, next, allowedFromTrace,
    marker, seed.frames.1, path, fun same => phaseFresh (same.symm ▸ oldPhaseRef),
    fun same => sessionFresh (same.symm ▸ oldSessionRef), cacheIdentity, census, owner, directorySlot,
    pair, checkpoint, durable, lock.trans sameLock, directory, report.reads.chunkReads, seed⟩

end Alvoki.Storage.DiskSession
