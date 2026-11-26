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

/-- Local primitive reports for the healthy attempt after the exact
failed data has been released. The marker selection is supplied by
the preceding proof. -/
def ReleasedMarkedReports (seen : NativeReadyWriteFailure state) (input : FilePath)
    (inventory : DescriptorInventory) (lockBinding : Option Nat) : Prop :=
  ∀ chosen, ∀ layout : CanonicalKeeperLayout seen.failure.released.image chosen,
  (chosen = state.writer.history ∨ chosen = state.writer.history ++ seen.failure.batch) →
  Prepared seen.failure.released.image layout.target layout.plan →
  ∀ selected : SelectedIntegrityCheckpoint state.writer.published.durable
      seen.failure.released.image.directory.active.manifest state.writer.checkpoint,
  ∀ vacant : TryLockObserves seen.failure.released.owners state.session.directory (.ok true),
  ∃ report : MarkedReadyOpenObservations input state.session.directory inventory
      seen.failure.released layout state.writer.published vacant selected,
    report.reads.bindings (state.session.directory.file .lock) = lockBinding ∧
    report.reads.bindings state.session.directory.path = some (state.census.inode state.directorySlot.description) ∧
    state.session.phaseRef ∈ report.callbacks.liveRefs ∧ state.session.sessionRef ∈ report.callbacks.liveRefs

def releasedWal (seen : NativeReadyWriteFailure state) (history : List WAL.Write) : WalSegmentImage :=
  state.writer.wal.appendSelectedView seen.failure.released.image.directory.active history

theorem releasedVacant (seen : NativeReadyWriteFailure state) :
    TryLockObserves seen.failure.released.owners state.session.directory (.ok true) := by
  simp [SegmentedBatchFailure.released, TryLockObserves, LockOwners.set]

/-- Choose the replay from the live marker of the released write image.
No power-loss image or successful recovery has been chosen here. -/
structure ReleasedPlan (seen : NativeReadyWriteFailure state) where
  history : List WAL.Write
  allowed : history = state.writer.history ∨ history = state.writer.history ++ seen.failure.batch
  marker : seen.failure.released.image.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64)
  layout : CanonicalKeeperLayout seen.failure.released.image history
  walLayout : (seen.releasedWal history).ReadLayout history
  walValid : (seen.releasedWal history).Valid history
  first : layout.target.first = (seen.releasedWal history).active.first
  descriptors : layout.sealed ++ [layout.keeper] = (seen.releasedWal history).readDescriptors layout.range.watermark
  offsets : selectWalSegmentReads ((seen.releasedWal history).segments.map WalSegment.first) layout.range.watermark =
    some (layout.first, ((seen.releasedWal history).readDescriptors layout.range.watermark).map WalSegment.first)
  prepared : Prepared seen.failure.released.image layout.target layout.plan
  kept : seen.failure.released.image.kept = ((seen.releasedWal history).checkpointReopenFiles (seen.releasedWal history).directory none).kept
  selected : SelectedIntegrityCheckpoint state.writer.published.durable
    seen.failure.released.image.directory.active.manifest state.writer.checkpoint
  accepted : state.writer.published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
    seen.failure.released.image.directory.active.manifest
  ordered : WAL.OrdinalsFrom 1 history

theorem releasedPlans (seen : NativeReadyWriteFailure state) (valid : state.Valid) : Nonempty seen.ReleasedPlan := by
  have started : ReportedReopenPrefix state.session.directory state.writer.wal.active.first
      ⟨seen.failure.released.image, seen.failure.released.owners⟩ seen.failure.released := .start
  obtain ⟨_, kept, manifest, chosen, allowed, marker, walLayout, walValid, layout, first, descriptors, offsets,
    prepared, accepted, ordered⟩ := seen.failure.refinesReopenPrefixWithWal valid.retained started
  have sameManifest := manifest.trans (congrArg DirectoryPublication.Bindings.manifest valid.retained.walPair)
  exact ⟨⟨chosen, allowed, marker, layout, walLayout, walValid, first, descriptors, offsets, prepared, kept,
    sameManifest.symm ▸ valid.retained.resumed.selected, accepted, ordered⟩⟩

/-- The original selected read result with its open, custody and ledger
all indexed by the same chosen report. -/
abbrev ReleasedReadResult (seen : NativeReadyWriteFailure state) (history : List WAL.Write) (log : List DatabaseSubmissions)
    (recorded : List RecordedSnapshotRead) {input : FilePath} {inventory : DescriptorInventory} {chosen : List WAL.Write}
    {layout : CanonicalKeeperLayout seen.failure.released.image chosen}
    {selected : SelectedIntegrityCheckpoint state.writer.published.durable
      seen.failure.released.image.directory.active.manifest state.writer.checkpoint}
    {vacant : TryLockObserves seen.failure.released.owners state.session.directory (.ok true)}
    (report : MarkedReadyOpenObservations input state.session.directory inventory
      seen.failure.released layout state.writer.published vacant selected) (next : NativeReadyState) : Prop :=
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
      (log ++ [.uncertainBatch seen.failure.batch]) recorded next

/-- The exact marked return, its selected history and the continued old
read ledger, after the caller's reported release. -/
def ReleasedReopenResult (seen : NativeReadyWriteFailure state) (input : FilePath)
    (inventory : DescriptorInventory) (history : List WAL.Write) (log : List DatabaseSubmissions)
    (recorded : List RecordedSnapshotRead) : Prop :=
  ∃ (chosen : List WAL.Write) (layout : CanonicalKeeperLayout seen.failure.released.image chosen)
    (selected : SelectedIntegrityCheckpoint state.writer.published.durable
      seen.failure.released.image.directory.active.manifest state.writer.checkpoint)
    (vacant : TryLockObserves seen.failure.released.owners state.session.directory (.ok true))
    (report : MarkedReadyOpenObservations input state.session.directory inventory
      seen.failure.released layout state.writer.published vacant selected) (next : NativeReadyState),
    seen.ReleasedReadResult history log recorded report next

end NativeReadyWriteFailure

/-- Select the exact ready result from the same primitive report used by
the released write's raw reopen. -/
theorem NativeReadyReadPrefix.reopensReleasedUncertainWriteFrom
    (prior : NativeReadyReadPrefix opened initial history log recorded state)
    (seen : NativeReadyWriteFailure state) {input : FilePath} {inventory : DescriptorInventory}
    (plan : seen.ReleasedPlan)
    (report : MarkedReadyOpenObservations input state.session.directory inventory seen.failure.released
      plan.layout state.writer.published seen.releasedVacant plan.selected)
    (lock : report.reads.bindings (state.session.directory.file .lock) = some (state.census.inode state.owner.description))
    (directory : report.reads.bindings state.session.directory.path = some (state.census.inode state.directorySlot.description))
    (oldPhaseRef : state.session.phaseRef ∈ report.callbacks.liveRefs)
    (oldSessionRef : state.session.sessionRef ∈ report.callbacks.liveRefs) :
    ∃ next, seen.ReleasedReadResult history log recorded report next := by
  obtain ⟨valid, oldHistory, priorReplay⟩ := prior.refines
  have allowed : plan.history = history ∨ plan.history = history ++ seen.failure.batch := oldHistory ▸ plan.allowed
  obtain ⟨pending, bounded⟩ := priorReplay.appendUncertain prior.readsBounded allowed plan.ordered
  obtain ⟨next, seed, cacheIdentity, census, owner, directorySlot, pair, durable, checkpoint, path, _, _, _, _,
    phaseFresh, sessionFresh⟩ :=
    report.finish.startsNativeReadPrefix report.chronology report.markerFound plan.prepared.newer
      (report.reads.walReads.selectedAfterWatermark plan.offsets plan.descriptors) plan.accepted plan.ordered
      plan.walLayout plan.walValid valid.retained.spans plan.prepared.pair plan.first plan.kept pending bounded
  exact ⟨next, allowed, plan.marker, seed.frames.1, path, fun same => phaseFresh (same.symm ▸ oldPhaseRef),
    fun same => sessionFresh (same.symm ▸ oldSessionRef), cacheIdentity, census, owner, directorySlot,
    pair, checkpoint, durable, lock, directory, report.reads.chunkReads, seed⟩

/-- Once the failed bytes and released owner are fixed, choose the old
history or whole group before running the next reported marked open. -/
theorem NativeReadyReadPrefix.reopensReleasedUncertainWrite
    (prior : NativeReadyReadPrefix opened initial history log recorded state)
    (seen : NativeReadyWriteFailure state) {input : FilePath} {inventory : DescriptorInventory}
    {lockBinding : Option Nat}
    (lockIdentity : lockBinding = some (state.census.inode state.owner.description))
    (observe : seen.ReleasedMarkedReports input inventory lockBinding) :
    seen.ReleasedReopenResult input inventory history log recorded := by
  obtain ⟨plan⟩ := seen.releasedPlans prior.refines.1
  obtain ⟨report, lock, directory, phase, token⟩ :=
    observe plan.history plan.layout plan.allowed plan.prepared plan.selected seen.releasedVacant
  obtain ⟨next, recovered⟩ := prior.reopensReleasedUncertainWriteFrom seen plan report (lock.trans lockIdentity) directory phase token
  exact ⟨plan.history, plan.layout, plan.selected, seen.releasedVacant, report, next, recovered⟩

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
      seen.ReleasedMarkedReports input close.close.finished.descriptors
        (close.close.bindings (state.session.directory.file .lock))) :
    ∃ cache, seen.returnedAt cache ∧ ∃ close : seen.CloseObservation cache,
      close.close.run = .ok () close.close.finished ∧
      close.close.finished.files = ⟨(⟨none, none, []⟩, seen.failure.failed), seen.failure.released.owners⟩ ∧
      seen.ReleasedReopenResult input close.close.finished.descriptors history log recorded := by
  let valid := prior.refines.1
  obtain ⟨cache, returned⟩ := seen.returnsUnknown valid
  obtain ⟨close⟩ := closeReported cache returned
  have closed := close.close.outcome rfl
  rw [close.successful] at closed
  have closedFiles := close.close.finishedFiles valid.retained.held
  have lockAtClose := close.close.lockObject
  rw [close.owner] at lockAtClose
  have sameLock := lockAtClose.trans (congrArg some close.lockInode)
  exact ⟨cache, returned, close, closed, closedFiles,
    prior.reopensReleasedUncertainWrite seen sameLock (observe cache close)⟩

end Alvoki.Storage.DiskSession
