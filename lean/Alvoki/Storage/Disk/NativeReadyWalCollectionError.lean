import Alvoki.Storage.Disk.NativeReadyWalCollection

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

/-- Bounded reads after collection use the remaining sealed files but
the same selected checkpoint, keeper and acknowledged WAL suffix. -/
structure CoveredWalRetrySelection (before : SegmentedWriterState) (wal : WalSegmentImage) where
  retained : WalSegmentCollectionRetry before.wal wal
  layout : CanonicalKeeperLayout (wal.checkpointReopenFiles wal.directory before.files.keeper.staged) before.history
  pair : wal.directory.active = before.target.pair
  range : layout.range = before.target.range
  keeper : layout.keeper = before.wal.active
  aligned : layout.tail = ByteArray.empty
  reads : layout.sealed ++ [layout.keeper] = before.wal.readDescriptors layout.range.watermark
  offsets : selectWalSegmentReads (wal.segments.map WalSegment.first) layout.range.watermark =
    some (layout.first, (layout.sealed ++ [layout.keeper]).map WalSegment.first)
  prepared : Prepared (wal.checkpointReopenFiles wal.directory before.files.keeper.staged) layout.target layout.plan
  checkpoint : SelectedIntegrityCheckpoint before.published.durable wal.directory.active.manifest before.checkpoint
  accepted : before.published.AcceptsVersioned before.history.length.toUInt64 (CheckpointRepresentsPrefix before.history)
    wal.directory.active.manifest

private theorem preparesCoveredWalRetry
    {directory : DiskDirectory} {descriptor : Nat} {before : SegmentedWriterState} {wal : WalSegmentImage}
    (ready : before.RetainedReady directory descriptor) (retry : WalSegmentCollectionRetry before.wal wal) :
    Nonempty (CoveredWalRetrySelection before wal) := by
  have pair := (retry.keepsSettledPair ready.walDirectorySettled).1.trans ready.walPair
  have decoded : wal.directory.active.walRange = some before.target.range := pair.symm ▸ before.target.decoded
  obtain ⟨selected, range, keeper, aligned, reads, offsets, _, choices, prefixes, later⟩ :=
    (retry.readLayout ready.layout).checkpointReopenLayout (retry.valid ready.valid)
      .visible decoded ready.resumed.through before.files.keeper.staged
  have kept := retry.keepsReadDescriptors (List.mem_cons_self ..) decoded
  have checkpoint : SelectedIntegrityCheckpoint before.published.durable wal.directory.active.manifest before.checkpoint :=
    (congrArg DirectoryPublication.Bindings.manifest pair).symm ▸ ready.resumed.selected
  have accepted : before.published.AcceptsVersioned before.history.length.toUInt64 (CheckpointRepresentsPrefix before.history)
      wal.directory.active.manifest := (congrArg DirectoryPublication.Bindings.manifest pair).symm ▸ ready.resumed.accepted
  refine ⟨⟨retry, selected, pair, range, keeper.trans retry.keepsActive, aligned, ?_, ?_,
    selected.prepared choices prefixes (range.symm ▸ later), checkpoint, accepted⟩⟩
  · rw [range, reads, kept]
  · rw [range, reads]
    exact offsets

namespace NativeReadyWalCollection

variable {state : NativeReadyState}

/-- Keep the full reached sealed namespace with its possible crash lists,
including while the poisoned writer still owns the lock. -/
def pending (reported : NativeReadyWalCollection state) : LockedFileState WalSealedUnlinkImage :=
  ⟨reported.barrier.after, state.files.owners⟩

end NativeReadyWalCollection

/-- A returned directory sync error leaves the original session poisoned.
The exact visible files and any reported durable sealed alternatives use
the same checkpoint and WAL selection before another open is attempted. -/
theorem NativeReadyReadPrefix.collectionBarrierFailed
    {opened : EStateM.Result IO.Error CensusOpenState SegmentedSession}
    {initial state : NativeReadyState} {history : List WAL.Write} {log : List DatabaseSubmissions}
    {reads : List RecordedSnapshotRead}
    (prior : NativeReadyReadPrefix opened initial history log reads state)
    (reported : NativeReadyWalCollection state) {cause : IO.Error}
    (failed : reported.barrier.outcome = .errorBeforeEffect cause ∨
      reported.barrier.outcome = .errorAfterEffect cause) :
    reported.run = .error (IO.userError s!"sync failed for '{state.session.directory.path}': {cause}")
      (.poisoned, ⟨(state.cache, reported.pending.image), reported.pending.owners⟩) ∧
    reported.pending.image =
      (if reported.barrier.outcome.effective then reported.atBarrier.syncDirectory else reported.atBarrier) ∧
    reported.barrier.reached = reported.inventory.listing.afterClose.afterDrops reported.barrier.drops ∧
    reported.census = state.census ∧ reported.pending.owners.Owns state.session.directory state.session.descriptor ∧
    reported.barrier.handle.2.1 = state.directorySlot ∧ reported.barrier.writerSlot = state.owner ∧
    state.directorySlot ∈ reported.barrier.reached.slots ∧ state.owner ∈ reported.barrier.reached.slots ∧
    reported.reachedView.child reported.inventory.lifetime.root "LOCK" = some reported.inventory.lifetime.lock ∧
    reported.reachedView.modelObject reported.inventory.lifetime.lock = reported.barrier.reached.inode state.owner.description ∧
    (∀ offset ∈ state.writer.wal.collectionOffsets,
      reported.reachedView.child reported.inventory.lifetime.root (renderWalSegmentName offset) = none) ∧
    Nonempty (CoveredWalRetrySelection state.writer reported.pending.image.visible) ∧
    (∀ sealed ∈ reported.pending.image.crashSealed,
      Nonempty (CoveredWalRetrySelection state.writer { reported.pending.image.visible with sealed })) ∧
    state.writer.history = history ∧ PendingClientReplay log reads history := by
  obtain ⟨valid, sameHistory, replay⟩ := prior.refines
  have ready := valid.retained
  have plan := ready.completeObservedWalPlan reported.calls reported.inventory reported.manifest reported.marker
  have bound (segment : WalSegment) (stored : segment ∈ state.writer.wal.sealed) :
      (reported.inventory.lifetime.namespaceView.child reported.inventory.lifetime.root
        (renderWalSegmentName segment.first)).isSome = true := by
    rw [reported.inventory.bound segment (List.mem_append_left _ stored)]
    rfl
  obtain ⟨effect, ⟨projected, invariant⟩, survive, _, _, _⟩ := ready.reportedWalCollectionBarrier
    reported.calls plan (fun _ member => member) bound reported.remove reported.unlinked reported.barrier
  have visible : WalSegmentCollectionRetry state.writer.wal reported.pending.image.visible := by
    change WalSegmentCollectionRetry state.writer.wal reported.barrier.after.visible
    rw [invariant.visible]
    exact (invariant.trace.projects ready.layout).1
  have returned := reported.returned valid
  have stopped : reported.run = .error (IO.userError s!"sync failed for '{state.session.directory.path}': {cause}")
      (.poisoned, ⟨(state.cache, reported.pending.image), reported.pending.owners⟩) := by
    rcases failed with before | after
    · simpa only [before, NativeReadyWalCollection.pending] using returned
    · simpa only [after, NativeReadyWalCollection.pending] using returned
  obtain ⟨directory, _, _, _⟩ := reported.retainsCustody valid
  obtain ⟨owner, lock, lockObject⟩ := reported.retainsLock
  exact ⟨stopped, effect, reported.reachesBarrier, reported.censusPreserved, ready.held, directory, owner,
    directory ▸ reported.barrier.directoryLive, owner ▸ reported.barrier.writerLive, lock, lockObject,
    reported.unlinked.completedNamesAbsent rfl rfl, preparesCoveredWalRetry ready visible, fun sealed survives => preparesCoveredWalRetry ready (survive sealed survives),
    sameHistory, replay⟩

end Alvoki.Storage.DiskSession
