import Alvoki.Storage.Disk.SegmentedCheckpointPowerLoss
import Alvoki.Storage.Disk.CachedMarkedRetryInstallation

namespace Alvoki.Storage.DiskSession

open WalSegmentRepair

private theorem followingAfterSelection {offsets selected : List Nat} {watermark first : Nat}
    (chosen : selectWalSegmentReads offsets watermark = some (first, selected))
    (ordered : selected.Pairwise (· < ·)) (head : selected.head? = some first) :
    ∀ start ∈ selected.drop 1, watermark < start := by
  unfold selectWalSegmentReads at chosen
  cases maximum : (offsets.filter fun offset => decide (offset ≤ watermark)).max? with
  | none => simp [maximum, Bind.bind, Option.bind] at chosen
  | some greatest =>
    have pair : (greatest, offsets.filter fun offset => decide (greatest ≤ offset)) = (first, selected) := by
      simpa [maximum, Bind.bind, Option.bind, Pure.pure] using chosen
    obtain ⟨rfl, selectedOffsets⟩ := Prod.mk.inj pair
    have upper := (List.max?_eq_some_iff.mp maximum).2
    cases selected with
    | nil => contradiction
    | cons start rest =>
      have exactHead : start = greatest := Option.some.inj head
      subst start
      intro later member
      have greater := (List.pairwise_cons.mp ordered).1 _ member
      have listed := List.mem_filter.mp (selectedOffsets ▸ List.mem_cons_of_mem _ member)
      apply Nat.lt_of_not_ge
      intro within
      exact Nat.not_le_of_gt greater (upper _ (List.mem_filter.mpr ⟨listed.1, decide_eq_true within⟩))

private theorem headOfChain {history : List WAL.Write} {first : Nat} {segments : List WalSegment}
    (chain : WalSegment.Chain history first segments) (nonempty : segments ≠ []) :
    (segments.map WalSegment.first).head? = some first := by
  cases chain with
  | endOfHistory => contradiction
  | cons => rfl

/-- A reached checkpoint primitive can be interrupted without a returned
result. At the final retry, the marked dispatcher reads the checkpoint
selected by the surviving pair, then installs the replay of the same WAL.
The callback packet is indexed by the physical selected layout at that
retry. It supplies its chunk reads and successful reached repair effects. -/
theorem CheckpointPowerCut.reopensFromChunks {files : Type} {directory : DiskDirectory}
    {before : SegmentedWriterState} {writer : Nat} (cut : CheckpointPowerCut directory before)
    (ready : before.RetainedReady directory writer) (published : CheckpointPublication.Image)
    (projected : before.published.executeVersioned cut.checkpoint.plan cut.checkpoint.cut = some published)
    (pair : DirectoryPublication.Bindings) (survives : pair ∈ (published.segmentedCheckpointView before.wal).directory.crashImages)
    (retry : LockedFileState FileImage)
    (failures : BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
      ⟨(physical before published).crash pair (some before.wal.active.bytes) [],
        before.owners.set (directory.file .lock) none⟩ retry)
    (observes : ∀ layout : CanonicalKeeperLayout retry.image before.history,
      layout.keeper = before.wal.active → layout.tail = ByteArray.empty →
      layout.sealed ++ [layout.keeper] = (published.segmentedCheckpointView before.wal).readDescriptors layout.range.watermark →
      Nonempty (MarkedRetryChunkReports files directory layout published)) :
    BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
      ⟨physical before published, before.owners⟩ retry ∧
    ∃ (layout : CanonicalKeeperLayout retry.image before.history)
      (observed : MarkedRetryChunkReports files directory layout published)
      (sizes : SizedCheckpointRunReports directory observed.reported.inventory.reports
        retry.image.directory.active.manifest published.durable)
      (opened : Reopened) (checkpoint : Option (PackedTable × UInt64)) (model : Sequential.SnapshotTable UInt64)
      (session : SegmentedSession) (final : LockedFileState FileImage),
      observed.run = .ok session final ∧ session.directory = directory ∧ session.descriptor = observed.slot.description ∧
      session.phase = .ready opened.installed ∧ final.owners.Owns directory session.descriptor ∧
      retry.image.directory.active = pair ∧ final.image.directory.active = pair ∧ final.image.Ready layout.target ∧
      SelectedIntegrityCheckpoint published.durable pair.manifest checkpoint ∧
      sizes.readPrefix = observed.reads.readPrefix ∧
      ((opened.generation = before.installed.generation ∧ pair.manifest = before.wal.directory.active.manifest) ∨
        (opened.generation = SegmentedCheckpointReport.generation before ∧ pair.manifest = some cut.checkpoint.manifest)) ∧
      opened.walBytes.toNat = before.installed.walBytes ∧ opened.keeper = before.installed.activeFirst ∧
      recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode before.history) = .ok opened.table ∧
      opened.table.committed.toNat = before.history.length ∧ opened.table.RowBounds ∧ opened.table.Refines model ∧
      RepresentsWalHistory before.history model := by
  obtain ⟨reached, executed, walLayout, valid, inputs, crash⟩ := cut.selectsAcknowledgedHistory ready
  have exactPublished : reached = published := Option.some.inj (executed.symm.trans projected)
  subst reached
  obtain ⟨loss, _, _, _, _, _, _, checkpoint, _, _, selected, generation, _, _, _, _⟩ := crash survives
  have lineage := failures.lineage (fun a b selectedPair => CheckpointRetryTarget.unique a b selectedPair)
  rw [physical_eq published ready] at lineage
  have crashDirectory : (published.segmentedCheckpointView before.wal).CheckpointReopenDirectory (.settled pair) :=
    .crash survives
  obtain ⟨layout, _, keeper, tail, descriptors, offsets, prepared, _, accepted⟩ :=
    published.checkpointRetryLayout walLayout valid crashDirectory inputs lineage
  obtain ⟨observed⟩ := observes layout keeper tail descriptors
  have ordered := (List.pairwise_append.mp (List.pairwise_append.mp observed.reported.ordered).1).2.1
  rw [← descriptors] at offsets
  have following := followingAfterSelection offsets ordered (headOfChain layout.chain (by simp))
  have recovered := runOpenWithInstallation_markedRetryFromChunks observed prepared.keeperPrefix prepared.newer
    following accepted ready.resumed.ordered
  obtain ⟨opened, loaded, model, session, final, returned, directoryExact, lock, phase, _, _, _, _, held,
    _, _, _, repaired, _, chosen, replayed, generationRead, bytes, keeperRead, committed, bounds, refines,
    represents, _⟩ := recovered
  have surviving := SegmentedCheckpointPowerLossReport.keepsSelectedPair rfl lineage
  have selectedRetry : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint :=
    surviving.symm ▸ selected
  have same := chosen.uniqueResult selectedRetry
  rw [same] at generationRead replayed
  have exactGeneration := generationRead.symm ▸ generation
  have exactBytes : opened.walBytes.toNat = before.installed.walBytes := by
    rw [bytes, ready.resumed.bytes, WAL.encode_size, Nat.mul_comm]
  have exactKeeper : opened.keeper = before.installed.activeFirst :=
    keeperRead.trans ((congrArg WalSegment.first keeper).trans (ready.resumed.keeper.trans ready.active).symm)
  have finalPair := repaired.selected.trans surviving
  let sizes := SizedCheckpointRunReports.ofChunkReads selectedRetry observed.reads observed.metadata observed.chunks
  exact ⟨loss.trans failures, layout, observed, sizes, opened, checkpoint, model, session, final, returned, directoryExact,
    lock.trans observed.inventoryDescription, phase, held, surviving, finalPair, repaired, selected, rfl,
    exactGeneration, exactBytes, exactKeeper, replayed, committed, bounds, refines, represents⟩

end Alvoki.Storage.DiskSession
