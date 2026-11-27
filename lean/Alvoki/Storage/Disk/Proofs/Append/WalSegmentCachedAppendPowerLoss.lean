import Alvoki.Storage.Disk.Proofs.Append.WalSegmentAppendPowerLoss
import Alvoki.Storage.Disk.WalSegmentCachedExtentReports

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

private theorem CanonicalKeeperLayout.replacesTail {files history}
    (layout : CanonicalKeeperLayout files history) (nonempty : layout.tail ≠ ByteArray.empty) :
    layout.plan.finishActions = steps layout.plan.newer true := by
  have width : layout.plan.keeperSize = layout.keeper.bytes.size := layout.target.trimmedSize.symm
  have positive : 0 < layout.tail.size := by
    apply Nat.pos_of_ne_zero
    exact fun zero => nonempty (ByteArray.size_eq_zero_iff.mp zero)
  have larger : layout.plan.keeperSize < layout.plan.keeperBytes.size := by
    change layout.plan.keeperSize < (layout.keeper.bytes ++ layout.tail).size
    rw [width, ByteArray.size_append]
    omega
  simp [Plan.finishActions, Plan.alignedWithoutPrune, Plan.actions, Nat.ne_of_gt larger, larger]

/-- From power loss inside the first append, the cached worker can reopen
after any admitted retry prefix. A remaining tail forces replacement.
The resulting writer keeps the exact checkpoint, acknowledged history,
and the marker-selected keeper in both the visible and durable image. -/
theorem FirstAppendCut.reopensRetainedCached (cut : FirstAppendCut) {directory descriptor before}
    (ready : before.RetainedReady directory descriptor)
    {tail : ByteArray} (survives : tail ∈ ByteArray.empty :: cut.crashTails)
    {retry : LockedFileState FileImage}
    (failures : BoundedReopenTrace directory (fun target => target = before.target)
      (cut.crashed before directory tail) retry)
    {nextDescriptor nextRef : Nat} (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < nextRef)
    (acquisition : TryLockObserves retry.owners directory (.ok true)) (unlock : UnlockReport)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit) :
    BoundedReopenTrace directory (fun target => target = before.target)
      ⟨cut.physical before, before.owners⟩ (cut.crashed before directory tail) ∧
    ∃ selected : CanonicalKeeperLayout retry.image before.history,
      selected.target = before.target ∧
      (retry.image.keeper.active = (cut.crashed before directory tail).image.keeper.active → selected.tail = tail) ∧
      (selected.tail ≠ ByteArray.empty → selected.plan.finishActions = steps selected.plan.newer true) ∧
      ∀ raw : HealthyBoundedWalReports directory (retry.owners.set (directory.file .lock) (some nextDescriptor))
          nextDescriptor before.wal retry.image.directory.active selected.range.watermark
          before.published.durable selected.tail,
        ∀ sizes : SizedCheckpointRunReports directory raw.reports retry.image.directory.active.manifest
          before.published.durable,
        ∀ cached : CachedWalFileReports directory raw.reports before.wal selected.range.watermark selected.tail,
        sync #[directory.path] retry.image = .ok () retry.image.syncDirectory →
        (∀ action prior next,
          ReachesAction selected.target retry.image.syncDirectory selected.plan.finishActions action prior →
          prior.effect selected.target action = some next →
          performPaths directory selected.plan removeFile throw write sync renameFile action prior = .ok () next) →
        ∃ session final, ∃ writer : SegmentedWriterState,
          runOpenWithInstallation directory nextDescriptor nextRef (.ok true) unlock
            (raw.reopenCached sizes cached removeFile write sync renameFile) retry = .ok session final ∧
          session.directory = directory ∧ session.descriptor = nextDescriptor ∧
          session.phase = .ready writer.installed ∧ writer.files = final.image ∧ writer.owners = final.owners ∧
          final.image.Ready before.target ∧
          writer.wal = { before.wal with directory := final.image.directory } ∧
          writer.target = before.target ∧ writer.history = before.history ∧
          writer.published.durable = before.published.durable ∧ writer.checkpoint = before.checkpoint ∧
          writer.installed.generation = before.installed.generation ∧ writer.RetainedReady directory nextDescriptor := by
  obtain ⟨powerLoss, selected, target, install⟩ := cut.reopensRetained ready survives failures
    (nextDescriptor := nextDescriptor) liveRefs fresh acquisition unlock removeFile write sync renameFile
  have unchangedTail (same : retry.image.keeper.active = (cut.crashed before directory tail).image.keeper.active) :
      selected.tail = tail := by
    let selectedBytes := WAL.encode (before.history.drop before.wal.active.first)
    change retry.image.keeper.active = some (selectedBytes ++ tail) at same
    have keeperBytes : selected.keeper.bytes = selectedBytes := by
      change selected.target.trimmed = selectedBytes
      rw [target, ready.resumed.contents, ready.active]
    have bytes := Option.some.inj (selected.visible.symm.trans same)
    rw [keeperBytes] at bytes
    exact (ByteArray.append_right_inj selectedBytes).mp bytes
  refine ⟨powerLoss, selected, target, unchangedTail, selected.replacesTail, ?_⟩
  intro raw sizes cached settles healthy
  have pair : retry.image.directory.active = before.target.pair := congrArg Target.pair target
  have chosen : before.wal.Selects retry.image.directory.active := by
    rw [pair, ← ready.walPair]
    exact List.mem_cons_self ..
  have checkpoint : SelectedIntegrityCheckpoint before.published.durable retry.image.directory.active.manifest
      before.checkpoint := by
    rw [pair]
    exact ready.resumed.selected
  have cachedEq := raw.reopenCached_eq sizes cached ready.layout ready.valid chosen selected.decoded rfl
    selected.through checkpoint removeFile write sync renameFile
  obtain ⟨session, final, writer, ran, path, lock, phase, files, owners, wal, writerTarget, history,
    durable, checkpoint, generation, nextReady⟩ := install raw settles healthy
  have finalReady : final.image.Ready before.target := by
    rw [← files, ← writerTarget]
    exact nextReady.resumed.ready
  rw [cachedEq]
  exact ⟨session, final, writer, ran, path, lock, phase, files, owners, finalReady, wal, writerTarget,
    history, durable, checkpoint, generation, nextReady⟩

end Alvoki.Storage.DiskSession
