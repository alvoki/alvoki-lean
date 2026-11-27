import Alvoki.Storage.Disk.Proofs.Collection.SegmentedCollectionLiveReopen
import Alvoki.Storage.Disk.WalSegmentCachedExtentReports

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WAL.Boundary

private def withCollectionNamespace {α : Type} (action : EStateM IO.Error FileImage α) :
    EStateM IO.Error (FileImage × WalSealedUnlinkImage) α :=
  fun (files, namespaceImage) => match action files with
    | .ok value after => .ok value (after, namespaceImage)
    | .error cause after => .error cause (after, namespaceImage)

namespace SegmentedCollectionReopenReport

variable {directory : DiskDirectory} {before : SegmentedWriterState} {writer descriptor : Nat}

private def syncFiles (report : SegmentedCollectionReopenReport directory before writer descriptor)
    (paths : Array FilePath) : EStateM IO.Error (FileImage × WalSealedUnlinkImage) Unit :=
  if paths = #[directory.path] then report.syncWithNamespace paths
  else withCollectionNamespace (report.reopen.sync paths)

/-- The cached worker carries the exact sealed namespace through its
directory barrier. Its other callbacks affect the file image. -/
def reopenCachedWithNamespace (report : SegmentedCollectionReopenReport directory before writer descriptor)
    (sizes : SizedCheckpointRunReports directory report.raw.reports
      report.pending.image.visible.directory.active.manifest before.published.durable)
    (cached : CachedWalFileReports directory report.raw.reports report.pending.image.visible
      before.target.range.watermark ByteArray.empty) : EStateM IO.Error (FileImage × WalSealedUnlinkImage) Reopened :=
  report.raw.reopenCachedWithState sizes cached (fun path => withCollectionNamespace (report.reopen.removeFile path))
    (fun path bytes => withCollectionNamespace (report.reopen.write path bytes)) report.syncFiles
    (fun source destination => withCollectionNamespace (report.reopen.renameFile source destination))

private theorem keeperSync_ne_directorySync (directory : DiskDirectory) (first : Nat) :
    #[directory.file (.walSegment first)] ≠ #[directory.path] := by
  intro same
  have paths := congrArg (fun paths : Array FilePath => paths[0]?) same
  have lengths := congrArg (fun path : FilePath => path.toString.length) (Option.some.inj paths)
  simp [DiskDirectory.walSegment_path, renderWalSegmentName] at lengths
  have slash : "/".length = 1 := by decide
  omega

private theorem reopenAligned {state : Type} {owners reader wal pair watermark durable tail}
    (raw : HealthyBoundedWalReports directory owners reader wal pair watermark durable tail)
    (removeFile : FilePath → EStateM IO.Error state (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error state Unit)
    (sync : Array FilePath → EStateM IO.Error state Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error state Unit)
    {initial middle final : state} {plan : Plan} {opened : Reopened}
    (reading : prepareBoundedMarkedWith directory raw.reports.readOptional raw.list
      (fun path => .ok (raw.reports.lstat path)) raw.reports.readBin raw.readPrefix = .ok (plan, opened, plan.keeperSize))
    (valid : plan.valid = true) (width : plan.keeperBytes.size = plan.keeperSize) (empty : plan.newer = [])
    (metadata : sync #[directory.path] initial = .ok () middle)
    (keeper : sync #[directory.file (.walSegment plan.keeper)] middle = .ok () final) :
    raw.reopenWithState removeFile write sync renameFile initial = .ok opened final := by
  unfold HealthyBoundedWalReports.reopenWithState reopenMarkedBoundedWith
  rw [prepareBoundedMarkedWith_liftReports, reading]
  simp [finishBoundedMarkedOpen, liftExcept, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
    valid, width, empty, metadata, keeper]

/-- After actual collection errors and the observed reopen attempts, the
healthy cached worker settles the exact pending sealed namespace and
installs its unchanged checkpoint and selected WAL payload. -/
theorem installsCachedWithNamespace (report : SegmentedCollectionReopenReport directory before writer descriptor)
    (observed : report.Valid) (ready : before.RetainedReady directory writer)
    (sizes : SizedCheckpointRunReports directory report.raw.reports
      report.pending.image.visible.directory.active.manifest before.published.durable)
    (cached : CachedWalFileReports directory report.raw.reports report.pending.image.visible
      before.target.range.watermark ByteArray.empty) :
    WalSealedUnlinkTrace before.wal report.pending.image.syncDirectory ∧
    ∃ after session final,
      report.Installs after ∧
      runOpenWithInstallation directory report.reopen.descriptor report.reopen.nextRef report.reopen.acquired
        report.reopen.unlock (report.reopenCachedWithNamespace sizes cached)
        ⟨(report.files.image, report.pending.image), report.pending.owners⟩ = .ok session final ∧
      session.phase = .ready after.installed ∧ final.image.1 = after.files ∧ final.owners = after.owners ∧
      final.image.2 = report.pending.image.syncDirectory ∧
      final.image.2.crashSealed = [after.wal.sealed] ∧
      after.wal.readDescriptors before.target.range.watermark = before.wal.readDescriptors before.target.range.watermark ∧
      after.target = before.target ∧ after.history = before.history ∧
      after.published.durable = before.published.durable ∧ after.checkpoint = before.checkpoint ∧
      after.installed.generation = before.installed.generation ∧ after.RetainedReady directory descriptor ∧
      final.image.2 = WalSealedUnlinkImage.start after.wal ∧ session.descriptor = descriptor := by
  have reached := report.attempts.continues (report.failed.keepsNamespace ready).1
  have retry := (reached.projects ready.layout).1
  have pair := (retry.keepsSettledPair ready.walDirectorySettled).1.trans ready.walPair
  have layout := retry.readLayout ready.layout
  have valid := retry.valid ready.valid
  have decoded : report.pending.image.visible.directory.active.walRange = some before.target.range :=
    pair.symm ▸ before.target.decoded
  have checkpoint : SelectedIntegrityCheckpoint before.published.durable
      report.pending.image.visible.directory.active.manifest before.checkpoint := pair.symm ▸ ready.resumed.selected
  have exactDescriptors := retry.keepsReadDescriptors (List.mem_cons_self ..) decoded
  obtain ⟨selected, range, keeper, tail, descriptors, offsets, _, choices, payload, later⟩ :=
    layout.checkpointReopenLayout valid .visible decoded ready.resumed.through report.scratch
  have prepared := selected.prepared choices payload (range.symm ▸ later)
  have aligned : selected.plan.keeperBytes.size = selected.plan.keeperSize := by
    change (selected.keeper.bytes ++ selected.tail).size = _
    rw [tail, ByteArray.append_empty]
    exact selected.target.trimmedSize
  have boundedPlan : selected.boundedPlan = selected.plan := by
    simp [CanonicalKeeperLayout.boundedPlan, CanonicalKeeperLayout.plan, tail]
  let raw : HealthyBoundedWalReports directory
      (report.pending.owners.set (directory.file .lock) (some report.reopen.descriptor)) report.reopen.descriptor
      report.pending.image.visible report.files.image.directory.active selected.range.watermark before.published.durable selected.tail :=
    { report.raw with
      sealed := by rw [range]; exact report.raw.sealed
      keeper := by rw [tail]; exact report.raw.keeper }
  have accepted : before.published.AcceptsVersioned before.history.length.toUInt64 (CheckpointRepresentsPrefix before.history)
      report.files.image.directory.active.manifest := pair.symm ▸ ready.resumed.accepted
  have watermark := congrArg MarkedWalRange.watermark range
  obtain ⟨base, table, _, _, _, reading, _, _, _, _, _, _⟩ := selected.prepareBoundedReports layout keeper
    (watermark.symm ▸ descriptors) (watermark.symm ▸ offsets) rfl accepted ready.resumed.ordered raw
  let opened : Reopened :=
    ⟨table, (base.getD (.empty, 0)).2, (WAL.encode before.history).size.toUInt64, selected.keeper.first⟩
  have readPlan : prepareBoundedMarkedWith directory report.raw.reports.readOptional report.raw.list
      (fun path => .ok (report.raw.reports.lstat path)) report.raw.reports.readBin report.raw.readPrefix =
      .ok (selected.plan, opened, selected.plan.keeperSize) := by
    simpa only [boundedPlan, aligned, opened] using reading
  have keeperPath : selected.plan.keeper = report.pending.image.visible.active.first :=
    congrArg WalSegment.first keeper
  have singleton : selected.plan.newer = [] := rfl
  have plainSync : report.reopen.sync #[directory.path] report.files.image = .ok () report.files.image.syncDirectory :=
    observed.directoryProjection.trans (congrArg projectCollectionBarrier observed.directoryEffect)
  have fileKeeper : report.reopen.sync #[directory.file (.walSegment selected.plan.keeper)]
      report.files.image.syncDirectory = .ok () report.files.image.syncDirectory.syncKeeper := by
    rw [keeperPath]
    exact observed.syncKeeper
  have bounded : report.raw.reopen report.reopen.removeFile report.reopen.write report.reopen.sync
      report.reopen.renameFile report.files.image = .ok opened report.files.image.syncDirectory.syncKeeper :=
    reopenAligned report.raw report.reopen.removeFile report.reopen.write report.reopen.sync
      report.reopen.renameFile readPlan prepared.valid aligned singleton plainSync fileKeeper
  have pairedDirectory : report.syncFiles #[directory.path] (report.files.image, report.pending.image) =
      .ok () (report.files.image.syncDirectory, report.pending.image.syncDirectory) := by
    simpa only [syncFiles, ite_true, barrier] using observed.directoryEffect
  have pairedKeeper : report.syncFiles #[directory.file (.walSegment selected.plan.keeper)]
      (report.files.image.syncDirectory, report.pending.image.syncDirectory) =
      .ok () (report.files.image.syncDirectory.syncKeeper, report.pending.image.syncDirectory) := by
    simp only [syncFiles, ite_eq_right (keeperSync_ne_directorySync directory selected.plan.keeper),
      withCollectionNamespace, fileKeeper]
  have cachedRun : report.reopenCachedWithNamespace sizes cached (report.files.image, report.pending.image) =
      .ok opened (report.files.image.syncDirectory.syncKeeper, report.pending.image.syncDirectory) := by
    unfold reopenCachedWithNamespace
    rw [report.raw.reopenCachedWithState_eq sizes cached layout valid (List.mem_cons_self ..) decoded rfl
      ready.resumed.through checkpoint]
    exact reopenAligned report.raw _ _ _ _ readPlan prepared.valid aligned singleton pairedDirectory pairedKeeper
  obtain ⟨after, installed, next⟩ := report.installs observed ready
  obtain ⟨session, final, _, returned, phase, exactWriter⟩ := installed.opened
  have finalAction := returned
  simp only [BoundedReopenAttempt.run, observed.acquired, observed.reads, runOpenWithInstallation_outcome,
    runOpenWithImage_acquired, bounded] at finalAction
  obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj finalAction
  let finalWithNamespace : LockedFileState (FileImage × WalSealedUnlinkImage) :=
    ⟨(report.files.image.syncDirectory.syncKeeper, report.pending.image.syncDirectory),
      report.pending.owners.set (directory.file .lock) (some report.reopen.descriptor)⟩
  let openedSession : SegmentedSession :=
    ⟨directory, report.reopen.descriptor, .ready opened.installed, report.reopen.nextRef, report.reopen.nextRef + 1⟩
  have installedCache : runOpenWithInstallation directory report.reopen.descriptor report.reopen.nextRef
      report.reopen.acquired report.reopen.unlock (report.reopenCachedWithNamespace sizes cached)
      ⟨(report.files.image, report.pending.image), report.pending.owners⟩ = .ok openedSession finalWithNamespace := by
    rw [observed.acquired, runOpenWithInstallation_outcome, runOpenWithImage_acquired, cachedRun]
  have keptReads : after.wal.readDescriptors before.target.range.watermark =
      before.wal.readDescriptors before.target.range.watermark := by
    rw [exactWriter]
    exact exactDescriptors
  have sameCheckpoint : after.checkpoint = before.checkpoint := by rw [exactWriter]; rfl
  have generation := next.resumed.generation.trans (sameCheckpoint.symm ▸ ready.resumed.generation.symm)
  refine ⟨reached.sync, after, openedSession, finalWithNamespace, installed, installedCache, ?_, ?_, ?_, rfl, ?_,
    keptReads, ?_, installed.history, ?_, sameCheckpoint, generation, next, ?_, observed.descriptorEq⟩ <;>
    rw [exactWriter] <;> first | exact phase | rfl

end SegmentedCollectionReopenReport

end Alvoki.Storage.DiskSession
