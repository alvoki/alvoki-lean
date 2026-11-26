import Alvoki.Storage.Disk.RotationDirectoryFsyncStop
import Alvoki.Storage.Disk.CapturedAlignedInstallation
import Alvoki.Storage.Disk.PendingClientReplay

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WalSegmentRotation

variable {directory : DiskDirectory} {before : SegmentedWriterState}
  {lookup : FilePath → Except IO.Error IO.FS.Metadata} {inventory : DescriptorInventory}
  {parent : RotationCreateParent directory before lookup inventory}
  {created : RotationRawSuccessor parent}

/-- The reported effective rotation keeps the new empty successor and
the old selected checkpoint. Power loss makes the original lock vacant. -/
def RotationDirectoryFsyncStop.effectiveCrash (report : RotationDirectoryFsyncStop created) : LockedFileState FileImage :=
  report.cut.crashedFiles before.wal.directory.active true

theorem RotationDirectoryFsyncStop.effectiveCrashVacant (report : RotationDirectoryFsyncStop created) :
    TryLockObserves report.effectiveCrash.owners directory (.ok true) := by
  intro _
  simp [effectiveCrash, RotationInFlightCut.crashedFiles, RotationInFlightCut.released, LockOwners.set]

/-- The next healthy aligned attempt supplies its admitted callbacks and
stable child resolutions for the same directory, lock and successor.
The final session and its table come from executing the shared open. -/
structure RotationAlignedOpenReports (report : RotationDirectoryFsyncStop created) (input : FilePath)
    (postCrash : DescriptorInventory) (layout : CanonicalKeeperLayout report.effectiveCrash.image before.history)
    (selected : SelectedIntegrityCheckpoint before.published.durable
      report.effectiveCrash.image.directory.active.manifest before.checkpoint) where
  admission : CensusOpenAdmissionReports input directory postCrash report.effectiveCrash
  callbacks : CapturedAlignedCallbacks admission
  reads : CapturedMarkedReadReports admission layout before.published
  finish : CapturedAlignedFinish callbacks reads report.effectiveCrashVacant selected
  marker : IO.FS.Metadata
  markerFound : admission.lookup (directory.file .walBoundary) (admission.reached, admission.held) =
    .ok (.ok marker) (admission.reached, admission.held)
  root : admission.root = parent.root
  objects : admission.view.modelObject = report.after.view.modelObject
  lock : admission.view.child admission.root "LOCK" = some parent.lock.child
  markerChild : admission.view.child admission.root "WAL.commit" = some parent.marker.child
  successor : admission.view.child admission.root
    (renderWalSegmentName (before.installed.walBytes / WAL.frameSize)) = some created.child.child

/-- Join the effective interrupted rotation to the direct captured
aligned reopen. The reported survivor fixes the new empty keeper object;
the prior manifest and exact held reads supply the same checkpoint and
WAL replay. The next attempt's successful primitive reports derive its
returned session and guarded reads. -/
theorem RotationDirectoryFsyncStop.reopensEffectiveAligned
    (report : RotationDirectoryFsyncStop created) (effective : report.effective = true)
    {first : Nat} {initial : EStateM.Result IO.Error (LockedFileState State) SegmentedSession}
    (start : BootstrapClientStart directory first initial)
    (client : SegmentedClientReadTrace directory first start.writer allowCollection log reads parent.owner.description before)
    {input : FilePath} (postCrash : DescriptorInventory) :
    (∀ (layout : CanonicalKeeperLayout report.effectiveCrash.image before.history),
      layout.keeper.first = before.installed.walBytes / WAL.frameSize →
      layout.keeper.bytes = ByteArray.empty →
      layout.tail = ByteArray.empty →
      ∀ selected : SelectedIntegrityCheckpoint before.published.durable
        report.effectiveCrash.image.directory.active.manifest before.checkpoint,
      Nonempty (RotationAlignedOpenReports report input postCrash layout selected)) →
    report.run = .error directory.path
      (.poisoned, ⟨(report.toRotationSuccessorFileIssue.atIssue, report.cut.image), before.owners⟩) ∧
    ∃ (layout : CanonicalKeeperLayout report.effectiveCrash.image before.history)
      (selected : SelectedIntegrityCheckpoint before.published.durable
        report.effectiveCrash.image.directory.active.manifest before.checkpoint)
      (next : RotationAlignedOpenReports report input postCrash layout selected)
      (session : SegmentedSession) (final : LockedFileState FileImage) (installed : Installed),
      next.finish.run = .ok session (next.finish.census, final) ∧
      next.admission.owner ∈ next.finish.census.slots ∧ next.admission.cached ∈ next.finish.census.slots ∧
      session.directory = directory ∧ session.phase = .ready installed ∧ final.owners.Owns directory session.descriptor ∧
      next.admission.root = parent.root ∧
      next.admission.reached.inode next.admission.cached.description =
        report.directoryHandle.1.inode report.directoryHandle.2.1.description ∧
      next.admission.reached.inode session.descriptor = inventory.inode parent.owner.description ∧
      final.image.directory.active = before.wal.directory.active ∧ final.image.Ready layout.target ∧
      installed.walBytes = before.installed.walBytes ∧ installed.activeFirst = before.installed.walBytes / WAL.frameSize ∧
      installed.generation = before.installed.generation ∧
      layout.keeper.bytes = ByteArray.empty ∧
      next.reads.wal.keeper.observesFile.object = inventory.inode created.raw.description ∧
      report.after.inodes.crashBytes next.reads.wal.keeper.observesFile.object = [ByteArray.empty] ∧
      (∃ marker, before.wal.directory.active.walBoundary = some marker ∧
        next.reads.catalog.inventory.reports.readOptional (directory.file .walBoundary) = .ok (some marker) ∧
        ∃ file : next.reads.reads.ObservesFile (directory.file .walBoundary) marker,
          file.object = report.after.view.modelObject parent.marker.child ∧
          report.after.inodes.crashBytes file.object = [marker]) ∧
      recoverSelected (before.checkpoint.getD (.empty, 0)).1 (WAL.encode before.history) = .ok installed.table ∧
      InstalledClientReplay log reads before.history installed session := by
  intro observe
  let pair := before.wal.directory.active
  let cut := report.cut
  let wal := cut.survivingWal pair true
  have ready := (client.writes.preservesRetained (start.bootstrap.writerReady start.held).toRetained).1
  have survives : some created.child.child ∈
      report.after.crashNames (renderWalSegmentName (before.installed.walBytes / WAL.frameSize)) := by
    rw [report.settled.2.1 effective]
    exact List.mem_singleton_self _
  have synced : report.after.inodes.crashBytes (inventory.inode created.raw.description) = [ByteArray.empty] := by
    rw [report.bytes, created.syncedBytes]
  have payload : ByteArray.empty ∈ report.after.inodes.crashBytes (report.after.view.modelObject created.child.child) := by
    rw [report.view, created.inode, synced]
    exact List.mem_singleton_self _
  obtain ⟨canSurvive, empty, _⟩ := report.selectedKeeperPayload survives payload
  have metadata : pair ∈ cut.image.metadata.crashImages := by
    simp [pair, cut, RotationDirectoryFsyncFailure.cut, RotationCreateParent.cutAtBarrier, effective,
      DirectoryPublication.Image.syncDirectory]
  have lost : WalSegmentRotation.Trace before.wal (cut.released pair true).image := .crash cut.trace pair metadata canSurvive
  have decoded : (cut.released pair true).image.metadata.active.walRange = some before.target.range := by
    change pair.walRange = _
    rw [show pair = before.target.pair from ready.walPair]
    exact before.target.decoded
  obtain ⟨_, _, _, _, layout, sameRange, keeper, tail, descriptors, offsets, prepared⟩ :=
    lost.settledReopenLayout (ready.rotationInput cut.nonempty) ready.layout ready.valid decoded ready.resumed.through
  have successor : wal.active.first = before.installed.walBytes / WAL.frameSize := by
    change before.wal.active.last = _
    rw [ready.layout.activeEnd, ready.resumed.bytes, WAL.encode_size, Nat.mul_comm,
      Nat.mul_div_cancel _ (by decide : 0 < WAL.frameSize)]
  have first := (congrArg WalSegment.first keeper).trans successor
  have emptyKeeper : layout.keeper.bytes = ByteArray.empty := (congrArg WalSegment.bytes keeper).trans empty
  have selected : SelectedIntegrityCheckpoint before.published.durable
      report.effectiveCrash.image.directory.active.manifest before.checkpoint := by
    change SelectedIntegrityCheckpoint before.published.durable pair.manifest before.checkpoint
    rw [show pair = before.target.pair from ready.walPair]
    exact ready.resumed.selected
  have accepted : before.published.AcceptsVersioned before.history.length.toUInt64
      (WAL.Boundary.CheckpointRepresentsPrefix before.history) report.effectiveCrash.image.directory.active.manifest := by
    change before.published.AcceptsVersioned _ _ pair.manifest
    rw [show pair = before.target.pair from ready.walPair]
    exact ready.resumed.accepted
  obtain ⟨next⟩ := observe layout first emptyKeeper tail selected
  have following := next.reads.walReads.selectedAfterWatermark (sameRange.symm ▸ offsets) (sameRange.symm ▸ descriptors)
  obtain ⟨session, final, returned, finalPair, actual⟩ := next.finish.installsAfterVacancy
    next.markerFound prepared.newer following accepted ready.resumed.ordered
  have replay : PendingClientReplay log reads before.history := client.keyValueRefinement start.bootstrap start.held
  obtain ⟨actualSession, actualFinal, installed, actualCheckpoint, sameReturn, phase, exactCheckpoint, recovered, answers⟩ :=
    CachedRetryInstalled.refinesPendingClient actual replay
  obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj sameReturn
  have sameCheckpoint := exactCheckpoint.uniqueResult selected
  have endpoint : session.directory = directory ∧ session.descriptor = next.admission.owner.description ∧
      final.owners.Owns directory session.descriptor ∧ final.image.Ready layout.target ∧
      installed.walBytes = before.installed.walBytes ∧ installed.activeFirst = before.installed.walBytes / WAL.frameSize ∧ installed.generation = before.installed.generation := by
    obtain ⟨opened, checkpoint, _, nextSession, nextFinal, same, path, owner, installedPhase, _, _, _, _, held,
      _, _, _, filesReady, _, checkpointSelected, _, generation, bytes, installedKeeper, _⟩ := actual
    obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj same
    obtain rfl := Phase.ready.inj (installedPhase.symm.trans phase)
    have previous := checkpointSelected.uniqueResult selected
    have sized : opened.installed.walBytes = before.installed.walBytes := by
      change opened.walBytes.toNat = _
      rw [bytes, ready.resumed.bytes, WAL.encode_size, Nat.mul_comm]
    exact ⟨path, owner, held, filesReady, sized, installedKeeper.trans first, generation.trans
      ((congrArg (fun value : Option (PackedTable × UInt64) => (value.getD (.empty, 0)).2) previous).trans
        ready.resumed.generation.symm)⟩
  obtain ⟨path, owner, held, filesReady, sized, installedKeeper, generation⟩ := endpoint
  have sameKeeper : next.reads.wal.keeper.observesFile.object = inventory.inode created.raw.description := by
    let file := next.reads.wal.keeper
    have bound : next.admission.view.child next.admission.root (renderWalSegmentName layout.keeper.first) =
        some created.child.child := first.symm ▸ next.successor
    have child := file.calls.statLookup.child_eq bound
    change file.calls.statObject = inventory.inode created.raw.description
    rw [← file.calls.identifiedStat, child, next.objects, report.view]
    exact created.inode
  refine ⟨report.stopsSchedule, layout, selected, next, session, final, installed, returned,
    next.finish.lockRetained, next.finish.directoryRetained, path, phase, held, next.root, ?_, ?_,
    finalPair, filesReady, sized, installedKeeper, generation, emptyKeeper, sameKeeper, sameKeeper.symm ▸ synced, ?_,
    sameCheckpoint ▸ recovered, answers⟩
  · obtain ⟨_, _, _, _, sameDirectory, _⟩ := next.admission.opened.captures
    calc
      next.admission.reached.inode next.admission.cached.description =
          next.admission.view.modelObject next.admission.root := sameDirectory.symm
      _ = parent.files.view.modelObject parent.root := by
        rw [next.root, next.objects, report.view, created.objects]
      _ = _ := report.captureObject
  · have sameLock := Option.some.inj (next.reads.lockEntry.symm.trans next.lock)
    rw [owner, ← next.reads.identifiesLock, sameLock, next.objects, report.view, created.objects]
    exact parent.lockObject
  · obtain ⟨_, _, _, _, _, marker, stored, stable⟩ := report.keepsKeeperMarker
    have selectedMarker : report.effectiveCrash.image.directory.active.walBoundary = some marker := stored
    obtain ⟨file, _⟩ := next.reads.metadata.markerFile marker selectedMarker
    have child := file.calls.statLookup.child_eq next.markerChild
    have same : file.observesFile.object = report.after.view.modelObject parent.marker.child := by
      change file.calls.statObject = _
      rw [← file.calls.identifiedStat, child, next.objects]
    exact ⟨marker, stored, selectedMarker ▸ next.reads.metadata.markerRead layout.decoded,
      file.observesFile, same, same.symm ▸ stable⟩

end Alvoki.Storage.DiskSession
