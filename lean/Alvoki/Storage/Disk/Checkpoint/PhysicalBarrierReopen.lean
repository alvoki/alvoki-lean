import Alvoki.Storage.Disk.Checkpoint.PhysicalWalAtBarrier
import Alvoki.Storage.Disk.Checkpoint.Reopen.HeldInstallation
import Alvoki.Storage.Disk.CapturedAlignedInstallation

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair SyncHandleRouting

/-- Power loss settles the reported selected manifest, keeps the existing
WAL, and releases the database lock. The next open has a new census. -/
def CheckpointPowerCut.barrierCrashState {directory : DiskDirectory} {before : SegmentedWriterState}
    (_cut : CheckpointPowerCut directory before) (binding : Option ByteArray) : LockedFileState FileImage :=
  ⟨before.wal.checkpointReopenFiles (.settled ⟨binding, before.wal.directory.active.walBoundary⟩) none,
    before.owners.set (directory.file .lock) none⟩

theorem CheckpointPowerCut.barrierCrashVacant {directory : DiskDirectory} {before : SegmentedWriterState}
    (cut : CheckpointPowerCut directory before) (binding : Option ByteArray) :
    TryLockObserves (cut.barrierCrashState binding).owners directory (.ok true) := by
  intro _
  simp [barrierCrashState, LockOwners.set]

/-- Compare canonical child lookups across the reported power-loss map
and the stable namespace of the next held open. -/
def CheckpointCrashChild (names : FilePath → Option Nat) (admission : CensusOpenAdmissionReports input directory inventory retry)
    (path : FilePath) (name : String) : Prop :=
  (admission.view.child admission.root name).map admission.view.modelObject = names path

private theorem CheckpointCrashChild.sameObject {input directory inventory retry names path name}
    {admission : CensusOpenAdmissionReports input directory inventory retry} {reads object payload}
    (child : CheckpointCrashChild names admission path name)
    (file : RunChunkPathReport reads path name admission.root admission.view)
    (bound : admission.view.child admission.root name = some object)
    (contents : reads.objectBytes (admission.view.modelObject object) = some payload) :
    names path = some (file.observesFile bound contents).object := by
  unfold CheckpointCrashChild at child
  rw [bound, Option.map_some] at child
  have stat := (congrArg admission.view.modelObject (file.statLookup.child_eq bound)).symm.trans file.identifiedStat
  exact child.symm.trans (congrArg some stat)

/-- The primitive observations for the next healthy aligned attempt.
The reported durable run map projects payloads, so the separate child
reports connect those payloads to the surviving inodes. -/
structure CheckpointBarrierAlignedReports (input : FilePath) (directory : DiskDirectory)
    (inventory : DescriptorInventory) (retry : LockedFileState FileImage)
    {history : List WAL.Write} (layout : CanonicalKeeperLayout retry.image history)
    (published : Image) (vacant : TryLockObserves retry.owners directory (.ok true))
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint)
    (names : FilePath → Option Nat) where
  admission : CensusOpenAdmissionReports input directory inventory retry
  callbacks : CapturedAlignedCallbacks admission
  reads : CapturedMarkedReadReports admission layout published
  finish : CapturedAlignedFinish callbacks reads vacant selected
  marker : IO.FS.Metadata
  markerFound : admission.lookup (directory.file .walBoundary) (admission.reached, admission.held) =
    .ok (.ok marker) (admission.reached, admission.held)
  manifestChild : CheckpointCrashChild names admission (directory.file .manifest) "MANIFEST"
  markerChild : CheckpointCrashChild names admission (directory.file .walBoundary) "WAL.commit"
  keeperChild : CheckpointCrashChild names admission (directory.file (.walSegment layout.keeper.first))
    (renderWalSegmentName layout.keeper.first)
  sealChild : ∀ segment ∈ layout.sealed,
    CheckpointCrashChild names admission (directory.file (.walSegment segment.first)) (renderWalSegmentName segment.first)
  runChild : ∀ bytes metadata, retry.image.directory.active.manifest = some bytes →
    Manifest.IntegrityCheckpoint.decode bytes = .ok metadata → ∀ index < metadata.header.runCount.toNat,
    CheckpointCrashChild names admission (directory.file (.run metadata.header.generation index))
      (renderRunFileName metadata.header.generation index)

/-- The same joint survivor that supplies the manifest and retained WAL
also supplies the ordered run payloads for the next admitted session.
The power-loss edge leaves the earlier submissions and reads unchanged. -/
theorem CheckpointPowerCut.reopensPhysicalBarrierAligned {directory : DiskDirectory}
    {before : SegmentedWriterState} {first writer : Nat}
    {initial : EStateM.Result IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession}
    (cut : CheckpointPowerCut directory before)
    (start : BootstrapClientStart directory first initial)
    (client : SegmentedClientReadTrace directory first start.writer allowCollection log reads writer before)
    (calls : CheckpointManifestDirectoryCalls) (atRun : Nat → CheckpointManifestState)
    (runs : CheckpointManifestState → RunUnlinkImage)
    (runPrefix : CheckpointRunPrefix cut (calls.perform cut) atRun runs)
    (reached : CheckpointManifestDirectoryReached cut calls (atRun cut.checkpoint.table.runs.length) runs)
    (completed : cut.completed = runSteps cut.checkpoint.table.runs.length ++
      [.syncRunsDirectory, .manifest .writeStaged, .manifest .syncStaged, .manifest .renameStaged])
    (wal : reached.WalFrame) (names : FilePath → Option Nat) (survives : names ∈ wal.crashNames reached.interrupted)
    (binding : Option ByteArray) (manifestBytes : binding ∈ manifestCrashBytes reached.interrupted (names (directory.file .manifest)))
    {input : FilePath} (inventory : DescriptorInventory) :
    let cache := (atRun cut.checkpoint.table.runs.length).1.consume (directory.file .stagedManifest)
    let atBarrier : CheckpointManifestState := (cache, reached.renamed)
    let physical := runs (cache, reached.interrupted)
    let retry := cut.barrierCrashState binding
    (∀ bytes metadata, binding = some bytes → Manifest.IntegrityCheckpoint.decode bytes = .ok metadata →
      ∀ index < metadata.header.runCount.toNat, ∀ payload,
      physical.guaranteed metadata.header.generation index = some payload →
      ∃ inode, names (directory.file (.run metadata.header.generation index)) = some inode ∧
        reached.interrupted.crashBytes inode = [payload]) →
    (∀ (layout : CanonicalKeeperLayout retry.image before.history) (published : Image),
      layout.keeper = before.wal.active → layout.tail = ByteArray.empty →
      layout.sealed ++ [layout.keeper] = before.wal.readDescriptors layout.range.watermark →
      published.durable = physical.guaranteed →
      ∀ {checkpoint}, ∀ selected : SelectedIntegrityCheckpoint published.durable binding checkpoint,
        Nonempty (CheckpointBarrierAlignedReports input directory inventory retry layout published
          (cut.barrierCrashVacant binding) selected names)) →
    CheckpointIssue ((calls.callbacks directory).perform directory) (.ready before.installed)
      ⟨atRun 0, before.owners⟩ cut.checkpoint.prepared cut.checkpoint.manifest
      cut.completed (.manifest .syncDirectory) atBarrier ∧
    wal.objects.Retains directory before (checkpointWalPathView reached.bindings wal.crashNames reached.interrupted) ∧
    (cut.tookEffect = true → binding = some cut.checkpoint.manifest) ∧
    ∃ (layout : CanonicalKeeperLayout retry.image before.history) (published : Image)
      (checkpoint : Option (PackedTable × UInt64))
      (selected : SelectedIntegrityCheckpoint published.durable binding checkpoint)
      (openReports : CheckpointBarrierAlignedReports input directory inventory retry layout published
        (cut.barrierCrashVacant binding) selected names)
      (session : SegmentedSession) (final : LockedFileState FileImage) (ready : Installed),
      published.durable = physical.guaranteed ∧
      openReports.finish.run = .ok session (openReports.finish.census, final) ∧
      session.phase = .ready ready ∧ final.owners.Owns directory session.descriptor ∧
      final.image.directory.active = ⟨binding, before.wal.directory.active.walBoundary⟩ ∧
      openReports.reads.wal.keeper.observesFile.object = wal.objects.keeper ∧
      openReports.reads.catalog.inventory.reports.readOptional (directory.file .manifest) = .ok binding ∧
      (match binding with
        | none => names (directory.file .manifest) = none
        | some bytes =>
          ∃ file : openReports.reads.reads.ObservesFile (directory.file .manifest) bytes,
            names (directory.file .manifest) = some file.object ∧ bytes ∈ reached.interrupted.crashBytes file.object) ∧
      (∀ bytes metadata, binding = some bytes → Manifest.IntegrityCheckpoint.decode bytes = .ok metadata →
        ∀ index < metadata.header.runCount.toNat, ∀ payload,
        physical.guaranteed metadata.header.generation index = some payload →
        ∃ file : openReports.reads.reads.ObservesFile (directory.file (.run metadata.header.generation index)) payload,
          names (directory.file (.run metadata.header.generation index)) = some file.object ∧
          reached.interrupted.crashBytes file.object = [payload]) ∧
      (((checkpoint.getD (.empty, 0)).2 = before.installed.generation ∧
          binding = before.wal.directory.active.manifest) ∨
        ((checkpoint.getD (.empty, 0)).2 = SegmentedCheckpointReport.generation before ∧
          binding = some cut.checkpoint.manifest)) ∧
      recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode before.history) = .ok ready.table ∧
      InstalledClientReplay log reads before.history ready session := by
  intro cache atBarrier physical retry runSurvivors observe
  have ready := (client.writes.preservesRetained (start.bootstrap.writerReady start.held).toRetained).1
  obtain ⟨issue, _, keptWal, pending⟩ :=
    cut.replaysPhysicalWalAtManifestDirectory start client calls atRun runs runPrefix reached completed wal
  obtain ⟨settledNew, checkpoint, _, _, selected, generation, _, _, _, _, replay⟩ := pending names survives binding manifestBytes
  obtain ⟨_, _, _, _, publication, reachedPublication⟩ := cut.atManifestDirectory ready calls atRun runs runPrefix reached completed
  have survived : binding ∈ reached.crashBindings.flatMap (manifestCrashBytes reached.interrupted) := by
    refine List.mem_flatMap.mpr ⟨names (directory.file .manifest), ?_, manifestBytes⟩
    rw [← wal.manifestBindings]
    exact List.mem_map_of_mem survives
  have admitted := reachedPublication.admitted binding survived
  obtain ⟨logical, executed, walLayout, valid, inputs, _⟩ := cut.selectsAcknowledgedHistory ready
  have same := Option.some.inj (executed.symm.trans reachedPublication.executed)
  subst logical
  let pair : DirectoryPublication.Bindings := ⟨binding, before.wal.directory.active.walBoundary⟩
  have pairSurvives : pair ∈ (publication.segmentedCheckpointView before.wal).directory.crashImages :=
    List.mem_map.mpr ⟨binding, admitted, rfl⟩
  obtain ⟨accepted, range, decoded, atEnd⟩ := inputs pair (List.mem_cons_of_mem _ pairSurvives)
  obtain ⟨layout, rangeEq, keeper, tail, descriptors, offsets, _, crashKeeper, keptPrefix, later⟩ :=
    walLayout.checkpointReopenLayout valid (.crash pairSurvives) decoded atEnd none
  have origin : binding = before.wal.directory.active.manifest ∨ binding = some cut.checkpoint.manifest :=
    generation.imp And.right And.right
  let published : Image := { publication with durable := physical.guaranteed }
  have agrees := cut.selectedRunAgreement ready publication binding origin physical.guaranteed
    reachedPublication.newRuns reachedPublication.priorRuns
  have accepted := SelectedRunsAgree.acceptsVersioned (actual := published) agrees decoded accepted
  obtain ⟨openReports⟩ := observe layout published keeper tail (rangeEq.symm ▸ descriptors) rfl selected
  have following := openReports.reads.walReads.selectedAfterWatermark (rangeEq.symm ▸ offsets) (rangeEq.symm ▸ descriptors)
  have prepared : Prepared retry.image layout.target layout.plan :=
    layout.prepared crashKeeper keptPrefix (rangeEq.symm ▸ later)
  obtain ⟨session, final, returned, finalPair, installed⟩ :=
    openReports.finish.installsAfterVacancy openReports.markerFound prepared.keeperPrefix prepared.newer
      following accepted ready.resumed.ordered
  obtain ⟨sameSession, sameFinal, table, actualCheckpoint, sameReturn, phase, actualSelected, recovered, refined⟩ :=
    CachedRetryInstalled.refinesPendingClient installed replay
  obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj sameReturn
  have sameCheckpoint := actualSelected.uniqueResult selected
  refine ⟨issue, keptWal, settledNew, layout, published, checkpoint, selected, openReports,
    session, final, table, rfl, returned, phase, ?_, finalPair, ?_,
    openReports.reads.metadata.manifestRead layout.decoded,
    ?_, ?_, generation, sameCheckpoint ▸ recovered, refined⟩
  · obtain ⟨_, _, _, _, _, observed, _, _, _, _, _, _, _, held, _⟩ := installed
    obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj observed
    exact held
  · let file := openReports.reads.wal.keeper
    have opened := openReports.keeperChild.sameObject file.calls file.bound file.contents
    have samePath := congrArg (fun (segment : WalSegment) => names (directory.file (.walSegment segment.first))) keeper
    exact Option.some.inj (opened.symm.trans (samePath.trans (keptWal.2.1.2 _ ⟨names, survives, rfl⟩)))
  · cases visible : binding with
    | none =>
      have absent := (openReports.reads.metadata.manifestMissing visible).1
      exact openReports.manifestChild.symm.trans (by simp [absent])
    | some bytes =>
      obtain ⟨⟨file⟩, _⟩ := openReports.reads.metadata.manifestFile bytes visible
      have bound := openReports.manifestChild.sameObject file.calls file.bound file.contents
      refine ⟨file.observesFile, bound, ?_⟩
      rw [visible, bound, manifestCrashBytes] at manifestBytes
      obtain ⟨fromInode, present, same⟩ := List.mem_map.mp manifestBytes
      exact Option.some.inj same ▸ present
  · intro bytes metadata visible decoded index within payload stored
    obtain ⟨inode, bound, durable⟩ := runSurvivors bytes metadata visible decoded index within payload stored
    obtain ⟨object, childBound, contents, ⟨file⟩⟩ := openReports.reads.runs bytes metadata visible decoded index within payload stored
    have observed := (openReports.runChild bytes metadata visible decoded index within).sameObject file childBound contents
    let read := file.observesFile childBound contents
    have sameObject : read.object = inode := Option.some.inj (observed.symm.trans bound)
    exact ⟨read, observed, sameObject.symm ▸ durable⟩

end Alvoki.Storage.DiskSession
