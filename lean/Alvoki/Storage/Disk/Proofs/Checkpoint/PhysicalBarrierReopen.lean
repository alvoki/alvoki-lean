import Alvoki.Storage.Disk.Proofs.Checkpoint.BarrierRetryObservations
import Alvoki.Storage.Disk.Proofs.Checkpoint.Reopen.HeldInstallation
import Alvoki.Storage.Disk.Proofs.Session.CapturedAlignedInstallation

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
def CheckpointCrashChild {retry : LockedFileState FileImage}
    (names : FilePath → Option Nat) (admission : CensusOpenAdmissionReports input directory inventory retry)
    (path : FilePath) (name : String) : Prop :=
  (admission.view.child admission.root name).map admission.view.modelObject = names path

theorem CheckpointCrashChild.sameObject {input directory inventory names path name} {retry : LockedFileState FileImage}
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

section SampledReads

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : Image}
  {vacant : TryLockObserves retry.owners directory (.ok true)} {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {names : FilePath → Option Nat}

namespace CheckpointBarrierAlignedReports

def ReadsSample (opening : CheckpointBarrierAlignedReports input directory inventory retry layout published
    vacant selected names) (contents : Nat → ByteArray) (path : FilePath) (payload : ByteArray) : Prop :=
  ∃ read : opening.reads.reads.ObservesFile path payload,
    names path = some read.object ∧ contents read.object = payload

/-- The read report supplies the actual child, so equality with the
sampled value can be established at that inode. -/
theorem readsSample (opening : CheckpointBarrierAlignedReports input directory inventory retry layout published
      vacant selected names) {contents : Nat → ByteArray}
    {path : FilePath} {name : String} {child : DeviceInode} {payload : ByteArray}
    (same : CheckpointCrashChild names opening.admission path name)
    (bound : opening.admission.view.child opening.admission.root name = some child)
    (actual : opening.reads.reads.objectBytes (opening.admission.view.modelObject child) = some payload)
    (calls : RunChunkPathReport opening.reads.reads path name opening.admission.root opening.admission.view)
    (sampled : (names path).map contents = some payload) :
    opening.ReadsSample contents path payload := by
  let read := calls.observesFile bound actual
  have observed : names path = some read.object := same.sameObject calls bound actual
  rw [observed, Option.map_some] at sampled
  exact ⟨read, observed, Option.some.inj sampled⟩

/-- The aligned reader's exact held objects carry the manifest and marker
it selected, every run named by the strict manifest, and the WAL suffix. -/
theorem readsSelectedSamples (opening : CheckpointBarrierAlignedReports input directory inventory retry layout published
      vacant selected names) (contents : Nat → ByteArray)
    (manifest : (names (directory.file .manifest)).map contents = retry.image.directory.active.manifest)
    (marker : (names (directory.file .walBoundary)).map contents = retry.image.directory.active.walBoundary)
    (markerSelected : retry.image.directory.active.walBoundary =
      some (WAL.Boundary.encode (WAL.encode history).size.toUInt64))
    (runs : ∀ bytes metadata, retry.image.directory.active.manifest = some bytes →
      Manifest.IntegrityCheckpoint.decode bytes = .ok metadata →
      ∀ index < metadata.header.runCount.toNat, ∀ payload,
        published.durable metadata.header.generation index = some payload →
        (names (directory.file (.run metadata.header.generation index))).map contents = some payload)
    (aligned : layout.tail = ByteArray.empty)
    (segments : ∀ segment ∈ layout.sealed ++ [layout.keeper],
      (names (directory.file (.walSegment segment.first))).map contents = some segment.bytes) :
    (retry.image.directory.active.manifest = none → names (directory.file .manifest) = none ∧
      ∃ filename message, opening.reads.reads.stat (directory.file .manifest) =
        .error (.noFileOrDirectory filename 2 message)) ∧
    (∀ bytes, retry.image.directory.active.manifest = some bytes →
      opening.ReadsSample contents (directory.file .manifest) bytes) ∧
    opening.ReadsSample contents (directory.file .walBoundary)
      (WAL.Boundary.encode (WAL.encode history).size.toUInt64) ∧
    (∀ bytes metadata, retry.image.directory.active.manifest = some bytes →
      Manifest.IntegrityCheckpoint.decode bytes = .ok metadata →
      ∀ index < metadata.header.runCount.toNat, ∀ payload,
        published.durable metadata.header.generation index = some payload →
        opening.ReadsSample contents (directory.file (.run metadata.header.generation index)) payload) ∧
    ∀ segment ∈ layout.sealed ++ [layout.keeper],
      opening.ReadsSample contents (directory.file (.walSegment segment.first)) segment.bytes := by
  obtain ⟨markerFile, _⟩ := opening.reads.metadata.markerFile _ markerSelected
  refine ⟨?_, ?_, opening.readsSample opening.markerChild markerFile.bound markerFile.contents markerFile.calls
    (marker.trans markerSelected), ?_, ?_⟩
  · intro absent
    exact ⟨Option.map_eq_none_iff.mp (manifest.trans absent), (opening.reads.metadata.manifestMissing absent).2⟩
  · intro bytes present
    obtain ⟨⟨file⟩, _⟩ := opening.reads.metadata.manifestFile bytes present
    exact opening.readsSample opening.manifestChild file.bound file.contents file.calls (manifest.trans present)
  · intro bytes metadata present decoded index within payload stored
    obtain ⟨_, bound, actual, ⟨calls⟩⟩ := opening.reads.runs bytes metadata present decoded index within payload stored
    exact opening.readsSample (opening.runChild bytes metadata present decoded index within) bound actual calls
      (runs bytes metadata present decoded index within payload stored)
  · intro segment occurs
    have sampled := segments segment occurs
    rcases List.mem_append.mp occurs with sealed | last
    · let file := opening.reads.wal.sealedFile segment sealed
      exact opening.readsSample (opening.sealChild segment sealed) file.bound file.contents file.calls sampled
    · obtain rfl := List.mem_singleton.mp last
      let file := opening.reads.wal.keeper
      have actual : opening.reads.reads.objectBytes (opening.admission.view.modelObject file.object) =
          some layout.keeper.bytes := by simpa only [aligned, ByteArray.append_empty] using file.contents
      exact opening.readsSample opening.keeperChild file.bound actual file.calls sampled

end CheckpointBarrierAlignedReports
end SampledReads

/-- Follow the selected survivor through the reported failed opens. The
healthy aligned attempt uses the reached files and still explains every
earlier submission and snapshot response with the same WAL. -/
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
    {input : FilePath} (inventory : DescriptorInventory) (retry : LockedFileState FileImage)
    (retryFiles : CheckpointSurvivingFiles)
    (attempts : CheckpointBarrierRetryPrefix directory before.wal.active.first
      (checkpointSurvivorPath directory before binding) (cut.barrierCrashState binding)
      ⟨names, reached.interrupted.crashBytes⟩ retry retryFiles)
    (vacant : TryLockObserves retry.owners directory (.ok true)) :
    let cache := (atRun cut.checkpoint.table.runs.length).1.consume (directory.file .stagedManifest)
    let atBarrier : CheckpointManifestState := (cache, reached.renamed)
    let physical := runs (cache, reached.interrupted)
    (∀ bytes metadata, binding = some bytes → Manifest.IntegrityCheckpoint.decode bytes = .ok metadata →
      ∀ index < metadata.header.runCount.toNat, ∀ payload,
      physical.guaranteed metadata.header.generation index = some payload →
      ∃ inode, names (directory.file (.run metadata.header.generation index)) = some inode ∧
        reached.interrupted.crashBytes inode = [payload]) →
    (∀ (layout : CanonicalKeeperLayout retry.image before.history) (published : Image),
      layout.keeper = before.wal.active → layout.tail = ByteArray.empty →
      layout.sealed ++ [layout.keeper] = before.wal.readDescriptors layout.range.watermark →
      published.durable = physical.guaranteed →
      ∀ {checkpoint}, ∀ selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint,
        Nonempty (CheckpointBarrierAlignedReports input directory inventory retry layout published
          vacant selected retryFiles.names)) →
    CheckpointIssue ((calls.callbacks directory).perform directory) (.ready before.installed)
      ⟨atRun 0, before.owners⟩ cut.checkpoint.prepared cut.checkpoint.manifest
      cut.completed (.manifest .syncDirectory) atBarrier ∧
    wal.objects.Retains directory before (checkpointWalPathView reached.bindings wal.crashNames reached.interrupted) ∧
    (cut.tookEffect = true → binding = some cut.checkpoint.manifest) ∧
    BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
      (cut.barrierCrashState binding) retry ∧
    retry.image = (cut.barrierCrashState binding).image ∧
    CheckpointSurvivingFiles.Frames (checkpointSurvivorPath directory before binding)
      ⟨names, reached.interrupted.crashBytes⟩ retryFiles ∧
    ∃ (layout : CanonicalKeeperLayout retry.image before.history) (published : Image)
      (checkpoint : Option (PackedTable × UInt64))
      (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint)
      (openReports : CheckpointBarrierAlignedReports input directory inventory retry layout published
        vacant selected retryFiles.names)
      (session : SegmentedSession) (final : LockedFileState FileImage) (ready : Installed),
      published.durable = physical.guaranteed ∧
      openReports.finish.run = .ok session (openReports.finish.census, final) ∧
      session.phase = .ready ready ∧ final.owners.Owns directory session.descriptor ∧
      final.image.directory.active = ⟨binding, before.wal.directory.active.walBoundary⟩ ∧
      openReports.reads.wal.keeper.observesFile.object = wal.objects.keeper ∧
      openReports.reads.catalog.inventory.reports.readOptional (directory.file .manifest) = .ok binding ∧
      ((binding = none → names (directory.file .manifest) = none ∧ retryFiles.names (directory.file .manifest) = none) ∧
        ∀ bytes, binding = some bytes →
          ∃ file : openReports.reads.reads.ObservesFile (directory.file .manifest) bytes,
            names (directory.file .manifest) = some file.object ∧ bytes ∈ reached.interrupted.crashBytes file.object ∧
            bytes ∈ retryFiles.bytes file.object) ∧
      (∀ bytes metadata, binding = some bytes → Manifest.IntegrityCheckpoint.decode bytes = .ok metadata →
        ∀ index < metadata.header.runCount.toNat, ∀ payload,
        physical.guaranteed metadata.header.generation index = some payload →
        ∃ file : openReports.reads.reads.ObservesFile (directory.file (.run metadata.header.generation index)) payload,
          names (directory.file (.run metadata.header.generation index)) = some file.object ∧
          reached.interrupted.crashBytes file.object = [payload] ∧ retryFiles.bytes file.object = [payload]) ∧
      (((checkpoint.getD (.empty, 0)).2 = before.installed.generation ∧
          binding = before.wal.directory.active.manifest) ∨
        ((checkpoint.getD (.empty, 0)).2 = SegmentedCheckpointReport.generation before ∧
          binding = some cut.checkpoint.manifest)) ∧
      recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode before.history) = .ok ready.table ∧
      InstalledClientReplay log reads before.history ready session := by
  intro cache atBarrier physical runSurvivors observe
  obtain ⟨reported, retryImage, frame⟩ := attempts.reached rfl
  have retryPair : retry.image.directory.active = ⟨binding, before.wal.directory.active.walBoundary⟩ :=
    congrArg (·.directory.active) retryImage
  have retryManifest : retry.image.directory.active.manifest = binding :=
    congrArg DirectoryPublication.Bindings.manifest retryPair
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
  have select {current : LockedFileState FileImage}
      (prior : BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
        (cut.barrierCrashState binding) current) :=
    publication.checkpointRetryLayout walLayout valid (.crash pairSurvives) inputs
      (scratch := none) (prior.lineage CheckpointRetryTarget.unique)
  have bounded := reported.refines fun earlier => by
    obtain ⟨layout, _, keeper, _, _, _, prepared, _, _⟩ := select earlier
    have first := congrArg WalSegment.first keeper
    exact ⟨layout.target, layout.plan, ⟨first, layout.through, first ▸ layout.chain.keeperBytes⟩, first, prepared⟩
  obtain ⟨layout, _, keeper, tail, descriptors, offsets, prepared, _, accepted⟩ := select bounded
  have origin : binding = before.wal.directory.active.manifest ∨ binding = some cut.checkpoint.manifest :=
    generation.imp And.right And.right
  let published : Image := { publication with durable := physical.guaranteed }
  have agrees := cut.selectedRunAgreement ready publication binding origin physical.guaranteed
    reachedPublication.newRuns reachedPublication.priorRuns
  have accepted := SelectedRunsAgree.acceptsVersioned (actual := published) (retryManifest.symm ▸ agrees)
    layout.decoded accepted
  have selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint :=
    retryManifest.symm ▸ selected
  obtain ⟨openReports⟩ := observe layout published keeper tail descriptors rfl selected
  have following := openReports.reads.walReads.selectedAfterWatermark offsets descriptors
  obtain ⟨session, final, returned, finalPair, installed⟩ :=
    openReports.finish.installsAfterVacancy openReports.markerFound prepared.newer
      following accepted ready.resumed.ordered
  obtain ⟨sameSession, sameFinal, table, actualCheckpoint, sameReturn, phase, actualSelected, recovered, refined⟩ :=
    CachedRetryInstalled.refinesPendingClient installed replay
  obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj sameReturn
  have sameCheckpoint := actualSelected.uniqueResult selected
  refine ⟨issue, keptWal, settledNew, bounded, retryImage, frame, layout, published, checkpoint, selected, openReports,
    session, final, table, rfl, returned, phase, ?_, finalPair.trans retryPair, ?_,
    (openReports.reads.metadata.manifestRead layout.decoded).trans (congrArg Except.ok retryManifest),
    ?_, ?_, generation, sameCheckpoint ▸ recovered, refined⟩
  · obtain ⟨_, _, _, _, _, observed, _, _, _, _, _, _, _, held, _⟩ := installed
    obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj observed
    exact held
  · let file := openReports.reads.wal.keeper
    have opened := openReports.keeperChild.sameObject file.calls file.bound file.contents
    have keeperPath : checkpointSurvivorPath directory before binding (directory.file (.walSegment layout.keeper.first)) := by
      rw [congrArg WalSegment.first keeper]
      exact .inr (.inl (.inr (.inl rfl)))
    have original := (frame _ keeperPath).1.symm.trans opened
    have samePath := congrArg (fun (segment : WalSegment) => names (directory.file (.walSegment segment.first))) keeper
    exact Option.some.inj (original.symm.trans (samePath.trans (keptWal.2.1.2 _ ⟨names, survives, rfl⟩)))
  · obtain ⟨sameName, sameBytes⟩ := frame _ (.inl rfl)
    constructor
    · intro visible
      have absent := (openReports.reads.metadata.manifestMissing (retryManifest.trans visible)).1
      have absentName : retryFiles.names (directory.file .manifest) = none :=
        openReports.manifestChild.symm.trans (by simp [absent])
      exact ⟨sameName.symm.trans absentName, absentName⟩
    · intro bytes visible
      obtain ⟨⟨file⟩, _⟩ := openReports.reads.metadata.manifestFile bytes (retryManifest.trans visible)
      have bound : names (directory.file .manifest) = some file.observesFile.object :=
        sameName.symm.trans (openReports.manifestChild.sameObject file.calls file.bound file.contents)
      refine ⟨file.observesFile, bound, ?_⟩
      rw [visible, bound, manifestCrashBytes] at manifestBytes
      obtain ⟨fromInode, present, same⟩ := List.mem_map.mp manifestBytes
      have original : bytes ∈ reached.interrupted.crashBytes file.observesFile.object := Option.some.inj same ▸ present
      exact ⟨original, (sameBytes _ bound).symm ▸ original⟩
  · intro bytes metadata visible decoded index within payload stored
    obtain ⟨inode, bound, durable⟩ := runSurvivors bytes metadata visible decoded index within payload stored
    have active := retryManifest.trans visible
    obtain ⟨object, childBound, contents, ⟨file⟩⟩ := openReports.reads.runs bytes metadata active decoded index within payload stored
    have opened := (openReports.runChild bytes metadata active decoded index within).sameObject file childBound contents
    obtain ⟨sameName, sameBytes⟩ := frame _ (.inr (.inr ⟨bytes, metadata, index, visible, decoded, within, rfl⟩))
    have observed := sameName.symm.trans opened
    let read := file.observesFile childBound contents
    have sameObject : read.object = inode := Option.some.inj (observed.symm.trans bound)
    have original := sameObject.symm ▸ durable
    exact ⟨read, observed, original, (sameBytes _ observed).trans original⟩

end Alvoki.Storage.DiskSession
