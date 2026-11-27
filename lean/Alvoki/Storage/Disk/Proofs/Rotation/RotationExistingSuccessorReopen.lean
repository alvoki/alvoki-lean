import Alvoki.Storage.Disk.Proofs.Rotation.RotationExistingSuccessor
import Alvoki.Storage.Disk.CapturedAlignedInstallation
import Alvoki.Storage.Disk.PendingClientReplay

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

variable {directory : DiskDirectory} {before : SegmentedWriterState}
  {opened : RotationExistingSuccessorOpen directory before}
  {file : RotationExistingSuccessorFileSync opened}

/-- One reported power loss after the successful directory barrier.
The observed namespace and payloads come from its possible survivors.
The canonical lock and settled marker still bind their original inodes. -/
structure RotationExistingSuccessorPowerLoss (returned : RotationExistingSuccessorDirectorySync file) where
  view : DirectoryReadNamespace
  objects : view.modelObject = returned.settled.view.modelObject
  names : ∀ name, view.child opened.root name ∈ returned.settled.crashNames name
  bytes : Nat → ByteArray
  payload : ∀ name child, view.child opened.root name = some child →
    bytes (view.modelObject child) ∈ returned.settled.inodes.crashBytes (view.modelObject child)
  lock : view.child opened.root "LOCK" = some opened.lock.child
  marker : RunChildLookup opened.root "WAL.commit" returned.settled.view
  markerName : returned.settled.crashNames "WAL.commit" = [some marker.child]
  markerValue : ByteArray
  markerBytes : returned.settled.inodes.crashBytes (returned.settled.view.modelObject marker.child) = [markerValue]

namespace RotationExistingSuccessorPowerLoss

variable {returned : RotationExistingSuccessorDirectorySync file}

private abbrev successorFirst (before : SegmentedWriterState) := before.installed.walBytes / WAL.frameSize

/-- The settled successor is the new keeper; the old keeper joins the
sealed list. The projection forgets scratch and releases the local lock. -/
def files (_loss : RotationExistingSuccessorPowerLoss returned) : LockedFileState FileImage :=
  ⟨before.wal.rotated.checkpointReopenFiles (.settled before.wal.directory.active) none,
    before.owners.set (directory.file .lock) none⟩

theorem vacant (loss : RotationExistingSuccessorPowerLoss returned) :
    TryLockObserves loss.files.owners directory (.ok true) := by
  intro _
  simp [files, LockOwners.set]

theorem successor (loss : RotationExistingSuccessorPowerLoss returned) :
    loss.view.child opened.root (renderWalSegmentName (successorFirst before)) = some opened.statChild.child ∧
    loss.view.modelObject opened.statChild.child = opened.inventory.inode opened.slot.description ∧
    loss.bytes (loss.view.modelObject opened.statChild.child) = ByteArray.empty := by
  obtain ⟨_, durableName, durableObject, durableBytes, _⟩ := returned.durableSuccessor
  have survivor := loss.names (renderWalSegmentName (successorFirst before))
  rw [durableName] at survivor
  have bound := List.mem_singleton.mp survivor
  have payload := loss.payload _ _ bound
  have identified := congrFun loss.objects opened.statChild.child
  rw [← identified] at durableBytes
  rw [durableBytes] at payload
  exact ⟨bound, identified.trans durableObject, List.mem_singleton.mp payload⟩

theorem markerSurvives (loss : RotationExistingSuccessorPowerLoss returned) :
    loss.view.child opened.root "WAL.commit" = some loss.marker.child ∧
    loss.bytes (loss.view.modelObject loss.marker.child) = loss.markerValue := by
  have survived := loss.names "WAL.commit"
  rw [loss.markerName] at survived
  have bound := List.mem_singleton.mp survived
  have bytes := loss.payload _ _ bound
  have markerBytes := loss.markerBytes
  rw [← congrFun loss.objects loss.marker.child] at markerBytes
  rw [markerBytes] at bytes
  exact ⟨bound, List.mem_singleton.mp bytes⟩

private theorem prepares (loss : RotationExistingSuccessorPowerLoss returned)
    (ready : before.RetainedReady directory opened.owner.description) :
    ∃ layout : CanonicalKeeperLayout loss.files.image before.history,
      layout.range = before.target.range ∧ layout.keeper = before.wal.rotated.active ∧
      layout.keeper.first = successorFirst before ∧ layout.keeper.bytes = ByteArray.empty ∧
      layout.tail = ByteArray.empty ∧
      layout.sealed ++ [layout.keeper] = before.wal.rotated.readDescriptors before.target.range.watermark ∧
      selectWalSegmentReads (before.wal.rotated.segments.map WalSegment.first) before.target.range.watermark =
        some (layout.first, (before.wal.rotated.readDescriptors before.target.range.watermark).map WalSegment.first) ∧
      Prepared loss.files.image layout.target layout.plan := by
  have rotation := ready.rotationInput opened.nonempty
  have retained := (⟨before.wal.directory, .durable⟩ : WalSegmentRotation.State).visibleReadLayout rotation ready.layout
  change before.wal.rotated.ReadLayout before.history at retained
  have selected : before.wal.rotated.CheckpointReopenDirectory (.settled before.wal.directory.active) := by
    apply WalSegmentImage.CheckpointReopenDirectory.crash
    change before.wal.directory.active ∈ before.wal.directory.crashImages
    rw [ready.walDirectorySettled]
    exact List.mem_singleton_self _
  have decoded : before.wal.directory.active.walRange = some before.target.range := ready.walPair ▸ before.target.decoded
  obtain ⟨layout, exactRange, keeper, tail, descriptors, offsets, _, choices, prefixes, later⟩ :=
    retained.checkpointReopenLayout (rotation.valid_rotated ready.valid) selected decoded ready.resumed.through none
  have successor : before.wal.active.last = successorFirst before := by
    change before.wal.active.last = before.installed.walBytes / WAL.frameSize
    rw [ready.layout.activeEnd, ready.resumed.bytes, WAL.encode_size, Nat.mul_comm,
      Nat.mul_div_cancel _ (by decide : 0 < WAL.frameSize)]
  exact ⟨layout, exactRange, keeper, (congrArg WalSegment.first keeper).trans successor,
    congrArg WalSegment.bytes keeper, tail, descriptors, offsets,
    layout.prepared choices prefixes (exactRange.symm ▸ later)⟩

end RotationExistingSuccessorPowerLoss

variable {returned : RotationExistingSuccessorDirectorySync file}

/-- The new process observes the reported surviving bindings and bytes
under the same directory. It supplies the chronological reads and
successful aligned repair for the keeper selected by the crash. -/
structure RotationExistingSuccessorReopen
    (loss : RotationExistingSuccessorPowerLoss returned) (input : FilePath)
    (postCrash : DescriptorInventory) (layout : CanonicalKeeperLayout loss.files.image before.history)
    (selected : SelectedIntegrityCheckpoint before.published.durable loss.files.image.directory.active.manifest before.checkpoint) where
  admission : CensusOpenAdmissionReports input directory postCrash loss.files
  callbacks : CapturedAlignedCallbacks admission
  reads : CapturedMarkedReadReports admission layout before.published
  finish : CapturedAlignedFinish callbacks reads loss.vacant selected
  census : CapturedMarkedReadCensus reads finish.readCustody
  marker : IO.FS.Metadata
  markerFound : admission.lookup (directory.file .walBoundary) (admission.reached, admission.held) =
    .ok (.ok marker) (admission.reached, admission.held)
  root : admission.root = opened.root
  objects : admission.view.modelObject = loss.view.modelObject
  names : ∀ name, admission.view.child admission.root name = loss.view.child opened.root name
  bytes : ∀ object payload, reads.reads.objectBytes object = some payload → loss.bytes object = payload

theorem RotationExistingSuccessorReopen.readSurvivor
    {loss : RotationExistingSuccessorPowerLoss returned} {input postCrash layout selected}
    (next : RotationExistingSuccessorReopen loss input postCrash layout selected)
    {name child payload} (bound : next.admission.view.child next.admission.root name = some child)
    (read : next.reads.reads.objectBytes (next.admission.view.modelObject child) = some payload) :
    payload ∈ returned.settled.inodes.crashBytes (next.admission.view.modelObject child) := by
  have survives := loss.payload name child ((next.names name).symm.trans bound)
  rw [← congrFun next.objects child] at survives
  exact next.bytes _ _ read ▸ survives

/-- A successful rotation that reused an empty successor can be followed
through a reported power loss and a healthy chronological marked open.
The next table comes from the old checkpoint and acknowledged history,
using the exact successor and marker inodes left by the rotation. -/
theorem RotationExistingSuccessorPowerLoss.reopensAligned
    (loss : RotationExistingSuccessorPowerLoss returned)
    (ready : before.RetainedReady directory opened.owner.description)
    (replay : PendingClientReplay log recorded before.history)
    (create : FilePath → EStateM IO.Error (Cache RotationSuccessorHandle × (DescriptorInventory × RotationCreateFiles)) Unit)
    {input : FilePath} (postCrash : DescriptorInventory)
    (observe : ∀ (layout : CanonicalKeeperLayout loss.files.image before.history),
      layout.keeper.first = before.installed.walBytes / WAL.frameSize → layout.keeper.bytes = ByteArray.empty →
      layout.tail = ByteArray.empty →
      ∀ selected : SelectedIntegrityCheckpoint before.published.durable loss.files.image.directory.active.manifest before.checkpoint,
        Nonempty (RotationExistingSuccessorReopen loss input postCrash layout selected)) :
    runObservedRotation directory opened.lookup opened.readEmpty create file.group
      (.ready before.installed, ⟨(opened.cache, opened.inventory, opened.files), before.owners⟩) =
      .ok () (.ready { before.installed with activeFirst := before.installed.walBytes / WAL.frameSize },
        ⟨({ opened.cache with active := none }, returned.after), before.owners⟩) ∧
    ∃ (layout : CanonicalKeeperLayout loss.files.image before.history)
      (selected : SelectedIntegrityCheckpoint before.published.durable loss.files.image.directory.active.manifest before.checkpoint)
      (next : RotationExistingSuccessorReopen loss input postCrash layout selected)
      (session : SegmentedSession) (final : LockedFileState FileImage) (installed : Installed),
      next.finish.runFromCensus next.census.metadataRelease next.census.runs.released next.census.sealRelease =
        .ok session (next.finish.census, final) ∧
      session.directory = directory ∧ session.phase = .ready installed ∧ final.owners.Owns directory session.descriptor ∧
      next.admission.owner ∈ next.finish.census.slots ∧ next.admission.cached ∈ next.finish.census.slots ∧
      next.admission.reached.inode next.admission.cached.description =
        returned.handle.1.inode returned.handle.2.1.description ∧
      next.admission.reached.inode next.admission.owner.description = opened.inventory.inode opened.owner.description ∧
      final.image.directory.active = before.wal.directory.active ∧ final.image.Ready layout.target ∧
      layout.keeper.bytes = ByteArray.empty ∧ installed.activeFirst = before.installed.walBytes / WAL.frameSize ∧
      installed.walBytes = before.installed.walBytes ∧ installed.generation = before.installed.generation ∧
      next.reads.wal.keeper.observesFile.object = opened.inventory.inode opened.slot.description ∧
      loss.bytes next.reads.wal.keeper.observesFile.object = ByteArray.empty ∧
      next.census.marker.file.observesFile.object = loss.view.modelObject loss.marker.child ∧
      next.census.marker.bytes = loss.markerValue ∧
      next.reads.reads.ObservesSelected directory loss.files.image.directory.active.manifest before.published.durable ∧
      (∀ segment, ∀ member : segment ∈ layout.sealed,
        segment.bytes ∈ returned.settled.inodes.crashBytes (next.reads.wal.sealedFile segment member).observesFile.object) ∧
      (∀ bytes manifest, loss.files.image.directory.active.manifest = some bytes →
        Manifest.IntegrityCheckpoint.decode bytes = .ok manifest → ∀ index < manifest.header.runCount.toNat,
        ∀ payload, before.published.durable manifest.header.generation index = some payload →
        ∃ file : next.reads.reads.ObservesFile (directory.file (.run manifest.header.generation index)) payload,
          payload ∈ returned.settled.inodes.crashBytes file.object) ∧
      CachedRetryInstalled (before := loss.files) next.reads.walReads next.admission.reached
        next.admission.owner next.reads.bindings before.published next.callbacks.liveRefs (.ok session final) ∧
      recoverSelected (before.checkpoint.getD (.empty, 0)).1 (WAL.encode before.history) = .ok installed.table ∧
      InstalledClientReplay log recorded before.history installed session := by
  obtain ⟨layout, range, _, first, emptyKeeper, tail, descriptors, offsets, prepared⟩ := loss.prepares ready
  have selected : SelectedIntegrityCheckpoint before.published.durable loss.files.image.directory.active.manifest before.checkpoint := by
    change SelectedIntegrityCheckpoint before.published.durable before.wal.directory.active.manifest before.checkpoint
    rw [ready.walPair]
    exact ready.resumed.selected
  have accepted : before.published.AcceptsVersioned before.history.length.toUInt64 (CheckpointRepresentsPrefix before.history)
      loss.files.image.directory.active.manifest := by
    change before.published.AcceptsVersioned before.history.length.toUInt64 (CheckpointRepresentsPrefix before.history)
      before.wal.directory.active.manifest
    rw [ready.walPair]
    exact ready.resumed.accepted
  obtain ⟨next⟩ := observe layout first emptyKeeper tail selected
  have following := next.reads.walReads.selectedAfterWatermark (range.symm ▸ offsets) (range.symm ▸ descriptors)
  let census := next.census
  obtain ⟨session, final, result, samePair, liveOwner, liveDirectory, actual⟩ :=
    next.finish.installsFromCensus census.manifest census.runs census.marker census.beforeListing
      census.seals census.offsets census.retained next.markerFound prepared.newer
      following accepted ready.resumed.ordered
  obtain ⟨_, _, installed, checkpoint, indexed, phase, exactCheckpoint, recovered, answers⟩ :=
    CachedRetryInstalled.refinesPendingClient actual replay
  obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj indexed
  have endpoint : session.directory = directory ∧ final.owners.Owns directory session.descriptor ∧
      final.image.Ready layout.target ∧ installed.activeFirst = before.installed.walBytes / WAL.frameSize ∧
      installed.walBytes = before.installed.walBytes ∧ installed.generation = before.installed.generation := by
    obtain ⟨data, chosen, _, _, _, same, path, _, readyPhase, _, _, _, _, held, _, _, _, filesReady, _,
      chosenCheckpoint, _, generation, bytes, position, _⟩ := actual
    obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj same
    obtain rfl := Phase.ready.inj (readyPhase.symm.trans phase)
    have sameCheckpoint := chosenCheckpoint.uniqueResult selected
    have sized : data.installed.walBytes = before.installed.walBytes := by
      change data.walBytes.toNat = _
      rw [bytes, ready.resumed.bytes, WAL.encode_size, Nat.mul_comm]
    refine ⟨path, held, filesReady, position.trans first, sized, ?_⟩
    rw [show data.installed.generation = data.generation from rfl, generation, sameCheckpoint, ready.resumed.generation]
  obtain ⟨path, held, filesReady, installedFirst, sized, generation⟩ := endpoint
  have successor := loss.successor
  have sameKeeper : next.reads.wal.keeper.observesFile.object = loss.view.modelObject opened.statChild.child := by
    let keeper := next.reads.wal.keeper
    have expected : next.admission.view.child next.admission.root (renderWalSegmentName layout.keeper.first) =
        some opened.statChild.child := (next.names _).trans (first.symm ▸ successor.1)
    have child := Option.some.inj (keeper.bound.symm.trans expected)
    change keeper.calls.statObject = _
    rw [← keeper.calls.identifiedStat, keeper.calls.statLookup.child_eq keeper.bound, child, next.objects]
  have sameMarker : census.marker.file.observesFile.object = loss.view.modelObject loss.marker.child := by
    let marker := census.marker.file
    have bound := (next.names "WAL.commit").trans loss.markerSurvives.1
    have child := marker.calls.statLookup.child_eq bound
    change marker.calls.statObject = _
    rw [← marker.calls.identifiedStat, child, next.objects]
  refine ⟨returned.returnsRotation create, layout, selected, next, session, final, installed, result,
    path, phase, held, liveOwner, liveDirectory, ?_, ?_, samePair, filesReady, emptyKeeper, installedFirst,
    sized, generation, sameKeeper.trans successor.2.1, sameKeeper.symm ▸ successor.2.2,
    sameMarker, (next.bytes _ _ census.marker.file.observesFile.contents).symm.trans
      (sameMarker.symm ▸ loss.markerSurvives.2),
    next.reads.chunkReads, ?_, ?_, actual, exactCheckpoint.uniqueResult selected ▸ recovered, answers⟩
  · obtain ⟨_, _, _, _, identified, _⟩ := next.admission.opened.captures
    calc
      next.admission.reached.inode next.admission.cached.description =
          next.admission.view.modelObject next.admission.root := identified.symm
      _ = returned.settled.view.modelObject opened.root := by rw [next.root, next.objects, loss.objects]
      _ = opened.files.view.modelObject opened.root :=
        congrArg (fun view => view.modelObject opened.root) returned.view
      _ = _ := returned.capturedObject
  · have bound := (next.names "LOCK").trans loss.lock
    have same := Option.some.inj (next.reads.lockEntry.symm.trans bound)
    calc
      next.admission.reached.inode next.admission.owner.description =
          next.admission.view.modelObject opened.lock.child := next.reads.identifiesLock.symm.trans (congrArg _ same)
      _ = returned.settled.view.modelObject opened.lock.child := by rw [next.objects, loss.objects]
      _ = opened.files.view.modelObject opened.lock.child := congrArg (fun view => view.modelObject opened.lock.child) returned.view
      _ = _ := opened.lockObject
  · intro segment member
    let sealFile := next.reads.wal.sealedFile segment member
    have surviving := next.readSurvivor sealFile.bound sealFile.contents
    change segment.bytes ∈ returned.settled.inodes.crashBytes sealFile.calls.statObject
    rw [← sealFile.calls.identifiedStat, sealFile.calls.statLookup.child_eq sealFile.bound]
    exact surviving
  · intro bytes manifest present decoded index within payload stored
    obtain ⟨_, bound, contents, ⟨calls⟩⟩ := next.reads.runs bytes manifest present decoded index within payload stored
    refine ⟨calls.observesFile bound contents, ?_⟩
    change payload ∈ returned.settled.inodes.crashBytes calls.statObject
    rw [← calls.identifiedStat, calls.statLookup.child_eq bound]
    exact next.readSurvivor bound contents

end Alvoki.Storage.DiskSession
