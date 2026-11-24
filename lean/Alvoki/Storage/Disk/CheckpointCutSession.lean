import Alvoki.Storage.Disk.WalSegmentCheckpointReopen
import Alvoki.Storage.Disk.WalSegmentCheckpointOpenReports
import Alvoki.Storage.Disk.CheckpointObservedDispatch
import Alvoki.Storage.Disk.CheckpointLockHandoff

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open WAL (frameSize)
open WAL.Boundary (CheckpointRepresentsPrefix)

def recoverCheckpointCut
    {directory owners descriptor wal pair watermark durable}
    (raw : HealthyCheckpointCutReports directory owners descriptor wal pair watermark durable)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit) : EStateM IO.Error FileImage Reopened :=
  reopenMarkedBoundedWith directory (fun path => liftExcept (raw.reports.readOptional path))
    (fun path => liftExcept (raw.list path)) (fun path => pure (raw.reports.lstat path))
    (fun path => liftExcept (raw.reports.readBin path)) (fun path size => liftExcept (raw.readPrefix path size))
    removeFile write sync renameFile

/-- The selected checkpoint and acknowledged history of a returned ready
session, with its exact settled files and the acquired lock. -/
def CheckpointCutReady (directory : DiskDirectory) (descriptor : Nat) (liveRefs : List Nat)
    (history : List WAL.Write) (durable : CheckpointPublication.RunFiles) (walBytes keeper : Nat) (files : FileImage)
    (result : EStateM.Result IO.Error (LockedFileState FileImage) SegmentedSession) : Prop :=
  ∃ checkpoint table model, ∃ count : UInt64, ∃ session final,
    result = .ok session final ∧
    SelectedIntegrityCheckpoint durable files.directory.active.manifest checkpoint ∧
    session.directory = directory ∧ session.descriptor = descriptor ∧
    session.phase = .ready ⟨table, (checkpoint.getD (.empty, 0)).2, count.toNat, keeper⟩ ∧
    count.toNat = walBytes ∧ table.committed.toNat = history.length ∧
    table.RowBounds ∧ table.Refines model ∧ RepresentsWalHistory history model ∧ table.pins.active = [] ∧
    final.image = files.syncDirectory.syncKeeper ∧ final.owners.Owns directory descriptor ∧
    session.phaseRef ≠ session.sessionRef ∧ session.phaseRef ∉ liveRefs ∧ session.sessionRef ∉ liveRefs

/-- An accepted checkpoint cut uses the actual bounded worker. Its held
listing, run reads and keeper prefix are supplied by one directory owner.
The keeper was already settled by the writer, so recovery reaches only the
directory and keeper syncs. No full keeper payload read is needed. -/
theorem runOpenWithInstallation_checkpointCut {directory : DiskDirectory} {owners : LockOwners}
    {descriptor nextRef : Nat} {wal : WalSegmentImage} {history : List WAL.Write}
    (layout : wal.ReadLayout history) (valid : wal.Valid history) (ordered : WAL.OrdinalsFrom 1 history)
    {seen : DirectoryPublication.Image} (observation : wal.CheckpointReopenDirectory seen)
    {range : MarkedWalRange} (decoded : seen.active.walRange = some range) (atEnd : range.through = history.length)
    {published : CheckpointPublication.Image}
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      seen.active.manifest)
    (raw : HealthyCheckpointCutReports directory (owners.set (directory.file .lock) (some descriptor)) descriptor
      wal seen.active range.watermark published.durable)
    (scratch : Option (ByteArray × Bool)) (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < nextRef)
    (acquisition : TryLockObserves owners directory (.ok true)) (unlock : UnlockReport)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit) :
    let files := wal.checkpointReopenFiles seen scratch
    sync #[directory.path] files = .ok () files.syncDirectory →
    sync #[directory.file (.walSegment wal.active.first)] files.syncDirectory =
      .ok () files.syncDirectory.syncKeeper →
    CheckpointCutReady directory descriptor liveRefs history published.durable (history.length * frameSize)
      wal.active.first files
      (runOpenWithInstallation directory descriptor nextRef (.ok true) unlock
        (recoverCheckpointCut raw removeFile write sync renameFile) ⟨files, owners⟩) := by
  intro files syncDirectory syncKeeper
  obtain ⟨selected, sameRange, sameKeeper, noTail, descriptors, offsets, _, choices, keeperPrefix, later⟩ :=
    layout.checkpointReopenLayout valid observation decoded atEnd scratch
  have prepared := selected.prepared choices keeperPrefix (sameRange.symm ▸ later)
  obtain ⟨watermark, covered, marker, count, markerVisible, markerDecoded, absolute⟩ :=
    DirectoryPublication.Bindings.walRange_accounting decoded
  have byteCount : (WAL.encode history).size = count.toNat := by
    rw [absolute, atEnd, WAL.encode_size, Nat.mul_comm]
  obtain ⟨checkpoint, table, model, exactCheckpoint, replayed, committed, bounds, refines, represents, noPins⟩ :=
    selectedCheckpoint_replays watermark accepted (byteCount ▸ count.toNat_lt_size) ordered
  have clock := Option.some.inj (exactCheckpoint.watermark.symm.trans watermark)
  have checkpointRead := raw.reports.readIntegrityCheckpoint_exact directory exactCheckpoint raw.manifest raw.runs
  have walRead := raw.readSelectedBounded layout atEnd covered absolute offsets
  have covers : selected.first ≤ (checkpoint.getD (.empty, 0)).1.committed.toNat := by
    rw [clock, ← sameRange]
    exact selected.covers
  have counted : count.toNat / frameSize = range.through := by
    rw [absolute, Nat.mul_div_cancel _ (by decide : 0 < frameSize)]
  let plan : Plan := ⟨range.through, wal.active.first, [], wal.active.bytes⟩
  have exactPlan : selected.plan = plan := by
    simp [CanonicalKeeperLayout.plan, plan, sameRange, sameKeeper, noTail, WalSegmentImage.checkpointReopenFiles,
      LaterNames.settled]
  have planValid : plan.valid = true := exactPlan ▸ prepared.valid
  have keeperSize : plan.keeperSize = wal.active.bytes.size := by
    rw [← exactPlan]
    change (selected.range.through - selected.keeper.first) * frameSize = _
    have size := selected.target.trimmedSize
    change selected.keeper.bytes.size = (selected.range.through - selected.keeper.first) * frameSize at size
    rw [← size]
    exact congrArg (fun segment => segment.bytes.size) sameKeeper
  have recovered := selected.chain.replaysMarked ByteArray.empty (atEnd ▸ absolute) covers ordered replayed
  rw [ByteArray.append_empty] at recovered
  have sameFiles : selected.sealed.map (fun segment => (segment.first, segment.bytes)) ++
      [(selected.keeper.first, selected.keeper.bytes)] =
        (wal.readDescriptors range.watermark).map (fun segment => (segment.first, segment.bytes)) := by
    rw [← descriptors, List.map_append]
    rfl
  rw [sameFiles] at recovered
  have keeperRead : ((wal.readDescriptors range.watermark).map (fun segment => (segment.first, segment.bytes))).getLast? =
      some (wal.active.first, wal.active.bytes) := by rw [← descriptors, List.map_append, sameKeeper]; simp
  have bounded := prepareBoundedMarkedWith_reported directory raw.reports.readOptional raw.list
    (fun path => .ok (raw.reports.lstat path)) raw.reports.readBin raw.readPrefix checkpointRead
    (raw.marker.trans (congrArg Except.ok markerVisible)) markerDecoded (by rw [clock]; exact walRead) recovered keeperRead
  let opened : Reopened := ⟨table, (checkpoint.getD (.empty, 0)).2, count, wal.active.first⟩
  have exactBounded : prepareBoundedMarkedWith directory raw.reports.readOptional raw.list
      (fun path => .ok (raw.reports.lstat path)) raw.reports.readBin raw.readPrefix =
        .ok (plan, opened, wal.active.bytes.size) := by
    simpa only [plan, opened, counted] using bounded
  have finish : finishBoundedMarkedOpen directory plan wal.active.bytes.size removeFile write sync renameFile files =
      .ok () files.syncDirectory.syncKeeper := by
    simp only [finishBoundedMarkedOpen, planValid, keeperSize, beq_self_eq_true, Nat.le_refl, decide_true,
      Bool.and_self, ite_true, plan, List.isEmpty_nil, Bind.bind, EStateM.bind, syncDirectory, syncKeeper]
  have installed : recoverCheckpointCut raw removeFile write sync renameFile files =
      .ok opened files.syncDirectory.syncKeeper := by
    dsimp only [recoverCheckpointCut, reopenMarkedBoundedWith]
    have liftedMetadata : (fun path => (pure (raw.reports.lstat path) :
        EStateM IO.Error FileImage (Except IO.Error IO.FS.Metadata))) =
        fun path => liftExcept (.ok (raw.reports.lstat path) : Except IO.Error (Except IO.Error IO.FS.Metadata)) := rfl
    rw [liftedMetadata, prepareBoundedMarkedWith_liftReports, exactBounded]
    simp only [liftExcept, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, finish]
  obtain ⟨session, final, result, path, lock, phase, image, _, held, distinct, phaseFresh, sessionFresh⟩ :=
    runOpenWithInstallation_ready liveRefs fresh (before := ⟨files, owners⟩) acquisition (unlock := unlock) installed
  exact ⟨checkpoint, table, model, count, session, final, result, exactCheckpoint, path, lock, phase, atEnd ▸ absolute,
    committed, bounds, refines, represents, noPins, image, held, distinct, phaseFresh, sessionFresh⟩

/-- From a ready writer with settled segment files and a complete WAL,
follow a reported checkpoint file error through release and the next
healthy bounded open. The visible cut retains all manifest choices until
directory sync. A crash uses only a manifest/marker pair admitted by that
cut. Primitive reports describe this same owned directory on both sides. -/
theorem runOpenAfterCheckpointFailure {directory : DiskDirectory} {owners : LockOwners}
    {writerDescriptor descriptor nextRef : Nat} (ownership : owners.Owns directory writerDescriptor)
    {before : WalSegmentImage} {history : List WAL.Write}
    (layout : before.ReadLayout history) (chain : WalSegment.Chain history 0 before.segments)
    (ordered : WAL.OrdinalsFrom 1 history)
    (settled : before.directory.crashImages = [before.directory.active])
    (marker : before.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64))
    (walFits : (WAL.encode history).size < UInt64.size)
    (initial : CheckpointPublication.Image) (projected : initial.manifest = before.directory.project .manifest)
    (previous : initial.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      before.directory.active.manifest)
    (installed : Installed) (model : Sequential.SnapshotTable UInt64)
    (installedGeneration : ((before.directory.active.manifest.mapM fun bytes =>
      (Manifest.IntegrityCheckpoint.decode bytes).map (·.header.generation)).map (·.getD 0) : Except String UInt64) =
      .ok installed.generation)
    (installedBytes : installed.walBytes = history.length * frameSize)
    (installedKeeper : installed.activeFirst = before.active.first)
    (refines : installed.table.Refines model) (represents : RepresentsWalHistory history model)
    (rowBounds : installed.table.RowBounds) (checkpoint : PackedTable)
    (flushed : (flushForCheckpoint installed.table id : Except String PackedTable) = .ok checkpoint)
    (generationFits : installed.generation.toNat + 1 < UInt64.size)
    (runCountFits : checkpoint.runs.length < UInt64.size)
    (runBytesFit : ∀ bytes ∈ checkpoint.runs.map (·.run.bytes), bytes.size < UInt64.size)
    (checkpointWrite checkpointStage : FilePath → ByteArray → EStateM IO.Error Nat Unit)
    (checkpointSync : Array FilePath → EStateM IO.Error Nat Unit)
    (checkpointRename : FilePath → FilePath → EStateM IO.Error Nat Unit)
    (report : CheckpointPublication.Step → CheckpointPublication.StepReport)
    {manifest : ByteArray} {cause : IO.Error} {cut : Nat}
    (scratch : Option (ByteArray × Bool)) (liveRefs : List Nat) (freshRefs : ∀ ref ∈ liveRefs, ref < nextRef)
    (unlock : UnlockReport)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit) :
    let generation := (installed.generation.toNat + 1).toUInt64
    let plan := CheckpointPublication.VersionedRunSet.integrity
      ⟨checkpointHeader checkpoint generation, checkpoint.runs.map (·.run.bytes)⟩
    let perform := performCheckpointFileStep directory generation checkpoint.runs.toArray
      (directory.file .stagedManifest) manifest
      (fun found => match found with
        | some run => pure run
        | none => throw (IO.userError "checkpoint run index is out of bounds"))
      checkpointWrite checkpointStage checkpointSync checkpointRename
    let poisoned : Phase Installed × LockedFileState Nat := (.poisoned, ⟨cut, owners⟩)
    let released : LockedFileState Nat := ⟨cut, owners.set (directory.file .lock) none⟩
    initial.UnreachableVersioned generation →
    encodeCheckpointIntegrityManifest checkpoint generation = .ok manifest →
    CheckpointPublication.ReachedFileReports report perform (CheckpointPublication.steps checkpoint.runs.length) 0 →
    CheckpointPublication.run checkpoint.runs.toArray.size perform 0 = .error cause cut →
    generation.toNat = installed.generation.toNat + 1 ∧ manifest = plan.manifest.encode ∧
    runPreparedCheckpoint { installed with table := checkpoint, generation := generation }
        perform (.ready installed, ⟨0, owners⟩) = .error cause poisoned ∧
    runCloseWithFiles directory writerDescriptor .success poisoned = .ok () (.closed, released) ∧
    (∀ (references : HeldLockReferences writerDescriptor) (drops : List LockReferenceDrop),
      references.remaining drops = [] → references.afterFileDrops drops directory poisoned.2 = released) ∧
    ∃ published, initial.executeVersioned plan cut = some published ∧
      let wal := published.segmentedCheckpointView before
      ∀ seen, wal.CheckpointReopenDirectory seen →
        let files := wal.checkpointReopenFiles seen scratch
        (seen.active.manifest = before.directory.active.manifest ∨ seen.active.manifest = some manifest) ∧
        seen.active.walBoundary = before.directory.active.walBoundary ∧
        ∃ range, seen.active.walRange = some range ∧ range.through = history.length ∧
          (∀ bytes, seen.active.manifest = some bytes → ∃ checkpointManifest orderedRuns,
            Manifest.IntegrityCheckpoint.decode bytes = .ok checkpointManifest ∧
            checkpointManifest.header.committed.toNat = range.watermark ∧
            (List.range checkpointManifest.header.runCount.toNat).mapM
              (published.durable checkpointManifest.header.generation) = some orderedRuns ∧
            checkpointManifest.validateRuns orderedRuns = true) ∧
          ∀ raw : HealthyCheckpointCutReports directory
              (released.owners.set (directory.file .lock) (some descriptor)) descriptor
              wal seen.active range.watermark published.durable,
            sync #[directory.path] files = .ok () files.syncDirectory →
            sync #[directory.file (.walSegment wal.active.first)] files.syncDirectory =
              .ok () files.syncDirectory.syncKeeper →
            CheckpointCutReady directory descriptor liveRefs history published.durable installed.walBytes
              installed.activeFirst files
              (runOpenWithInstallation directory descriptor nextRef (.ok true) unlock
                (recoverCheckpointCut raw removeFile write sync renameFile) ⟨files, released.owners⟩) := by
  intro generation plan perform poisoned released freshGeneration encoded reported failed
  obtain ⟨exactManifest, published, projectedCut, publication⟩ :=
    CheckpointPublication.observedIntegrityCheckpointFileFailure initial directory checkpoint generation encoded
      checkpointWrite checkpointStage checkpointSync checkpointRename report reported failed
  have runFailed : CheckpointPublication.run checkpoint.runs.length perform 0 = .error cause cut := by
    simpa only [List.size_toArray] using failed
  obtain ⟨poison, close, drops, canAcquire⟩ := runPreparedCheckpoint_failure_handoff
    (before := ⟨0, owners⟩) installed { installed with table := checkpoint, generation := generation }
    perform runFailed ownership
  refine ⟨UInt64.toNat_ofNat_of_lt' generationFits, exactManifest, poison, close, drops, published, projectedCut, ?_⟩
  have strict (bytes : ByteArray) (binding : before.directory.active.manifest = some bytes) :
      ∃ parsed, Manifest.IntegrityCheckpoint.decode bytes = .ok parsed := by
    have matched := installedGeneration
    rw [binding] at matched
    cases decodedBytes : Manifest.IntegrityCheckpoint.decode bytes with
    | error cause => simp [decodedBytes, Option.mapM, Functor.map, Except.map] at matched
    | ok parsed => exact ⟨parsed, rfl⟩
  obtain ⟨walLayout, walValid, inputs⟩ := CheckpointPublication.segmentedCheckpoint_reportedCut
    layout chain settled marker walFits projected previous strict refines represents rowBounds flushed runCountFits
    generation freshGeneration runBytesFit report publication
  intro wal seen observed files
  obtain ⟨sameMarker, chosen, _⟩ := inputs seen.active observed.selectsActive
  obtain ⟨range, decoded, through, accepted, exactRuns⟩ :=
    published.checkpointReopenInputs observed scratch (fun pair selects => by
      obtain ⟨_, _, accepted, _, range, _, decoded, through, _⟩ := inputs pair selects
      exact ⟨accepted, range, decoded, through⟩)
  refine ⟨by simpa only [exactManifest] using chosen, sameMarker, range, decoded, through, exactRuns, ?_⟩
  intro raw syncDirectory syncKeeper
  have keeper : installed.activeFirst = wal.active.first := installedKeeper
  rw [installedBytes, keeper]
  exact runOpenWithInstallation_checkpointCut walLayout walValid ordered observed decoded through accepted
    raw scratch liveRefs freshRefs canAcquire unlock removeFile write sync renameFile syncDirectory syncKeeper

end Alvoki.Storage.DiskSession
