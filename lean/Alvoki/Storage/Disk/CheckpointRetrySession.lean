import Alvoki.Storage.Disk.CheckpointCutSession
import Alvoki.Storage.Disk.WalSegmentCheckpointRetryLayout
import Alvoki.Storage.Disk.AppendCutSession

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

/-- Recover from the observed checkpoint directory, whether it is the
live publication cut or the image that survived a machine power loss. -/
theorem BoundedReopenTrace.installsFromCheckpointCut {directory : DiskDirectory}
    {published : CheckpointPublication.Image} {before : WalSegmentImage} {history : List WAL.Write}
    (layout : (published.segmentedCheckpointView before).ReadLayout history)
    (valid : (published.segmentedCheckpointView before).Valid history) (ordered : WAL.OrdinalsFrom 1 history)
    {observedDirectory : DirectoryPublication.Image}
    (observed : (published.segmentedCheckpointView before).CheckpointReopenDirectory observedDirectory)
    (inputs : ∀ pair, (published.segmentedCheckpointView before).Selects pair →
      published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history) pair.manifest ∧
      ∃ range, pair.walRange = some range ∧ range.through = history.length)
    {owners : LockOwners} {scratch : Option (ByteArray × Bool)} {retry : LockedFileState FileImage}
    (attempts : BoundedReopenTrace directory (CheckpointRetryTarget history before.active.first)
      ⟨(published.segmentedCheckpointView before).checkpointReopenFiles observedDirectory scratch, owners⟩ retry)
    {descriptor nextRef : Nat} (liveRefs : List Nat) (freshRefs : ∀ ref ∈ liveRefs, ref < nextRef)
    (acquisition : TryLockObserves retry.owners directory (.ok true)) (unlock : UnlockReport)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit) :
    let wal := published.segmentedCheckpointView before
    retry.image.kept = (wal.checkpointReopenFiles observedDirectory scratch).kept ∧
      wal.Selects retry.image.directory.active ∧
      ∃ selected : CanonicalKeeperLayout retry.image history,
        selected.target.first = before.active.first ∧ selected.tail = ByteArray.empty ∧
        ∃ selectedGeneration : UInt64,
          ((retry.image.directory.active.manifest.mapM fun bytes =>
            (Manifest.IntegrityCheckpoint.decode bytes).map (·.header.generation)).map (·.getD 0) :
              Except String UInt64) = .ok selectedGeneration ∧
          ∀ raw : HealthyBoundedWalReports directory
              (retry.owners.set (directory.file .lock) (some descriptor)) descriptor
              wal retry.image.directory.active selected.range.watermark published.durable selected.tail,
            sync #[directory.path] retry.image = .ok () retry.image.syncDirectory →
            (∀ action prior next,
              ReachesAction selected.target retry.image.syncDirectory selected.plan.finishActions action prior →
              prior.effect selected.target action = some next →
              performPaths directory selected.plan removeFile throw write sync renameFile action prior =
                .ok () next) →
            AppendCutReady directory descriptor liveRefs history published retry.image selected.target
              selectedGeneration (runOpenWithInstallation directory descriptor nextRef (.ok true) unlock
                (raw.reopen removeFile write sync renameFile) retry) := by
  intro wal
  have lineage := attempts.lineage (fun a b pair => CheckpointRetryTarget.unique a b pair)
  obtain ⟨selected, chosen, keeper, noTail, descriptors, offsets, prepared, emptyLater, accepted⟩ :=
    published.checkpointRetryLayout layout valid observed inputs lineage
  have generationRead : ∃ selectedGeneration : UInt64,
      ((retry.image.directory.active.manifest.mapM fun bytes =>
        (Manifest.IntegrityCheckpoint.decode bytes).map (·.header.generation)).map (·.getD 0) : Except String UInt64) =
      .ok selectedGeneration := by
    cases visible : retry.image.directory.active.manifest with
    | none => exact ⟨0, rfl⟩
    | some bytes =>
      have watermark := (DirectoryPublication.Bindings.walRange_accounting selected.decoded).1
      rw [visible] at watermark
      obtain ⟨parsed, decoded, _⟩ := selectedCheckpointWatermark_present_iff.mp watermark
      exact ⟨parsed.header.generation, by rw [Option.mapM, decoded]; rfl⟩
  obtain ⟨selectedGeneration, exactSelectedGeneration⟩ := generationRead
  refine ⟨lineage.keepsSealed, chosen, selected, congrArg WalSegment.first keeper, noTail,
    selectedGeneration, exactSelectedGeneration, ?_⟩
  intro raw settles healthy
  exact runOpenWithInstallation_appendLayout layout ordered selected keeper descriptors offsets prepared emptyLater
    accepted exactSelectedGeneration raw liveRefs freshRefs acquisition unlock removeFile write sync renameFile
    settles healthy

/-- Start from the reported checkpoint file cut after releasing the writer
lock, then run any finite trace of bounded reopen errors, lock reference
drops, and power losses. The next healthy bounded open installs the table
from the selected manifest's ordered runs and the same acknowledged WAL,
using the selected generation (zero for an absent manifest). -/
theorem BoundedReopenTrace.installsAfterCheckpointError {directory : DiskDirectory} {owners : LockOwners}
    {writerDescriptor descriptor nextRef : Nat} (ownership : owners.Owns directory writerDescriptor)
    {before : WalSegmentImage} {history : List WAL.Write}
    (layout : before.ReadLayout history) (beforeValid : before.Valid history)
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
      let files := wal.checkpointReopenFiles wal.directory scratch
      ∀ {retry : LockedFileState FileImage},
        BoundedReopenTrace directory (CheckpointRetryTarget history before.active.first)
          ⟨files, released.owners⟩ retry →
        TryLockObserves retry.owners directory (.ok true) →
        retry.image.kept = files.kept ∧
        wal.ReadLayout history ∧ wal.Valid history ∧ wal.Selects retry.image.directory.active ∧
        (retry.image.directory.active.manifest = before.directory.active.manifest ∨
          retry.image.directory.active.manifest = some manifest) ∧
        retry.image.directory.active.walBoundary = before.directory.active.walBoundary ∧
        ∃ selected : CanonicalKeeperLayout retry.image history,
          selected.target.first = installed.activeFirst ∧ selected.target.first = wal.active.first ∧
          selected.tail = ByteArray.empty ∧
          ∃ selectedGeneration : UInt64,
            ((retry.image.directory.active.manifest.mapM fun bytes =>
              (Manifest.IntegrityCheckpoint.decode bytes).map (·.header.generation)).map (·.getD 0) :
                Except String UInt64) = .ok selectedGeneration ∧
            ∀ raw : HealthyBoundedWalReports directory
                (retry.owners.set (directory.file .lock) (some descriptor)) descriptor
                wal retry.image.directory.active selected.range.watermark published.durable selected.tail,
              sync #[directory.path] retry.image = .ok () retry.image.syncDirectory →
              (∀ action prior next,
                ReachesAction selected.target retry.image.syncDirectory selected.plan.finishActions action prior →
                prior.effect selected.target action = some next →
                performPaths directory selected.plan removeFile throw write sync renameFile action prior =
                  .ok () next) →
              AppendCutReady directory descriptor liveRefs history published retry.image selected.target
                selectedGeneration (runOpenWithInstallation directory descriptor nextRef (.ok true) unlock
                  (raw.reopen removeFile write sync renameFile) retry) := by
  intro generation plan perform poisoned released freshGeneration encoded reported failed
  obtain ⟨exactGeneration, exactManifest, poison, close, drops, _, published, projectedCut, layout, valid, inputs⟩ :=
    runCheckpointFailureHandoff ownership layout beforeValid settled marker walFits initial projected previous
      installed model installedGeneration refines represents rowBounds checkpoint flushed generationFits runCountFits
      runBytesFit checkpointWrite checkpointStage checkpointSync checkpointRename report
      freshGeneration encoded reported failed
  refine ⟨exactGeneration, exactManifest, poison, close, drops, published, projectedCut, ?_⟩
  intro wal files retry attempts acquisition
  obtain ⟨kept, chosen, selected, keeper, noTail, selectedGeneration, exactGeneration, bounded⟩ :=
    attempts.installsFromCheckpointCut (descriptor := descriptor) layout valid ordered .visible
      (fun pair selects => (inputs pair selects).2.2) liveRefs freshRefs acquisition unlock removeFile write sync
      renameFile
  obtain ⟨sameMarker, sameManifest, _⟩ := inputs retry.image.directory.active chosen
  exact ⟨kept, layout, valid, chosen, sameManifest, sameMarker, selected, keeper.trans installedKeeper.symm, keeper,
    noTail, selectedGeneration, exactGeneration, bounded⟩

end Alvoki.Storage.DiskSession
