import Alvoki.Storage.Disk.CheckpointManifestRenameCut
import Alvoki.Storage.Disk.SegmentedCheckpointObservedReopen
import Alvoki.Storage.Disk.HeldWalInstallation

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair SyncHandleRouting
open WAL.Boundary (WalInodeImage)

private theorem SelectedRunsAgree.symm {binding : Option ByteArray} {left right : RunFiles}
    (same : SelectedRunsAgree binding left right) : SelectedRunsAgree binding right left :=
  fun bytes metadata selected decoded index inside => (same bytes metadata selected decoded index inside).symm

/-- Reindex the proof of the selected chunk contents. The callbacks and
their installation result are definitionally unchanged. -/
private def MarkedRetryChunkReports.withRunMap {files : Type} {directory : DiskDirectory}
    {retry : LockedFileState FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout retry.image history} {published : Image}
    (report : MarkedRetryChunkReports files directory layout published) (runs : RunFiles)
    (same : SelectedRunsAgree retry.image.directory.active.manifest published.durable runs) :
    MarkedRetryChunkReports files directory layout { published with durable := runs } :=
  { report with
    chunks := by
      intro bytes metadata selected decoded index inside payload stored
      change runs metadata.header.generation index = some payload at stored
      rw [← same bytes metadata selected decoded index inside] at stored
      exact report.chunks bytes metadata selected decoded index inside payload stored }

/-- A selected checkpoint depends only on the indices named by its manifest. -/
theorem SelectedIntegrityCheckpoint.withRunMap {binding : Option ByteArray}
    {left right : RunFiles} {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint left binding checkpoint)
    (same : SelectedRunsAgree binding left right) : SelectedIntegrityCheckpoint right binding checkpoint := by
  cases selected with
  | absent => exact .absent
  | @present bytes metadata files table decoded stored loaded =>
    have reads (indices : List Nat) (valid : ∀ index ∈ indices, index < metadata.header.runCount.toNat) :
        indices.mapM (left metadata.header.generation) = indices.mapM (right metadata.header.generation) := by
      induction indices with
      | nil => rfl
      | cons index rest ih =>
        simp only [List.mapM_cons, same bytes metadata rfl decoded index (valid index List.mem_cons_self),
          ih (fun other included => valid other (List.mem_cons_of_mem index included))]
    exact .present decoded
      ((reads (List.range metadata.header.runCount.toNat) (fun _ included => List.mem_range.mp included)).symm.trans stored)
      loaded

private theorem CheckpointPowerCut.newManifestHeader {directory : DiskDirectory} {before : SegmentedWriterState}
    {writer : Nat} (cut : CheckpointPowerCut directory before) (ready : before.RetainedReady directory writer)
    {metadata : Manifest.IntegrityCheckpoint}
    (decoded : Manifest.IntegrityCheckpoint.decode cut.checkpoint.manifest = .ok metadata) :
    metadata.header = checkpointHeader cut.checkpoint.table (SegmentedCheckpointReport.generation before) := by
  obtain ⟨_, refinement, _⟩ := ready.resumed.canonical
  let generation := SegmentedCheckpointReport.generation before
  let files := cut.checkpoint.table.runs.map (·.run.bytes)
  let exactManifest := Manifest.IntegrityCheckpoint.fromRuns (checkpointHeader cut.checkpoint.table generation) files
  have encoded := cut.encoded
  have exactBytes : cut.checkpoint.manifest = exactManifest.encode := by
    by_cases fits : files.all (fun bytes => decide (bytes.size < UInt64.size)) = true
    · exact Except.ok.inj (encoded.symm.trans (encodeCheckpointIntegrityManifest_exact generation
        (fun bytes member => of_decide_eq_true (List.all_eq_true.mp fits bytes member))))
    · simp [encodeCheckpointIntegrityManifest, files, fits, Bind.bind, Except.bind] at encoded
  have written := (WrittenCheckpoint.of_flushForCheckpoint cut.flushed refinement cut.runCountFits
    ready.resumed.bounds.runs ready.resumed.bounds.memory generation).1
  have roundTrip := Manifest.IntegrityCheckpoint.decode_encode exactManifest written.validFloor
    (by simpa [exactManifest, files, Manifest.IntegrityCheckpoint.fromRuns] using written.count)
  rw [exactBytes] at decoded
  exact congrArg Manifest.IntegrityCheckpoint.header (Except.ok.inj (decoded.symm.trans roundTrip))

private abbrev OpenHandle := DescriptorInventory × DescriptorSlot × Nat

/-- The native-shaped reports for the checked open of the physical run
map selected after the crash. The WAL and metadata callbacks, directory
inventory, and authorization all describe this same open. -/
structure CheckpointHeldOpen (input : FilePath) (directory : DiskDirectory)
    {retry : LockedFileState FileImage} {history : List WAL.Write}
    (layout : CanonicalKeeperLayout retry.image history) (physical : Image) where
  calls : MarkedRetryChunkCalls (Cache OpenHandle) directory retry
  wal : HeldWalInstallReads layout calls
  held : HeldDirectoryMarkedRetryReports wal.operations physical
  namespaceMatches : held.lifetime.namespaceView = wal.view
  rootMatches : held.lifetime.root = wal.root
  authorization : ListedDirectoryAuthorization held
  metadata : HeldMarkedMetadata held
  completed : authorization.outcome = .completed
  healthy : wal.operations.HealthyFinish
  admission : OpenAdmissionReports input directory calls.slot

def CheckpointHeldOpen.chunkReports {input directory history physical} {retry : LockedFileState FileImage}
    {layout : CanonicalKeeperLayout retry.image history}
    (observed : CheckpointHeldOpen input directory layout physical) :
    MarkedRetryChunkReports (Cache OpenHandle) directory layout physical :=
  observed.held.toChunkReports (observed.authorization.settles observed.completed)
    observed.metadata.callbackMetadata observed.healthy

/-- A held open must report the keeper and ordered seals chosen from this
checkpoint survivor and its retained WAL. -/
abbrev CheckpointHeldOpen.Reports (input : FilePath) (directory : DiskDirectory) (before : SegmentedWriterState)
    (retry : LockedFileState FileImage) (published physical : Image) : Prop :=
  ∀ layout : CanonicalKeeperLayout retry.image before.history,
    layout.keeper = before.wal.active → layout.tail = ByteArray.empty →
    layout.sealed ++ [layout.keeper] = (published.segmentedCheckpointView before.wal).readDescriptors layout.range.watermark →
    Nonempty (CheckpointHeldOpen input directory layout physical)

/-- The actual held open and the next writer at its exact returned state. -/
abbrev CheckpointPowerCut.HeldReopen {directory : DiskDirectory} {before : SegmentedWriterState}
    (cut : CheckpointPowerCut directory before) (input : FilePath) (writer : Nat)
    (retry : LockedFileState FileImage) (published : Image) (binding : Option ByteArray)
    (runs : RunFiles) : Prop :=
  let pair : DirectoryPublication.Bindings := ⟨binding, before.wal.directory.active.walBoundary⟩
  let physical := { published with durable := runs }
  ∃ (layout : CanonicalKeeperLayout retry.image before.history)
    (observed : CheckpointHeldOpen input directory layout physical)
    (session : SegmentedSession) (final : LockedFileState FileImage)
    (opened : Reopened) (checkpoint : Option (PackedTable × UInt64)) (model : Sequential.SnapshotTable UInt64),
    observed.wal.operations.runWithAdmission observed.admission = .ok session final ∧
    session.directory = directory ∧ session.descriptor = observed.calls.slot.description ∧
    session.phase = .ready opened.installed ∧ final.owners.Owns directory session.descriptor ∧
    final.image.directory.active = pair ∧
    SelectedIntegrityCheckpoint runs binding checkpoint ∧
    ((opened.generation = before.installed.generation ∧ binding = before.wal.directory.active.manifest) ∨
      (opened.generation = SegmentedCheckpointReport.generation before ∧ binding = some cut.checkpoint.manifest)) ∧
    recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode before.history) = .ok opened.table ∧
    opened.table.committed.toNat = before.history.length ∧ opened.table.Refines model ∧
    RepresentsWalHistory before.history model ∧
    ∃ (after : SegmentedWriterState), after.RetainedReady directory observed.calls.slot.description ∧
      after.checkpoint = checkpoint ∧ after.installed = opened.installed ∧
      after.files = final.image ∧ after.owners = final.owners ∧
      ∀ {initialDescriptor initial allowCollection log},
        SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before →
          SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log observed.calls.slot.description after

/-- Reopen the selected checkpoint using its reported physical run bytes.
Only the selected indices enter the read contract. Reindexing them
preserves the exact callbacks and admission. -/
theorem CheckpointPowerCut.reopensSelectedRunMap {directory : DiskDirectory}
    {before : SegmentedWriterState} {writer : Nat} {input : FilePath}
    (cut : CheckpointPowerCut directory before) (ready : before.RetainedReady directory writer)
    (published : Image)
    (projected : before.published.executeVersioned cut.checkpoint.plan cut.checkpoint.cut = some published)
    (binding : Option ByteArray) (survives : binding ∈ published.manifest.crashImages)
    (runs : RunFiles) (agrees : SelectedRunsAgree binding runs published.durable)
    (retry : LockedFileState FileImage) :
    let pair : DirectoryPublication.Bindings := ⟨binding, before.wal.directory.active.walBoundary⟩
    BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
      ⟨(CheckpointPowerCut.physical before published).crash pair (some before.wal.active.bytes) [],
        before.owners.set (directory.file .lock) none⟩ retry →
    CheckpointHeldOpen.Reports input directory before retry published { published with durable := runs } →
    cut.HeldReopen input writer retry published binding runs := by
  intro pair failures observes
  let physical := { published with durable := runs }
  have pairSurvives : pair ∈ (published.segmentedCheckpointView before.wal).directory.crashImages :=
    List.mem_map.mpr ⟨binding, survives, rfl⟩
  have retryPair := SegmentedCheckpointPowerLossReport.keepsSelectedPair rfl
    (failures.lineage (fun a b selected => CheckpointRetryTarget.unique a b selected))
  have retryAgrees : SelectedRunsAgree retry.image.directory.active.manifest runs published.durable := by
    rw [retryPair]
    exact agrees
  let observedBy {layout : CanonicalKeeperLayout retry.image before.history}
      (operations : MarkedRetryChunkOperations (Cache OpenHandle) directory layout)
      (admission : OpenAdmissionReports input directory operations.slot) : Prop :=
    ∃ packet : CheckpointHeldOpen input directory layout physical,
      packet.wal.operations = operations ∧ HEq packet.admission admission
  have modelReports (layout : CanonicalKeeperLayout retry.image before.history)
      (keeper : layout.keeper = before.wal.active) (tail : layout.tail = ByteArray.empty)
      (descriptors : layout.sealed ++ [layout.keeper] =
        (published.segmentedCheckpointView before.wal).readDescriptors layout.range.watermark) :
      ∃ (observed : MarkedRetryChunkReports (Cache OpenHandle) directory layout published)
        (admission : OpenAdmissionReports input directory observed.slot),
        observedBy observed.toMarkedRetryChunkOperations admission := by
    obtain ⟨packet⟩ := observes layout keeper tail descriptors
    exact ⟨packet.chunkReports.withRunMap published.durable retryAgrees, packet.admission, packet, rfl, HEq.rfl⟩
  obtain ⟨_, layout, observed, admission, _, opened, checkpoint, model, session, final,
    returned, directoryExact, slot, phase, held, _, finalPair, _, selected, _, generation, _, _, replayed, committed,
    _, refinement, represents, after, installed, afterCheckpoint, afterTable, packet, sameOperations, sameAdmission⟩ :=
    cut.reopensFromChunks ready published projected pair pairSurvives retry failures observedBy modelReports
  obtain ⟨_, afterFiles, afterOwners⟩ :=
    installed.atReopen ((observed.runWithAdmission_eq admission).symm.trans returned)
  let OpenCall := (operations : MarkedRetryChunkOperations (Cache OpenHandle) directory layout) ×
    OpenAdmissionReports input directory operations.slot
  have sameCall : (⟨packet.wal.operations, packet.admission⟩ : OpenCall) =
      ⟨observed.toMarkedRetryChunkOperations, admission⟩ := Sigma.ext sameOperations sameAdmission
  have sameReturn := congrArg (fun call : OpenCall => call.1.runWithAdmission call.2) sameCall
  have descriptor : packet.calls.slot.description = observed.slot.description :=
    congrArg (fun operations : MarkedRetryChunkOperations (Cache OpenHandle) directory layout =>
      operations.slot.description) sameOperations
  refine ⟨layout, packet, session, final, opened, checkpoint, model,
    sameReturn.trans returned, directoryExact, slot.trans descriptor.symm, phase, held, finalPair,
    SelectedIntegrityCheckpoint.withRunMap selected agrees.symm, generation, replayed, committed,
    refinement, represents, after, ?_, afterCheckpoint, afterTable, afterFiles, afterOwners, ?_⟩
  · rw [descriptor]
    exact installed.retained
  · intro _ _ _ _ prior
    rw [descriptor]
    exact .checkpointPowerLossObserved prior cut projected pairSurvives failures retryPair installed

/-- At an interrupted manifest rename the reported surviving inode determines
the selected manifest. Open reports use the same run bindings through the
retries. The held-directory packet supplies the exact callbacks and admission.
Reindexing the checkpoint run map preserves both. This same open installs the
checkpoint and unchanged marked WAL, and its returned writer continues any
mixed trace reaching the interrupted writer with the same submission log. -/
theorem CheckpointPowerCut.reopensAfterManifestRename {directory : DiskDirectory}
    {before : SegmentedWriterState} {writer : Nat} {input : FilePath}
    (cut : CheckpointPowerCut directory before) (ready : before.RetainedReady directory writer)
    (published : Image)
    (projected : before.published.executeVersioned cut.checkpoint.plan cut.checkpoint.cut = some published)
    (interrupted : WalInodeImage) (bindings : List (Option Nat)) (binding : Option ByteArray)
    (survives : binding ∈ bindings.flatMap (manifestCrashBytes interrupted))
    (admitted : ∀ bytes ∈ bindings.flatMap (manifestCrashBytes interrupted), bytes ∈ published.manifest.crashImages)
    (runs : WalInodeImage → RunUnlinkImage)
    (newRuns : ∀ index < cut.checkpoint.table.runs.length,
      (runs interrupted).guaranteed (SegmentedCheckpointReport.generation before) index =
      published.durable (SegmentedCheckpointReport.generation before) index)
    (oldRuns : ∀ bytes metadata, before.wal.directory.active.manifest = some bytes →
      Manifest.IntegrityCheckpoint.decode bytes = .ok metadata →
      ∀ index < metadata.header.runCount.toNat,
        (runs interrupted).guaranteed metadata.header.generation index =
          published.durable metadata.header.generation index)
    (retry : LockedFileState FileImage) :
    let pair : DirectoryPublication.Bindings := ⟨binding, before.wal.directory.active.walBoundary⟩
    let physical := { published with durable := (runs interrupted).guaranteed }
    BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
      ⟨(CheckpointPowerCut.physical before published).crash pair (some before.wal.active.bytes) [],
        before.owners.set (directory.file .lock) none⟩ retry →
    CheckpointHeldOpen.Reports input directory before retry published physical →
    cut.HeldReopen input writer retry published binding (runs interrupted).guaranteed := by
  intro pair physical failures observes
  have survived := admitted binding survives
  have pairSurvives : pair ∈ (published.segmentedCheckpointView before.wal).directory.crashImages :=
    List.mem_map.mpr ⟨binding, survived, rfl⟩
  obtain ⟨computed, executed, _, _, _, crash⟩ := cut.selectsAcknowledgedHistory ready
  have sameImage := Option.some.inj (executed.symm.trans projected)
  subst computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, choice, _, _, _, _⟩ := crash pairSurvives
  have agrees : SelectedRunsAgree binding (runs interrupted).guaranteed published.durable := by
    rcases choice with ⟨_, old⟩ | ⟨_, new⟩
    · change binding = before.wal.directory.active.manifest at old
      exact old.symm ▸ oldRuns
    · intro bytes metadata present decoded index inside
      have sameBytes : bytes = cut.checkpoint.manifest := Option.some.inj (present.symm.trans new)
      subst bytes
      rw [cut.newManifestHeader ready decoded] at inside ⊢
      have count : (checkpointHeader cut.checkpoint.table (SegmentedCheckpointReport.generation before)).runCount.toNat =
          cut.checkpoint.table.runs.length := UInt64.toNat_ofNat_of_lt' cut.runCountFits
      exact newRuns index (count ▸ inside)
  exact cut.reopensSelectedRunMap ready published projected binding survived
    (runs interrupted).guaranteed agrees retry failures observes

end Alvoki.Storage.DiskSession
