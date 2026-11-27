import Alvoki.Storage.Disk.Proofs.Append.AppendLockHandoff
import Alvoki.Storage.Disk.Proofs.Append.WalSegmentAppendLayout
import Alvoki.Storage.Disk.WalSegmentBoundedRetry
import Alvoki.Storage.Disk.VersionedReadyWriter

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WalSegmentCommit WAL.Boundary
open WAL (frameSize)

def AppendCutReady (directory : DiskDirectory) (descriptor : Nat) (liveRefs : List Nat)
    (history : List WAL.Write) (published : CheckpointPublication.Image) (initial : FileImage) (target : Target)
    (generation : UInt64) (result : EStateM.Result IO.Error (LockedFileState FileImage) SegmentedSession) : Prop :=
  target.range.through = history.length ∧ target.trimmed = WAL.encode (history.drop target.first) ∧
  published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history) target.pair.manifest ∧
  WAL.OrdinalsFrom 1 history ∧
  ∃ checkpoint table model, ∃ session final,
    result = .ok session final ∧
    SelectedIntegrityCheckpoint published.durable target.pair.manifest checkpoint ∧
    generation = (checkpoint.getD (.empty, 0)).2 ∧
    recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode history) = .ok table ∧
    session.directory = directory ∧ session.descriptor = descriptor ∧
    session.phase = .ready ⟨table, generation, (WAL.encode history).size, target.first⟩ ∧
    final.image.Ready target ∧ final.image.kept = initial.kept ∧ final.owners.Owns directory descriptor ∧
    table.committed.toNat = history.length ∧ table.RowBounds ∧ table.Refines model ∧
    RepresentsWalHistory history model ∧ table.pins.active = [] ∧
    session.phaseRef ≠ session.sessionRef ∧ session.phaseRef ∉ liveRefs ∧ session.sessionRef ∉ liveRefs

private theorem selectedCheckpoint_generation {durable binding checkpoint generation}
    (selected : SelectedIntegrityCheckpoint durable binding checkpoint)
    (generationRead : ((binding.mapM fun bytes =>
      (Manifest.IntegrityCheckpoint.decode bytes).map (·.header.generation)).map (·.getD 0) : Except String UInt64) =
      .ok generation) : (checkpoint.getD (.empty, 0)).2 = generation := by
  cases selected with
  | absent => exact Except.ok.inj generationRead
  | present decoded _ _ =>
    rw [Option.mapM, decoded] at generationRead
    exact Except.ok.inj generationRead

theorem runOpenWithInstallation_appendLayout {directory : DiskDirectory} {owners : LockOwners}
    {descriptor nextRef : Nat} {wal : WalSegmentImage} {history : List WAL.Write} {files : FileImage}
    (layout : wal.ReadLayout history) (ordered : WAL.OrdinalsFrom 1 history)
    (selected : CanonicalKeeperLayout files history) (sameKeeper : selected.keeper = wal.active)
    (descriptors : selected.sealed ++ [selected.keeper] = wal.readDescriptors selected.range.watermark)
    (offsets : selectWalSegmentReads (wal.segments.map WalSegment.first) selected.range.watermark =
      some (selected.first, (wal.readDescriptors selected.range.watermark).map WalSegment.first))
    (prepared : Prepared files selected.target selected.plan)
    (emptyLater : files.later.visible = [])
    {published : CheckpointPublication.Image}
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      files.directory.active.manifest)
    {generation : UInt64} (generationRead : ((files.directory.active.manifest.mapM fun bytes =>
      (Manifest.IntegrityCheckpoint.decode bytes).map (·.header.generation)).map (·.getD 0) : Except String UInt64) =
      .ok generation)
    (raw : HealthyBoundedWalReports directory (owners.set (directory.file .lock) (some descriptor)) descriptor
      wal files.directory.active selected.range.watermark published.durable selected.tail)
    (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < nextRef)
    (acquisition : TryLockObserves owners directory (.ok true)) (unlock : UnlockReport)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit)
    (settles : sync #[directory.path] files = .ok () files.syncDirectory)
    (healthy : ∀ action prior next,
      ReachesAction selected.target files.syncDirectory selected.plan.finishActions action prior →
      prior.effect selected.target action = some next →
      performPaths directory selected.plan removeFile throw write sync renameFile action prior = .ok () next) :
    AppendCutReady directory descriptor liveRefs history published files selected.target generation
      (runOpenWithInstallation directory descriptor nextRef (.ok true) unlock
        (raw.reopen removeFile write sync renameFile) ⟨files, owners⟩) := by
  obtain ⟨checkpoint, table, model, exactCheckpoint, replayed, bounded, count, committed, bounds,
    refines, represents, noPins⟩ :=
    selected.prepareBoundedReports layout sameKeeper descriptors offsets emptyLater accepted ordered raw
  let opened : Reopened :=
    ⟨table, (checkpoint.getD (.empty, 0)).2, (WAL.encode history).size.toUInt64, selected.keeper.first⟩
  obtain ⟨after, finished, settled, trace⟩ := finishMarkedOpen_completes prepared directory removeFile write sync
    renameFile settles healthy
  have finish : finishBoundedMarkedOpen directory selected.boundedPlan selected.plan.keeperBytes.size removeFile
      write sync renameFile files = .ok () after := by
    rw [selected.boundedPlan_eq_extract, finishBoundedMarkedOpen_eq_full directory selected.plan prepared.valid, finished]
  have installed : raw.reopen removeFile write sync renameFile files = .ok opened after := by
    dsimp only [HealthyBoundedWalReports.reopen, HealthyBoundedWalReports.reopenWithState, reopenMarkedBoundedWith]
    rw [prepareBoundedMarkedWith_liftReports, bounded]
    simp only [liftExcept, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, finish, opened]
  obtain ⟨session, final, result, path, lock, ready, image, _, held, separate, phaseFresh, sessionFresh⟩ :=
    runOpenWithInstallation_ready liveRefs fresh (before := ⟨files, owners⟩) acquisition (unlock := unlock) installed
  have sameGeneration := selectedCheckpoint_generation exactCheckpoint generationRead
  exact ⟨selected.through, selected.chain.keeperBytes, accepted, ordered, checkpoint, table, model, session, final,
    result, exactCheckpoint, sameGeneration.symm, replayed, path, lock,
    by simpa only [opened, count, CanonicalKeeperLayout.target, sameGeneration] using ready,
    image ▸ settled, image ▸ trace.keepsSealed, held, committed, bounds, refines, represents, noPins, separate,
    phaseFresh, sessionFresh⟩

/-- The installed writer and its complete, settled WAL agree just before
the append. The no-follow active-file guard has already succeeded. -/
structure AppendCutWriter (installed : Installed) (wal : WalSegmentImage) (history : List WAL.Write)
    (published : CheckpointPublication.Image) (watermark : Nat) : Prop where
  layout : wal.ReadLayout history
  chain : WalSegment.Chain history 0 wal.segments
  ordered : WAL.OrdinalsFrom 1 history
  settled : wal.directory.crashImages = [wal.directory.active]
  marker : wal.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64)
  range : wal.directory.active.walRange = some ⟨watermark, history.length⟩
  checkpoint : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
    wal.directory.active.manifest
  generation : ((wal.directory.active.manifest.mapM fun bytes =>
    (Manifest.IntegrityCheckpoint.decode bytes).map (·.header.generation)).map (·.getD 0) : Except String UInt64) =
    .ok installed.generation
  count : installed.walBytes = (WAL.encode history).size
  first : installed.activeFirst = wal.active.first
  canonical : ∃ model, installed.table.Refines model ∧ RepresentsWalHistory history model

/-- An actual append-first commit error returns `commitUnknown` with the
same cause and poisons the writer. After release, the bounded worker
installs exactly the observed old or new history. Its repair reports can
describe either an aligned sync or replacement of a longer physical keeper.
Checkpoint runs and sealed segments stay fixed. The file projection tracks
the live marker scratch and takes the repair scratch as an observation.
It omits unrelated manifest scratch and does not track scratch survival
on power loss. -/
theorem runOpenAfterAppendFailure {directory : DiskDirectory} {owners : LockOwners}
    {writerDescriptor descriptor nextRef : Nat} (ownership : owners.Owns directory writerDescriptor)
    {installed : Installed} {before : WalSegmentImage} {history : List WAL.Write}
    {published : CheckpointPublication.Image} {watermark : Nat}
    (ready : AppendCutWriter installed before history published watermark)
    {key : UInt64} {value : Option UInt64} {event : WAL.Write} {table : PackedTable}
    (prepared : prepareWrite installed.table key value = some (event, table))
    (fits : installed.walBytes + frameSize < UInt64.size)
    (effects : WriteEffects)
    (append stage : FilePath → ByteArray → EStateM IO.Error WriteFiles Unit)
    (commitSync : Array FilePath → EStateM IO.Error WriteFiles Unit)
    (commitRename : FilePath → FilePath → EStateM IO.Error WriteFiles Unit)
    (reports : AppendCommitReports directory installed.activeFirst history event (installed.walBytes + frameSize)
      effects (before.directory.staged .walBoundary) append stage commitSync commitRename)
    {cause : IO.Error} {failed : WriteFiles}
    (commitFailed : commitAt directory installed.activeFirst event (installed.walBytes + frameSize)
      append stage commitSync commitRename (WriteFiles.initial history (before.directory.staged .walBoundary)) =
      .error cause failed)
    (scratch : Option (ByteArray × Bool)) (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < nextRef)
    (unlock : UnlockReport)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit) :
    let markerScratch := before.directory.staged .walBoundary
    let commit := commitAt directory installed.activeFirst event (installed.walBytes + frameSize)
      append stage commitSync commitRename
    let next := { installed with table, walBytes := installed.walBytes + frameSize }
    let poisoned : Phase Installed × LockedFileState WriteFiles := (.poisoned, ⟨failed, owners⟩)
    let released : LockedFileState WriteFiles := ⟨failed, owners.set (directory.file .lock) none⟩
    let cut := failed.reopenSegment before.active.first history before.directory.active.manifest
    event = ⟨table.committed, key, value⟩ ∧ table.committed.toNat = history.length + 1 ∧
    runPreparedWrite next event.sequence commit (.ready installed, ⟨WriteFiles.initial history markerScratch, owners⟩) =
      .error (.commitUnknown cause) poisoned ∧
    runCloseWithFiles directory writerDescriptor .success poisoned = .ok () (.closed, released) ∧
    (∀ (references : HeldLockReferences writerDescriptor) (drops : List LockReferenceDrop),
      references.remaining drops = [] → references.afterFileDrops drops directory poisoned.2 = released) ∧
    ∀ observed, AppendReopenObservation cut observed →
      let files := before.appendReopenFiles observed scratch
      ∃ selectedHistory, (selectedHistory = history ∨ selectedHistory = history ++ [event]) ∧
        WAL.OrdinalsFrom 1 selectedHistory ∧ (WAL.encode selectedHistory).size < UInt64.size ∧
        files.directory.active.manifest = before.directory.active.manifest ∧
        files.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode selectedHistory).size.toUInt64) ∧
        published.AcceptsVersioned selectedHistory.length.toUInt64 (CheckpointRepresentsPrefix selectedHistory)
          files.directory.active.manifest ∧
        let wal := before.appendSelectedView observed.directory.active selectedHistory
        wal.ReadLayout selectedHistory ∧ WalSegment.Chain selectedHistory 0 wal.segments ∧
        ∃ selected : CanonicalKeeperLayout files selectedHistory,
          selected.target.first = installed.activeFirst ∧
          selected.target.trimmed = WAL.encode (selectedHistory.drop selected.target.first) ∧
          ∀ raw : HealthyBoundedWalReports directory (released.owners.set (directory.file .lock) (some descriptor))
              descriptor wal files.directory.active selected.range.watermark published.durable selected.tail,
            sync #[directory.path] files = .ok () files.syncDirectory →
            (∀ action prior next,
              ReachesAction selected.target files.syncDirectory selected.plan.finishActions action prior →
              prior.effect selected.target action = some next →
              performPaths directory selected.plan removeFile throw write sync renameFile action prior = .ok () next) →
            AppendCutReady directory descriptor liveRefs selectedHistory published files selected.target
              installed.generation (runOpenWithInstallation directory descriptor nextRef (.ok true) unlock
                (raw.reopen removeFile write sync renameFile) ⟨files, released.owners⟩) := by
  intro markerScratch commit next poisoned released cut
  obtain ⟨model, refined, represented⟩ := ready.canonical
  have committed : history.length = installed.table.committed.toNat :=
    represented.committed_count.symm.trans (congrArg UInt64.toNat refined.committed).symm
  obtain ⟨fields, ordinal, extended, _, size⟩ := prepareWrite_extends_history ready.ordered committed prepared
  have byteCount : installed.walBytes + frameSize = (WAL.encode (history ++ [event])).size := by
    rw [ready.count, size]
  have modeled := reports.run byteCount
  change forgetError commit (WriteFiles.initial history markerScratch) = _ at modeled
  change commit (WriteFiles.initial history markerScratch) = .error cause failed at commitFailed
  rw [forgetError, commitFailed] at modeled
  obtain ⟨poisonedWriter, closed, dropped, available⟩ := runPreparedWrite_failure_handoff
    (before := ⟨WriteFiles.initial history markerScratch, owners⟩) installed next event.sequence commitFailed ownership
  refine ⟨fields, ordinal, poisonedWriter, closed, dropped, ?_⟩
  intro observed seen files
  have modeledCut : writeFilesAfter (runWriteEffects history event effects markerScratch) = failed := by
    rw [← modeled]
    rfl
  have cutSeen : AppendReopenObservation
      ((writeFilesAfter (runWriteEffects history event effects markerScratch)).reopenSegment
        before.active.first history before.directory.active.manifest) observed := by
    rw [modeledCut]
    exact seen
  obtain ⟨strict, covered, _⟩ := DirectoryPublication.Bindings.walRange_accounting ready.range
  have allFit := byteCount ▸ fits
  obtain ⟨selectedHistory, allowed, manifest, marker, layout, chain, selected, range, keeper, descriptors,
    offsets, _, keeperChoices, keptPrefix, later⟩ := ready.layout.afterAppendCut ready.chain covered event allFit
      effects before.directory.active.manifest markerScratch strict observed scratch cutSeen
  have accepted : published.AcceptsVersioned selectedHistory.length.toUInt64 (CheckpointRepresentsPrefix selectedHistory)
      files.directory.active.manifest := by
    rw [manifest]
    rcases allowed with rfl | rfl
    · exact ready.checkpoint
    · exact published.acceptsVersioned_extend_history ready.checkpoint allFit
  have selectedFits : (WAL.encode selectedHistory).size < UInt64.size := by
    rcases allowed with rfl | rfl
    · rw [ready.count] at fits
      exact Nat.lt_of_le_of_lt (Nat.le_add_right ..) fits
    · exact allFit
  have consecutive : WAL.OrdinalsFrom 1 selectedHistory := by
    rcases allowed with rfl | rfl
    · exact ready.ordered
    · exact extended
  refine ⟨selectedHistory, allowed, consecutive, selectedFits, manifest, marker, accepted, layout, chain, selected,
    ?_, selected.chain.keeperBytes, ?_⟩
  · change selected.keeper.first = installed.activeFirst
    rw [keeper, ready.first]
    rfl
  intro raw settles healthy
  have reads := congrArg MarkedWalRange.watermark range
  exact runOpenWithInstallation_appendLayout layout consecutive selected keeper (reads.symm ▸ descriptors)
    (reads.symm ▸ offsets) (selected.prepared keeperChoices keptPrefix later) rfl accepted
    (manifest.symm ▸ ready.generation) raw liveRefs fresh available unlock removeFile write sync renameFile
    settles healthy

end Alvoki.Storage.DiskSession
