import Alvoki.Storage.Disk.CheckpointCutSession
import Alvoki.Storage.Disk.SegmentedRetryTrace
import Alvoki.Storage.Disk.SegmentedWriterState

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- Record the observed reads and callbacks as the exact bounded attempt. -/
def _root_.Alvoki.Storage.WalSegmentRepair.HealthyBoundedWalReports.openAttempt
    {directory owners descriptor wal pair watermark durable tail}
    (raw : HealthyBoundedWalReports directory owners descriptor wal pair watermark durable tail)
    (nextRef : Nat) (unlock : UnlockReport)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit) : BoundedReopenAttempt where
  descriptor := descriptor
  nextRef := nextRef
  acquired := .ok true
  unlock := unlock
  readOptional := raw.reports.readOptional
  list := raw.list
  lstat := fun path => .ok (raw.reports.lstat path)
  readBin := raw.reports.readBin
  readPrefix := raw.readPrefix
  removeFile := removeFile
  write := write
  sync := sync
  renameFile := renameFile

private theorem SegmentedWriterState.Ready.cleanFiles {directory : DiskDirectory} {descriptor : Nat}
    {state : SegmentedWriterState}
    (ready : state.Ready directory descriptor) :
    state.wal.checkpointReopenFiles state.wal.directory state.files.keeper.staged = state.files := by
  have visible := ready.activeContents
  have durable := ready.resumed.ready.keeperDurable.trans (congrArg (fun bytes => [bytes])
    (ready.resumed.ready.keeper.symm.trans visible))
  have empty := ready.resumed.ready.pruned.1
  have absent := ready.resumed.ready.pruned.2
  have kept := ready.sealedFiles
  have directory := ready.directoryFiles
  cases files : state.files with
  | mk observed sealed keeper later =>
    cases keeper with
    | mk payload crashImages scratch =>
      cases later with
      | mk names alternatives =>
        simp only [files] at visible durable empty absent kept directory
        simp [WalSegmentImage.checkpointReopenFiles, Publication.Image.settled,
          LaterNames.settled, visible, durable, empty, absent, kept, directory]

private theorem SegmentedWriterState.Ready.cleanSyncs {directory : DiskDirectory} {descriptor : Nat}
    {state : SegmentedWriterState}
    (ready : state.Ready directory descriptor) :
    state.files.syncDirectory = state.files ∧ state.files.syncKeeper = state.files := by
  have projected := ready.cleanFiles
  rw [← projected]
  constructor
  · cases directory : state.wal.directory with
    | mk active crashes staged =>
      have exact := ready.walDirectorySettled
      rw [directory] at exact
      change crashes = [active] at exact
      subst crashes
      rfl
  · rfl

/-- Explicit successful close releases the old description without changing
files. A subsequent healthy bounded open acquires the same directory under
the new description, reloads its exact checkpoint and WAL, and allocates
fresh references for the new session. -/
theorem SegmentedWriterState.Ready.cleanReopen {directory : DiskDirectory} {descriptor nextDescriptor nextRef : Nat}
    {state : SegmentedWriterState} (ready : state.Ready directory descriptor)
    (freshDescriptor : nextDescriptor ≠ descriptor)
    (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < nextRef) (unlock : UnlockReport)
    (raw : HealthyCheckpointCutReports directory
      ((state.owners.set (directory.file .lock) none).set (directory.file .lock) (some nextDescriptor))
      nextDescriptor state.wal state.wal.directory.active state.target.range.watermark state.published.durable)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit)
    (syncDirectory : sync #[directory.path] state.files = .ok () state.files)
    (syncKeeper : sync #[directory.file (.walSegment state.wal.active.first)] state.files = .ok () state.files) :
    let released : LockedFileState FileImage := ⟨state.files, state.owners.set (directory.file .lock) none⟩
    let attempt := raw.openAttempt nextRef unlock removeFile write sync renameFile
    runCloseWithFiles directory descriptor .success (.ready state.installed, ⟨state.files, state.owners⟩) =
      .ok () (.closed, released) ∧
    ∃ session final table,
      let next := { state with installed := { state.installed with table }, owners := final.owners }
      attempt.run directory released = .ok session final ∧
      final.image = state.files ∧ final.owners = released.owners.set (directory.file .lock) (some nextDescriptor) ∧
      session.directory = directory ∧ session.descriptor = nextDescriptor ∧
      session.descriptor ≠ descriptor ∧ session.phase = .ready next.installed ∧
      session.phaseRef = nextRef ∧ session.sessionRef = nextRef + 1 ∧
      session.phaseRef ≠ session.sessionRef ∧ session.phaseRef ∉ liveRefs ∧ session.sessionRef ∉ liveRefs ∧
      table.pins.active = [] ∧ next.Ready directory nextDescriptor := by
  intro released attempt
  have closed : runCloseWithFiles directory descriptor .success (.ready state.installed, ⟨state.files, state.owners⟩) =
      .ok () (.closed, released) := by
    dsimp only [runCloseWithFiles]
    rw [runClose_open (by simp) .success, LockOwners.release_owned ready.held]
  have acquire : TryLockObserves released.owners directory (.ok true) := by
    simp [TryLockObserves, released, LockOwners.set]
  have samePair : state.wal.directory.active = state.target.pair := by
    rw [← ready.directoryFiles]
    exact ready.resumed.ready.selected
  have source := ready.cleanFiles
  obtain ⟨directoryFixed, keeperFixed⟩ := ready.cleanSyncs
  have recovered := runOpenWithInstallation_checkpointCut (owners := released.owners)
    ready.layout ready.walValid ready.resumed.ordered .visible ready.appendInput.range rfl
    ready.appendInput.checkpoint raw state.files.keeper.staged liveRefs fresh acquire unlock removeFile write sync renameFile
    (by simpa only [source, directoryFixed] using syncDirectory)
    (by simpa only [source, directoryFixed, keeperFixed] using syncKeeper)
  obtain ⟨checkpoint, table, model, count, session, final, returned, selected, path, lock, phase, countExact,
    _, bounds, refines, history, pins, fileEffects, held, separate, freshPhase, freshSession⟩ := recovered
  have priorCheckpoint : SelectedIntegrityCheckpoint state.published.durable state.wal.directory.active.manifest
      state.checkpoint := samePair.symm ▸ ready.resumed.selected
  have sameCheckpoint : checkpoint = state.checkpoint :=
    Except.ok.inj ((raw.readCheckpoint selected).symm.trans (raw.readCheckpoint priorCheckpoint))
  have filesAfter : final.image = state.files := by
    simpa only [source, directoryFixed, keeperFixed] using fileEffects
  have reopened : runOpenWithInstallation directory nextDescriptor nextRef (.ok true) unlock
      (raw.reopen removeFile write sync renameFile) released = .ok session final := by
    simpa only [recoverCheckpointCut, source, released] using returned
  have identities : final.owners = released.owners.set (directory.file .lock) (some nextDescriptor) ∧
      session.phaseRef = nextRef ∧ session.sessionRef = nextRef + 1 := by
    have actual := reopened
    rw [runOpenWithInstallation_outcome, runOpenWithImage_acquired] at actual
    cases ran : raw.reopen removeFile write sync renameFile released.image with
    | ok opened image =>
      rw [ran] at actual
      obtain ⟨sessionExact, finalExact⟩ := EStateM.Result.ok.inj actual
      exact ⟨congrArg LockedFileState.owners finalExact.symm,
        congrArg SegmentedSession.phaseRef sessionExact.symm, congrArg SegmentedSession.sessionRef sessionExact.symm⟩
    | error cause image =>
      rw [ran] at actual
      cases unlock <;> contradiction
  let next : SegmentedWriterState := { state with installed := { state.installed with table }, owners := final.owners }
  have exactBytes : count.toNat = state.installed.walBytes := by
    rw [countExact, ready.resumed.bytes, WAL.encode_size, Nat.mul_comm]
  have installed : session.phase = .ready next.installed := by
    simpa only [next, sameCheckpoint, ← ready.resumed.generation, exactBytes, ready.appendInput.first] using phase
  have nextReady : next.Ready directory nextDescriptor :=
    ⟨⟨ready.resumed.ready, ready.resumed.through, ready.resumed.keeper, ready.resumed.bytes, ready.resumed.contents,
      ready.resumed.generation, ready.resumed.selected, ready.resumed.accepted, ready.resumed.ordered,
      bounds, ⟨model, refines, history⟩⟩, ready.layout, ready.chain, ready.directoryFiles, ready.sealedFiles, ready.active,
      ready.manifestFiles, held⟩
  exact ⟨closed, session, final, table, reopened, filesAfter, identities.1, path, lock, lock ▸ freshDescriptor,
    installed, identities.2.1, identities.2.2, separate, freshPhase, freshSession, pins, nextReady⟩

end Alvoki.Storage.DiskSession
