import Alvoki.Storage.Disk.CheckpointCutSession
import Alvoki.Storage.Disk.SegmentedRetryTrace
import Alvoki.Storage.Disk.RetainedWriterState
import Alvoki.Storage.Disk.WalSegmentCachedExtentReports

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

private theorem SegmentedWriterState.RetainedReady.cleanFiles {directory : DiskDirectory} {descriptor : Nat}
    {state : SegmentedWriterState}
    (ready : state.RetainedReady directory descriptor) :
    state.wal.checkpointReopenFiles state.wal.directory state.files.keeper.staged = state.files := by
  have visible : state.files.keeper.active = some state.wal.active.bytes := by
    rw [ready.resumed.ready.keeper, ready.resumed.contents, ready.active, ready.layout.activeBytes]
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

private theorem SegmentedWriterState.RetainedReady.cleanSyncs {directory : DiskDirectory} {descriptor : Nat}
    {state : SegmentedWriterState}
    (ready : state.RetainedReady directory descriptor) :
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
theorem SegmentedWriterState.RetainedReady.cleanReopenRetained {directory : DiskDirectory} {descriptor nextDescriptor nextRef : Nat}
    {state : SegmentedWriterState} (ready : state.RetainedReady directory descriptor)
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
      session.directory = directory ∧ session.descriptor = nextDescriptor ∧ session.phase = .ready next.installed ∧
      session.phaseRef = nextRef ∧ session.sessionRef = nextRef + 1 ∧
      session.phaseRef ≠ session.sessionRef ∧ session.phaseRef ∉ liveRefs ∧ session.sessionRef ∉ liveRefs ∧
      table.pins.active = [] ∧ next.RetainedReady directory nextDescriptor := by
  intro released attempt
  have closed : runCloseWithFiles directory descriptor .success (.ready state.installed, ⟨state.files, state.owners⟩) =
      .ok () (.closed, released) := by
    dsimp only [runCloseWithFiles]
    rw [runClose_open (by simp) .success, LockOwners.release_owned ready.held]
  have acquire : TryLockObserves released.owners directory (.ok true) := by
    simp [TryLockObserves, released, LockOwners.set]
  have samePair := ready.walPair
  have decoded : state.wal.directory.active.walRange = some state.target.range := samePair.symm ▸ state.target.decoded
  have accepted : state.published.AcceptsVersioned state.history.length.toUInt64
      (WAL.Boundary.CheckpointRepresentsPrefix state.history) state.wal.directory.active.manifest :=
    samePair.symm ▸ ready.resumed.accepted
  have source := ready.cleanFiles
  obtain ⟨directoryFixed, keeperFixed⟩ := ready.cleanSyncs
  have recovered := runOpenWithInstallation_checkpointCut (owners := released.owners)
    ready.layout ready.valid ready.resumed.ordered .visible decoded ready.resumed.through
    accepted raw state.files.keeper.staged liveRefs fresh acquire unlock removeFile write sync renameFile
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
    simpa only [next, sameCheckpoint, ← ready.resumed.generation, exactBytes, ready.resumed.keeper, ready.active] using phase
  have nextReady : next.RetainedReady directory nextDescriptor :=
    ⟨⟨ready.resumed.ready, ready.resumed.through, ready.resumed.keeper, ready.resumed.bytes, ready.resumed.contents,
      ready.resumed.generation, ready.resumed.selected, ready.resumed.accepted, ready.resumed.ordered,
      bounds, ⟨model, refines, history⟩⟩, ready.layout, ready.valid, ready.spans, ready.directoryFiles, ready.sealedFiles, ready.active,
      ready.manifestFiles, held⟩
  exact ⟨closed, session, final, table, reopened, filesAfter, identities.1, path, lock,
    installed, identities.2.1, identities.2.2, separate, freshPhase, freshSession, pins, nextReady⟩

theorem SegmentedWriterState.Ready.cleanReopen {directory : DiskDirectory} {descriptor nextDescriptor nextRef : Nat}
    {state : SegmentedWriterState} (ready : state.Ready directory descriptor)
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
      session.directory = directory ∧ session.descriptor = nextDescriptor ∧ session.phase = .ready next.installed ∧
      session.phaseRef = nextRef ∧ session.sessionRef = nextRef + 1 ∧
      session.phaseRef ≠ session.sessionRef ∧ session.phaseRef ∉ liveRefs ∧ session.sessionRef ∉ liveRefs ∧
      table.pins.active = [] ∧ next.Ready directory nextDescriptor := by
  obtain ⟨closed, session, final, table, opened, files, owners, path, lock, phase, phaseRef, sessionRef, separate,
    freshPhase, freshSession, pins, next⟩ :=
    ready.toRetained.cleanReopenRetained liveRefs fresh unlock raw removeFile write sync renameFile syncDirectory syncKeeper
  exact ⟨closed, session, final, table, opened, files, owners, path, lock, phase, phaseRef, sessionRef, separate,
    freshPhase, freshSession, pins, ⟨next.resumed, next.layout, ready.chain, next.directoryFiles, next.sealedFiles,
      next.active, next.manifestFiles, next.held⟩⟩

/-- The read and effect reports used to reopen a settled writer after its
explicit close. A new allocation supplies the session reference identities. -/
structure SegmentedCleanReopenReport (directory : DiskDirectory) (before : SegmentedWriterState)
    (oldDescriptor nextDescriptor : Nat) where
  nextRef : Nat
  liveRefs : List Nat
  unlock : UnlockReport
  raw : HealthyCheckpointCutReports directory
    ((before.owners.set (directory.file .lock) none).set (directory.file .lock) (some nextDescriptor))
    nextDescriptor before.wal before.wal.directory.active before.target.range.watermark before.published.durable
  removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit)
  write : FilePath → ByteArray → EStateM IO.Error FileImage Unit
  sync : Array FilePath → EStateM IO.Error FileImage Unit
  renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit

namespace SegmentedCleanReopenReport

variable {directory : DiskDirectory} {before : SegmentedWriterState} {oldDescriptor nextDescriptor : Nat}

def released (directory : DiskDirectory) (before : SegmentedWriterState) : LockedFileState FileImage :=
  ⟨before.files, before.owners.set (directory.file .lock) none⟩

def attempt (report : SegmentedCleanReopenReport directory before oldDescriptor nextDescriptor) : BoundedReopenAttempt :=
  report.raw.openAttempt report.nextRef report.unlock report.removeFile report.write report.sync report.renameFile

structure Valid (report : SegmentedCleanReopenReport directory before oldDescriptor nextDescriptor) : Prop where
  fresh : ∀ ref ∈ report.liveRefs, ref < report.nextRef
  syncDirectory : report.sync #[directory.path] before.files = .ok () before.files
  syncKeeper : report.sync #[directory.file (.walSegment before.wal.active.first)] before.files = .ok () before.files

private def reopenedWriter (before : SegmentedWriterState) (table : PackedTable) (owners : LockOwners) :
    SegmentedWriterState :=
  { before with installed := { before.installed with table }, owners }

/-- The exact return from the shared close and subsequent bounded attempt.
A reused numeric descriptor still receives fresh session references. -/
structure Installs (report : SegmentedCleanReopenReport directory before oldDescriptor nextDescriptor)
    (after : SegmentedWriterState) : Prop where
  closeEffect : runCloseWithFiles directory oldDescriptor .success (.ready before.installed, ⟨before.files, before.owners⟩) =
    .ok () (.closed, released directory before)
  openEffect : ∃ session final table,
    report.attempt.run directory (released directory before) = .ok session final ∧
    final.image = before.files ∧ session.phase = .ready (reopenedWriter before table final.owners).installed ∧
    after = reopenedWriter before table final.owners

theorem installs (report : SegmentedCleanReopenReport directory before oldDescriptor nextDescriptor)
    (observed : report.Valid) (ready : before.Ready directory oldDescriptor) :
    ∃ after, report.Installs after ∧ after.Ready directory nextDescriptor := by
  obtain ⟨closed, session, final, table, opened, files, _, _, _, phase, _, _, _, _, _, _, next⟩ :=
    ready.cleanReopen report.liveRefs observed.fresh report.unlock report.raw report.removeFile report.write
      report.sync report.renameFile observed.syncDirectory observed.syncKeeper
  exact ⟨reopenedWriter before table final.owners, ⟨closed, session, final, table, opened, files, phase, rfl⟩, next⟩

theorem installsRetained (report : SegmentedCleanReopenReport directory before oldDescriptor nextDescriptor)
    (observed : report.Valid) (ready : before.RetainedReady directory oldDescriptor) :
    ∃ after, report.Installs after ∧ after.RetainedReady directory nextDescriptor := by
  obtain ⟨closed, session, final, table, opened, files, _, _, _, phase, _, _, _, _, _, _, next⟩ :=
    ready.cleanReopenRetained report.liveRefs observed.fresh report.unlock report.raw report.removeFile report.write
      report.sync report.renameFile observed.syncDirectory observed.syncKeeper
  exact ⟨reopenedWriter before table final.owners, ⟨closed, session, final, table, opened, files, phase, rfl⟩, next⟩

/-- Closing the previous writer and reading the immutable checkpoint and
WAL through the cached opener install the same next session. -/
theorem installsRetainedCached (report : SegmentedCleanReopenReport directory before oldDescriptor nextDescriptor)
    (observed : report.Valid) (ready : before.RetainedReady directory oldDescriptor)
    (sizes : SizedCheckpointRunReports directory report.raw.reports before.wal.directory.active.manifest
      before.published.durable)
    (cached : CachedWalFileReports directory report.raw.reports before.wal before.target.range.watermark ByteArray.empty) :
    ∃ after session final,
      report.Installs after ∧
      runOpenWithInstallation directory nextDescriptor report.nextRef (.ok true) report.unlock
        (report.raw.reopenCached sizes cached report.removeFile report.write report.sync report.renameFile)
        (released directory before) = .ok session final ∧
      session.phase = .ready after.installed ∧ final.image = after.files ∧ final.owners = after.owners := by
  have decoded : before.wal.directory.active.walRange = some before.target.range :=
    ready.walPair.symm ▸ before.target.decoded
  have checkpoint : SelectedIntegrityCheckpoint before.published.durable before.wal.directory.active.manifest
      before.checkpoint := ready.walPair.symm ▸ ready.resumed.selected
  have same := report.raw.reopenCached_eq sizes cached ready.layout ready.valid (List.mem_cons_self ..)
    decoded rfl ready.resumed.through checkpoint report.removeFile report.write report.sync report.renameFile
  obtain ⟨after, endpoint, _⟩ := report.installsRetained observed ready
  obtain ⟨session, final, table, ran, files, phase, exactWriter⟩ := endpoint.openEffect
  refine ⟨after, session, final, endpoint, ?_, exactWriter.symm ▸ phase, ?_, ?_⟩
  · rw [same]
    exact ran
  · rw [exactWriter]
    exact files
  · rw [exactWriter]
    rfl

theorem Installs.unique {report : SegmentedCleanReopenReport directory before oldDescriptor nextDescriptor}
    {left right : SegmentedWriterState} (a : report.Installs left) (b : report.Installs right) : left = right := by
  obtain ⟨_, _, leftTable, leftOpen, _, leftPhase, rfl⟩ := a.openEffect
  obtain ⟨_, _, rightTable, rightOpen, _, rightPhase, rfl⟩ := b.openEffect
  obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj (leftOpen.symm.trans rightOpen)
  have same : leftTable = rightTable := congrArg Installed.table (Phase.ready.inj (leftPhase.symm.trans rightPhase))
  rw [same]

theorem Installs.preservesReady {report : SegmentedCleanReopenReport directory before oldDescriptor nextDescriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after) (observed : report.Valid)
    (ready : before.Ready directory oldDescriptor) : after.Ready directory nextDescriptor := by
  obtain ⟨_, exactEndpoint, next⟩ := report.installs observed ready
  exact exactEndpoint.unique endpoint ▸ next

theorem Installs.preservesRetained {report : SegmentedCleanReopenReport directory before oldDescriptor nextDescriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after) (observed : report.Valid)
    (ready : before.RetainedReady directory oldDescriptor) : after.RetainedReady directory nextDescriptor := by
  obtain ⟨_, exactEndpoint, next⟩ := report.installsRetained observed ready
  exact exactEndpoint.unique endpoint ▸ next

theorem Installs.preservesChain {report : SegmentedCleanReopenReport directory before oldDescriptor nextDescriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after)
    (chain : WalSegment.Chain before.history 0 before.wal.segments) :
    WalSegment.Chain after.history 0 after.wal.segments := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := endpoint.openEffect
  exact chain

theorem Installs.history {report : SegmentedCleanReopenReport directory before oldDescriptor nextDescriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after) : after.history = before.history := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := endpoint.openEffect
  rfl

theorem Installs.generation {report : SegmentedCleanReopenReport directory before oldDescriptor nextDescriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after) :
    after.installed.generation = before.installed.generation := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := endpoint.openEffect
  rfl

end SegmentedCleanReopenReport

end Alvoki.Storage.DiskSession
