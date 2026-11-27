import Alvoki.Storage.Disk.WalBatchCommitReports
import Alvoki.Storage.Disk.RetainedWriterState
import Alvoki.Storage.Disk.Proofs.Append.AppendGroupedReports
import Alvoki.Storage.Disk.WalBatchSession
import Alvoki.Storage.Disk.SingleWritePreflight

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WalSegmentCommit WAL.Boundary SyncHandleRouting

/-- An acknowledged batch uses the native publication callbacks and
keeps their exact final file state. -/
structure SegmentedBatchAppendReport (directory : DiskDirectory) (before : SegmentedWriterState) where
  rows : List (UInt64 × Option UInt64)
  batch : List WAL.Write
  table : PackedTable
  effects : WriteEffects
  append : FilePath → ByteArray → EStateM IO.Error WriteFiles Unit
  stage : FilePath → ByteArray → EStateM IO.Error WriteFiles Unit
  sync : Array FilePath → EStateM IO.Error WriteFiles Unit
  rename : FilePath → FilePath → EStateM IO.Error WriteFiles Unit
  written : WriteFiles
  nonempty : rows ≠ []
  prepared : prepareBatch before.installed.table rows = some (batch, table)
  fits : before.installed.walBytes + WAL.frameSize * rows.length < UInt64.size
  reports : BatchCommitReports directory before.installed.activeFirst before.history batch
    (before.installed.walBytes + WAL.frameSize * rows.length) effects
    (before.files.directory.staged .walBoundary) append stage sync rename
  committed : commitBytesAt directory before.installed.activeFirst (WAL.encodeBatch batch)
    (before.installed.walBytes + WAL.frameSize * rows.length) append stage sync rename
    (WriteFiles.initial before.history (before.files.directory.staged .walBoundary)) = .ok () written

def SegmentedBatchAppendReport.nextInstalled {directory before} (report : SegmentedBatchAppendReport directory before) :
    Installed :=
  { before.installed with table := report.table, walBytes := before.installed.walBytes + WAL.frameSize * report.rows.length }

/-- The metadata on the path actually checked by the native writer. The
lookup is read-only at this reached state. -/
structure BatchActiveGuard (directory : DiskDirectory) (installed : Installed) where
  lookup : FilePath → Except IO.Error IO.FS.Metadata
  metadata : IO.FS.Metadata
  reached : lookup (directory.file (.walSegment installed.activeFirst)) = .ok metadata
  regular : metadata.type = .file
  privateFile : metadata.numLinks = 1
  extent : metadata.byteSize.toNat = installed.walBytes - installed.activeFirst * WAL.frameSize

theorem BatchActiveGuard.checked {image : Type} {directory : DiskDirectory} {installed : Installed}
    (guard : BatchActiveGuard directory installed) (before : image) :
    checkActiveSegmentWith (m := EStateM IO.Error image) directory installed
      (fun path => liftExcept (guard.lookup path)) before = .ok () before := by
  have fileKind : (IO.FS.FileType.file == .file) = true := rfl
  simp [checkActiveSegmentWith, checkPrivateRegularWith, guard.reached, guard.regular, guard.privateFile,
    guard.extent, fileKind, liftExcept, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

private def observeWriteFiles {image α : Type} (error : IO.Error → DiskWriteError)
    (run : EStateM IO.Error image α) : EStateM DiskWriteError (Phase Installed × LockedFileState image) α :=
  fun (phase, before) => match run before.image with
  | .ok value after => .ok value (phase, { before with image := after })
  | .error cause after => .error (error cause) (phase, { before with image := after })

/-- Interpret the complete native batch schedule while keeping the same
lock owner cell. The file state can also record the reached handle cache. -/
def runBatchWrite {image : Type} (directory : DiskDirectory) (rows : List (UInt64 × Option UInt64))
    (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (append stage : FilePath → ByteArray → EStateM IO.Error image Unit)
    (sync : Array FilePath → EStateM IO.Error image Unit)
    (rename : FilePath → FilePath → EStateM IO.Error image Unit) :
    EStateM DiskWriteError (Phase Installed × LockedFileState image) UInt64 :=
  writeBatchSchedule rows
    (fun state => match (state.1.installed : Except IO.Error Installed) with
      | .ok installed => .ok installed state
      | .error cause => .error (.rejected cause) state)
    DiskWriteError.rejected
    (fun prepared => match prepared with
      | some value => pure value
      | none => throw (.rejected (IO.userError "write sequence space exhausted")))
    (fun installed => observeWriteFiles .rejected <|
      checkActiveSegmentWith directory installed (fun path => liftExcept (lookup path)))
    (fun phase => modify fun state => (phase, state.2))
    (fun installed events bytes => observeWriteFiles .commitUnknown <|
      commitBytesAt directory installed.activeFirst (WAL.encodeBatch events) bytes append stage sync rename)

/-- An empty batch reads the ready sequence and leaves the phase, files,
cache and owner unchanged without calling the metadata or commit callbacks. -/
theorem runBatchWrite_empty {image : Type} (directory : DiskDirectory) (installed : Installed)
    (before : LockedFileState image) (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (append stage : FilePath → ByteArray → EStateM IO.Error image Unit)
    (sync : Array FilePath → EStateM IO.Error image Unit) (rename : FilePath → FilePath → EStateM IO.Error image Unit) :
    runBatchWrite directory [] lookup append stage sync rename (.ready installed, before) =
      .ok installed.table.committed (.ready installed, before) := rfl

private theorem activeGuard_readOnly {image : Type} (directory : DiskDirectory) (installed : Installed)
    (lookup : FilePath → Except IO.Error IO.FS.Metadata) (before : image) :
    checkActiveSegmentWith (m := EStateM IO.Error image) directory installed
      (fun path => liftExcept (lookup path)) before =
      match checkActiveSegmentWith directory installed lookup with
      | .ok () => .ok () before
      | .error cause => .error cause before := by
  unfold checkActiveSegmentWith
  cases found : lookup (directory.file (.walSegment installed.activeFirst)) with
  | error cause =>
    simp [found, liftExcept, Bind.bind, Except.bind, EStateM.bind] <;> rfl
  | ok metadata =>
    by_cases privateFile : (metadata.type == .file) = true ∧ metadata.numLinks = 1
    · by_cases extent : metadata.byteSize.toNat = installed.walBytes - installed.activeFirst * WAL.frameSize <;>
        simp [found, liftExcept, checkPrivateRegularWith, Bind.bind, Except.bind, EStateM.bind,
          Pure.pure, Except.pure, EStateM.pure, privateFile, extent] <;> rfl
    · simp [found, liftExcept, checkPrivateRegularWith, Bind.bind, Except.bind, EStateM.bind,
        Pure.pure, EStateM.pure, privateFile] <;> rfl

/-- The installed marker accounts for the complete logical history in bytes.
Even at WAL byte-count exhaustion, the one-row sequence check can succeed. -/
private theorem SegmentedWriterState.RetainedReady.hasSingleSequence {directory descriptor before}
    (ready : SegmentedWriterState.RetainedReady directory descriptor before) :
    before.installed.table.committed.toNat + 1 < UInt64.size := by
  obtain ⟨model, refinement, represented⟩ := ready.resumed.canonical
  have sequence := represented.committed_count
  rw [← refinement.committed] at sequence
  obtain ⟨_, _, _, length, _, _, size⟩ :=
    DirectoryPublication.Bindings.walRange_accounting before.target.decoded
  rw [ready.resumed.through, ← sequence, WAL.frameSize] at size
  have fits := length.toNat_lt_size
  have space : 2 ≤ UInt64.size := by decide
  omega

/-- In a retained-ready writer, the singleton's first sequence guard can
prepare its write even when its later WAL byte-count guard rejects. -/
theorem SegmentedWriterState.RetainedReady.preparesSingleWrite {directory descriptor} {writer : SegmentedWriterState}
    (ready : writer.RetainedReady directory descriptor) (key : UInt64) (value : Option UInt64) :
    ∃ next, prepareWrite writer.installed.table key value = some (⟨next.committed, key, value⟩, next) := by
  have sequence : (writer.installed.table.write key value).isSome = true :=
    (PackedTable.write_iff _ _ _).mpr ready.hasSingleSequence
  obtain ⟨next, written⟩ := Option.isSome_iff_exists.mp sequence
  exact ⟨next, by simp [prepareWrite, written]⟩

/-- Single and one-row batch writes from a retained-ready writer have
identical outcomes under the same native append, stage, sync and rename
callbacks. Sequence allocation cannot mask byte-count exhaustion even
though the two public schedules run those checks in opposite orders. -/
theorem runSingleWrite_eq_runBatchWrite_singleton {image : Type} {directory : DiskDirectory}
    {descriptor : Nat} {writer : SegmentedWriterState}
    (ready : writer.RetainedReady directory descriptor)
    (key : UInt64) (value : Option UInt64) (before : LockedFileState image)
    (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (append stage : FilePath → ByteArray → EStateM IO.Error image Unit)
    (sync : Array FilePath → EStateM IO.Error image Unit) (rename : FilePath → FilePath → EStateM IO.Error image Unit) :
    runSingleWrite directory key value lookup
      (fun state event count => commitAt directory state.activeFirst event count append stage sync rename)
      (.ready writer.installed, before) =
    runBatchWrite directory [(key, value)] lookup append stage sync rename (.ready writer.installed, before) := by
  obtain ⟨next, single⟩ := ready.preparesSingleWrite key value
  let event : WAL.Write := ⟨next.committed, key, value⟩
  change prepareWrite writer.installed.table key value = some (event, next) at single
  have batch : prepareBatch writer.installed.table [(key, value)] = some ([event], next) := by
    simp [prepareBatch_singleton, single]
  by_cases fits : writer.installed.walBytes + WAL.frameSize < UInt64.size
  · cases active : (checkActiveSegmentWith directory writer.installed lookup : Except IO.Error Unit) with
    | error cause =>
      rw [runSingleWrite_rejectedActive single fits active]
      simp [runBatchWrite, writeBatchSchedule, Phase.installed, batch, fits, active, activeGuard_readOnly,
        observeWriteFiles, Bind.bind, EStateM.bind, Pure.pure, Except.pure, EStateM.pure]
    | ok accepted =>
      cases accepted
      rw [runSingleWrite_of_preflight single fits active]
      simp [runBatchWrite, writeBatchSchedule, Phase.installed, batch, fits, active, activeGuard_readOnly,
        observeWriteFiles, Bind.bind, EStateM.bind, Pure.pure, Except.pure, EStateM.pure, WAL.encodeBatch_singleton,
        runPreparedWrite, commitAt]
      simp only [publishPreparedWrite, publishPrepared, modify, modifyGet, MonadStateOf.modifyGet,
        EStateM.modifyGet, observeWriteFiles, Bind.bind, EStateM.bind]
      cases commitBytesAt directory writer.installed.activeFirst (WAL.encodeFrame event)
          (writer.installed.walBytes + WAL.frameSize) append stage sync rename before.image with
      | ok accepted reached => cases accepted; rfl
      | error cause reached => rfl
  · rw [runSingleWrite_rejectedWalCount single (Nat.le_of_not_gt fits)]
    simp [runBatchWrite, writeBatchSchedule, Phase.installed, fits, Bind.bind, EStateM.bind,
      Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- The ready preflight's first failing check. Phase rejection is
handled before these operations. An empty batch reaches none of them. -/
inductive BatchPreflightRejection (directory : DiskDirectory) (installed : Installed)
    (rows : List (UInt64 × Option UInt64)) (lookup : FilePath → Except IO.Error IO.FS.Metadata) : IO.Error → Prop where
  | byteCount (nonempty : rows ≠ []) (overflow : UInt64.size ≤ installed.walBytes + WAL.frameSize * rows.length) :
      BatchPreflightRejection directory installed rows lookup (IO.userError "WAL byte count is too large")
  | sequence (nonempty : rows ≠ []) (fits : installed.walBytes + WAL.frameSize * rows.length < UInt64.size)
      (exhausted : prepareBatch installed.table rows = none) :
      BatchPreflightRejection directory installed rows lookup (IO.userError "write sequence space exhausted")
  | active (nonempty : rows ≠ []) (fits : installed.walBytes + WAL.frameSize * rows.length < UInt64.size)
      (prepared : prepareBatch installed.table rows = some (events, table))
      (checked : (checkActiveSegmentWith directory installed lookup : Except IO.Error Unit) = .error cause) :
      BatchPreflightRejection directory installed rows lookup cause

/-- A failed checked preflight determines the exact error with no
dependence on append, staging, sync or rename. -/
theorem BatchPreflightRejection.run {image : Type} {directory : DiskDirectory} {installed : Installed}
    {rows : List (UInt64 × Option UInt64)} {lookup : FilePath → Except IO.Error IO.FS.Metadata} {cause : IO.Error}
    (rejected : BatchPreflightRejection directory installed rows lookup cause) (before : LockedFileState image)
    (append stage : FilePath → ByteArray → EStateM IO.Error image Unit)
    (sync : Array FilePath → EStateM IO.Error image Unit) (rename : FilePath → FilePath → EStateM IO.Error image Unit) :
    runBatchWrite directory rows lookup append stage sync rename (.ready installed, before) =
      .error (.rejected cause) (.ready installed, before) := by
  have nonempty : rows.isEmpty = false := by
    cases rows with
    | nil => cases rejected <;> contradiction
    | cons => rfl
  cases rejected with
  | byteCount _ overflow =>
    simp [runBatchWrite, writeBatchSchedule, Phase.installed, nonempty, Nat.not_lt.mpr overflow, Bind.bind,
      EStateM.bind, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  | sequence _ fits exhausted =>
    simp [runBatchWrite, writeBatchSchedule, Phase.installed, nonempty, fits, exhausted, Bind.bind,
      EStateM.bind, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  | active _ fits prepared checked =>
    simp [runBatchWrite, writeBatchSchedule, Phase.installed, nonempty, fits, prepared, checked, observeWriteFiles,
      activeGuard_readOnly, Bind.bind, EStateM.bind, Pure.pure, Except.pure, EStateM.pure]

/-- A rejected batch returns the original phase, files, cache and owner.
Its error is independent of every WAL publication callback. -/
theorem runBatchWrite_rejected {image : Type} {directory : DiskDirectory}
    {rows : List (UInt64 × Option UInt64)} {lookup : FilePath → Except IO.Error IO.FS.Metadata}
    {append stage : FilePath → ByteArray → EStateM IO.Error image Unit}
    {sync : Array FilePath → EStateM IO.Error image Unit}
    {rename : FilePath → FilePath → EStateM IO.Error image Unit}
    {phase : Phase Installed} {before : LockedFileState image}
    {after : Phase Installed × LockedFileState image} {cause : IO.Error}
    (rejected : runBatchWrite directory rows lookup append stage sync rename (phase, before) =
      .error (.rejected cause) after)
    (append' stage' : FilePath → ByteArray → EStateM IO.Error image Unit)
    (sync' : Array FilePath → EStateM IO.Error image Unit)
    (rename' : FilePath → FilePath → EStateM IO.Error image Unit) :
    after = (phase, before) ∧
    runBatchWrite directory rows lookup append' stage' sync' rename' (phase, before) =
      .error (.rejected cause) (phase, before) := by
  cases phase with
  | poisoned =>
    cases rejected
    exact ⟨rfl, rfl⟩
  | closed =>
    cases rejected
    exact ⟨rfl, rfl⟩
  | ready installed =>
    simp only [runBatchWrite, writeBatchSchedule, Phase.installed, Pure.pure, Except.pure,
      Bind.bind, EStateM.bind] at rejected ⊢
    by_cases empty : rows.isEmpty = true
    · simp [empty, EStateM.pure] at rejected
    simp only [ite_eq_right empty] at rejected ⊢
    by_cases fits : installed.walBytes + WAL.frameSize * rows.length < UInt64.size
    · simp only [ite_eq_left fits] at rejected ⊢
      cases prepared : prepareBatch installed.table rows with
      | none =>
        rw [prepared] at rejected
        cases rejected
        exact ⟨rfl, rfl⟩
      | some result =>
        obtain ⟨events, table⟩ := result
        simp only [prepared, EStateM.bind, EStateM.pure, observeWriteFiles, activeGuard_readOnly]
          at rejected ⊢
        cases checked : checkActiveSegmentWith directory installed lookup with
        | error cause =>
          rw [checked] at rejected
          cases rejected
          exact ⟨rfl, rfl⟩
        | ok value =>
          cases value
          rw [checked] at rejected
          cases ran : commitBytesAt directory installed.activeFirst (WAL.encodeBatch events)
            (installed.walBytes + WAL.frameSize * rows.length) append stage sync rename before.image <;>
            simp [publishPreparedWrite, publishPrepared, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
              Pure.pure, Bind.bind, EStateM.bind, EStateM.pure, observeWriteFiles, ran] at rejected
    · simp only [ite_eq_right fits] at rejected ⊢
      cases rejected
      exact ⟨rfl, rfl⟩

/-- Successful reached primitive callbacks determine the native write result. -/
theorem runBatchWrite_acknowledges {image : Type} {directory : DiskDirectory}
    {before : LockedFileState image} {written : image} {installed : Installed}
    (guard : BatchActiveGuard directory installed)
    {rows : List (UInt64 × Option UInt64)} (nonempty : rows ≠ [])
    {batch : List WAL.Write} {table : PackedTable} (prepared : prepareBatch installed.table rows = some (batch, table))
    (fits : installed.walBytes + WAL.frameSize * rows.length < UInt64.size)
    {append stage : FilePath → ByteArray → EStateM IO.Error image Unit}
    {sync : Array FilePath → EStateM IO.Error image Unit}
    {rename : FilePath → FilePath → EStateM IO.Error image Unit}
    (committed : commitBytesAt directory installed.activeFirst (WAL.encodeBatch batch)
      (installed.walBytes + WAL.frameSize * rows.length) append stage sync rename before.image = .ok () written) :
    runBatchWrite directory rows guard.lookup append stage sync rename (.ready installed, before) =
      .ok table.committed
        (.ready { installed with table, walBytes := installed.walBytes + WAL.frameSize * rows.length },
          { before with image := written }) := by
  have rowsPresent : rows.isEmpty = false := List.isEmpty_eq_false_iff.mpr nonempty
  simp [runBatchWrite, writeBatchSchedule, Phase.installed, Bind.bind, EStateM.bind,
    rowsPresent, fits, prepared, observeWriteFiles, guard.checked before.image,
    publishPreparedWrite, publishPrepared, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    Pure.pure, Except.pure, EStateM.pure, committed]

/-- After checked preflight, a returned commit error fixes the exact
poisoned phase, image and original error of the batch schedule. -/
theorem runBatchWrite_commitUnknown {image : Type} {directory : DiskDirectory}
    {before : LockedFileState image} {reached : image} {installed : Installed}
    (guard : BatchActiveGuard directory installed)
    {rows : List (UInt64 × Option UInt64)} (nonempty : rows ≠ [])
    {batch : List WAL.Write} {table : PackedTable} (prepared : prepareBatch installed.table rows = some (batch, table))
    (fits : installed.walBytes + WAL.frameSize * rows.length < UInt64.size)
    {append stage : FilePath → ByteArray → EStateM IO.Error image Unit}
    {sync : Array FilePath → EStateM IO.Error image Unit}
    {rename : FilePath → FilePath → EStateM IO.Error image Unit} {cause : IO.Error}
    (failed : commitBytesAt directory installed.activeFirst (WAL.encodeBatch batch)
      (installed.walBytes + WAL.frameSize * rows.length) append stage sync rename before.image = .error cause reached) :
    runBatchWrite directory rows guard.lookup append stage sync rename (.ready installed, before) =
      .error (.commitUnknown cause) (.poisoned, { before with image := reached }) := by
  have rowsPresent : rows.isEmpty = false := List.isEmpty_eq_false_iff.mpr nonempty
  simp [runBatchWrite, writeBatchSchedule, Phase.installed, Bind.bind, EStateM.bind,
    rowsPresent, fits, prepared, observeWriteFiles, guard.checked before.image,
    publishPreparedWrite, publishPrepared, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    Pure.pure, Except.pure, EStateM.pure, failed]

/-- Project the reported native callbacks while retaining their reached cache.
Only the append and marker steps actually reached need a report. -/
structure ObservedBatchPublication (directory : DiskDirectory) (first : Nat) (bytes : ByteArray)
    (count : Nat) (initial : WriteFiles)
    (appendFiles stageFiles : FilePath → ByteArray → EStateM IO.Error WriteFiles Unit)
    (syncFiles : Array FilePath → EStateM IO.Error WriteFiles Unit)
    (renameFiles : FilePath → FilePath → EStateM IO.Error WriteFiles Unit)
    (handle : Type) where
  cache : Cache handle
  append : FilePath → ByteArray → EStateM IO.Error (Cache handle × WriteFiles) Unit
  stage : FilePath → ByteArray → EStateM IO.Error (Cache handle × WriteFiles) Unit
  sync : Array FilePath → EStateM IO.Error (Cache handle × WriteFiles) Unit
  rename : FilePath → FilePath → EStateM IO.Error (Cache handle × WriteFiles) Unit
  appendProjects :
    let keeper := directory.file (.walSegment first)
    withoutWriteGroupCache (append keeper bytes (cache, initial)) = appendFiles keeper bytes initial
  markerProjects : ∀ appended : Cache handle × WriteFiles,
    append (directory.file (.walSegment first)) bytes (cache, initial) = .ok () appended →
    ∀ (prior : List Publication.Step) step remaining reached, Publication.steps = prior ++ step :: remaining →
      let native := performMarkerAt directory first count stage sync rename
      (prior.forM native) appended = .ok () reached →
      withoutWriteGroupCache (native step reached) =
        performMarkerAt directory first count stageFiles syncFiles renameFiles step reached.2

/-- The successful batch also reached the native private-keeper preflight. -/
structure ObservedBatchWrite {directory before} (report : SegmentedBatchAppendReport directory before)
    (handle : Type) extends
      ObservedBatchPublication directory before.installed.activeFirst (WAL.encodeBatch report.batch)
        report.nextInstalled.walBytes (WriteFiles.initial before.history (before.files.directory.staged .walBoundary))
        report.append report.stage report.sync report.rename handle where
  guard : BatchActiveGuard directory before.installed

/-- The failed publication uses the same cache and callback projection as a
successful batch after the active-file preflight. -/
structure ObservedBatchFailure {directory before} (failure : SegmentedBatchFailure directory before)
    (handle : Type) extends
      ObservedBatchPublication directory before.installed.activeFirst (WAL.encodeBatch failure.batch)
        failure.proposed.walBytes (WriteFiles.initial before.history (before.wal.directory.staged .walBoundary))
        failure.append failure.stage failure.sync failure.rename handle where
  guard : BatchActiveGuard directory before.installed

/-- Project the reached cached publication result before deciding whether
the original write acknowledges or returns an uncertain commit. -/
theorem ObservedBatchPublication.projectsReturn {handle : Type}
    {directory first bytes count initial append stage sync rename}
    (observed : ObservedBatchPublication directory first bytes count initial append stage sync rename handle) :
    withoutWriteGroupCache (commitBytesAt directory first bytes count
      observed.append observed.stage observed.sync observed.rename (observed.cache, initial)) =
      commitBytesAt directory first bytes count append stage sync rename initial := by
  rw [withoutWriteGroupCache_eq_projectResult]
  apply commitBytesAt_projects Prod.snd directory first bytes count
    observed.append observed.stage observed.sync observed.rename append stage sync rename (observed.cache, initial)
  · simpa only [withoutWriteGroupCache_eq_projectResult] using observed.appendProjects
  · intro appended returned prior step remaining reached ordered _actual ranPrefix
    simpa only [withoutWriteGroupCache_eq_projectResult] using
      observed.markerProjects appended returned prior step remaining reached ordered ranPrefix

/-- Execute the native-shaped batch from the checked active segment. The
returned owner and installed table are exact, and the cache is the one
reached by this same set of file operations. -/
theorem ObservedBatchWrite.acknowledges {handle : Type} {directory before}
    {report : SegmentedBatchAppendReport directory before} (observed : ObservedBatchWrite report handle) :
    ∃ cacheAfter, runBatchWrite directory report.rows observed.guard.lookup observed.append
      observed.stage observed.sync observed.rename
      (.ready before.installed, ⟨(observed.cache, WriteFiles.initial before.history
        (before.files.directory.staged .walBoundary)), before.owners⟩) =
      .ok report.table.committed (.ready report.nextInstalled, ⟨(cacheAfter, report.written), before.owners⟩) := by
  have projected := observed.toObservedBatchPublication.projectsReturn
  rw [show commitBytesAt directory before.installed.activeFirst (WAL.encodeBatch report.batch)
      report.nextInstalled.walBytes report.append report.stage report.sync report.rename
      (WriteFiles.initial before.history (before.files.directory.staged .walBoundary)) = .ok () report.written from
    report.committed] at projected
  cases committed : commitBytesAt directory before.installed.activeFirst (WAL.encodeBatch report.batch)
      report.nextInstalled.walBytes observed.append observed.stage observed.sync observed.rename
      (observed.cache, WriteFiles.initial before.history (before.files.directory.staged .walBoundary)) with
  | error cause reached =>
    simp [committed, withoutWriteGroupCache] at projected
  | ok value reached =>
    cases value
    obtain ⟨cacheAfter, written⟩ := reached
    have files : written = report.written := by
      simpa [committed, withoutWriteGroupCache] using projected
    subst written
    exact ⟨cacheAfter, runBatchWrite_acknowledges observed.guard report.nonempty report.prepared report.fits committed⟩

/-- Project the same reached cached publication error and file state
before interpreting the phase assignments around it. -/
theorem ObservedBatchFailure.cachedCommitError {handle : Type} {directory before}
    {failure : SegmentedBatchFailure directory before} (observed : ObservedBatchFailure failure handle) :
    ∃ cacheAfter, commitBytesAt directory before.installed.activeFirst (WAL.encodeBatch failure.batch)
      failure.proposed.walBytes observed.append observed.stage observed.sync observed.rename
      (observed.cache, WriteFiles.initial before.history (before.wal.directory.staged .walBoundary)) =
      .error failure.cause (cacheAfter, failure.failed) := by
  have projected := observed.toObservedBatchPublication.projectsReturn
  have ran : commitBytesAt directory before.installed.activeFirst (WAL.encodeBatch failure.batch)
      failure.proposed.walBytes failure.append failure.stage failure.sync failure.rename
      (WriteFiles.initial before.history (before.wal.directory.staged .walBoundary)) = .error failure.cause failure.failed :=
    failure.ran
  rw [ran] at projected
  cases failed : commitBytesAt directory before.installed.activeFirst (WAL.encodeBatch failure.batch)
      failure.proposed.walBytes observed.append observed.stage observed.sync observed.rename
      (observed.cache, WriteFiles.initial before.history (before.wal.directory.staged .walBoundary)) with
  | ok value reached =>
    simp [failed, withoutWriteGroupCache] at projected
  | error cause reached =>
    obtain ⟨cacheAfter, files⟩ := reached
    have same : cause = failure.cause ∧ files = failure.failed := by
      simpa [failed, withoutWriteGroupCache] using projected
    obtain ⟨rfl, rfl⟩ := same
    exact ⟨cacheAfter, rfl⟩

/-- The reached batch publication error keeps the original diagnostic and
poisons the phase. The cache and failed file cut come from that same
callback run under the original owner. -/
theorem ObservedBatchFailure.commitUnknown {handle : Type} {directory before}
    {failure : SegmentedBatchFailure directory before} (observed : ObservedBatchFailure failure handle) :
    ∃ cacheAfter, runBatchWrite directory failure.rows observed.guard.lookup observed.append
      observed.stage observed.sync observed.rename
      (.ready before.installed, ⟨(observed.cache, WriteFiles.initial before.history
        (before.wal.directory.staged .walBoundary)), before.owners⟩) =
      .error (.commitUnknown failure.cause) (.poisoned, ⟨(cacheAfter, failure.failed), before.owners⟩) := by
  obtain ⟨cacheAfter, failed⟩ := observed.cachedCommitError
  exact ⟨cacheAfter, runBatchWrite_commitUnknown observed.guard failure.nonempty failure.prepared failure.fits failed⟩

/-- The publication tail acknowledges the last ordinal after installing
the prepared table under the same owner. -/
theorem SegmentedBatchAppendReport.acknowledges {directory before}
    (report : SegmentedBatchAppendReport directory before) :
    let commit := commitBytesAt directory before.installed.activeFirst (WAL.encodeBatch report.batch)
      report.nextInstalled.walBytes report.append report.stage report.sync report.rename
    let initial := WriteFiles.initial before.history (before.files.directory.staged .walBoundary)
    runPreparedWrite report.nextInstalled report.table.committed commit
      (.ready before.installed, ⟨initial, before.owners⟩) =
      .ok report.table.committed (.ready report.nextInstalled, ⟨report.written, before.owners⟩) :=
  runPreparedWrite_success before.installed report.nextInstalled report.table.committed report.committed

def SegmentedBatchAppendReport.files {directory before} (report : SegmentedBatchAppendReport directory before) :
    FileImage :=
  resumedAppendFiles before.files before.history before.installed.activeFirst report.written

/-- Extend the selected view while carrying the retained segments and owner
from the original writer. Both publication interpreters use this state. -/
def SegmentedWriterState.afterAppend (before : SegmentedWriterState) (installed : Installed)
    (batch : List WAL.Write) (written : WriteFiles) (target : Target) : SegmentedWriterState :=
  let history := before.history ++ batch
  let files := resumedAppendFiles before.files before.history before.installed.activeFirst written
  let wal := before.wal.appendSelectedView files.directory.active history
  SegmentedWriterState.ofReopen installed wal history before.published target before.checkpoint
    ⟨files, before.owners⟩

def SegmentedWriterState.SelectsAppend (before : SegmentedWriterState) (batch : List WAL.Write)
    (written : WriteFiles) (target : Target) : Prop :=
  let files := resumedAppendFiles before.files before.history before.installed.activeFirst written
  target.pair = files.directory.active ∧ target.first = before.installed.activeFirst ∧
    target.trimmed = WAL.encode ((before.history ++ batch).drop target.first)

def SegmentedBatchAppendReport.next {directory before} (report : SegmentedBatchAppendReport directory before)
    (target : Target) : SegmentedWriterState :=
  before.afterAppend report.nextInstalled report.batch report.written target

def SegmentedBatchAppendReport.Selects {directory before} (report : SegmentedBatchAppendReport directory before)
    (target : Target) : Prop :=
  before.SelectsAppend report.batch report.written target

private theorem retainedAppendStart {directory : DiskDirectory} {descriptor : Nat} {before : SegmentedWriterState}
    (ready : before.RetainedReady directory descriptor) : before.installed.activeFirst ≤ before.history.length := by
  rw [ready.resumed.keeper, ← ready.resumed.through]
  exact before.target.firstCovered

/-- The prepared batch and its settled recovery image determine the next
retained writer. The publication callbacks establish settlement separately. -/
theorem SegmentedWriterState.RetainedReady.advanceSettled {directory : DiskDirectory} {descriptor : Nat}
    {before : SegmentedWriterState}
    (ready : before.RetainedReady directory descriptor)
    {rows : List (UInt64 × Option UInt64)} {batch : List WAL.Write} {table : PackedTable}
    (prepared : prepareBatch before.installed.table rows = some (batch, table))
    (fits : before.installed.walBytes + WAL.frameSize * rows.length < UInt64.size)
    {written : WriteFiles}
    (settled :
      let count := before.installed.walBytes + WAL.frameSize * rows.length
      let files := resumedAppendFiles before.files before.history before.installed.activeFirst written
      files.directory.active = ⟨before.files.directory.active.manifest, some (WAL.Boundary.encode count.toUInt64)⟩ ∧
      files.directory.crashImages = [files.directory.active] ∧
      files.keeper.active = some (WAL.encode ((before.history ++ batch).drop before.installed.activeFirst)) ∧
      files.keeper.crashImages = [files.keeper.active]) :
    let count := before.installed.walBytes + WAL.frameSize * rows.length
    let installed : Installed := { before.installed with table, walBytes := count }
    ∃ target, before.SelectsAppend batch written target ∧
      (before.afterAppend installed batch written target).RetainedReady directory descriptor := by
  intro count
  let history := before.history ++ batch
  let installed : Installed := { before.installed with table, walBytes := count }
  let bytes := installed.walBytes
  let files := resumedAppendFiles before.files before.history before.installed.activeFirst written
  obtain ⟨model, refines, represents⟩ := ready.resumed.canonical
  have clock : before.history.length = before.installed.table.committed.toNat :=
    represents.committed_count.symm.trans (congrArg UInt64.toNat refines.committed).symm
  obtain ⟨_, ordered, _, size⟩ := prepareBatch_extends_history ready.resumed.ordered clock prepared
  have measured : bytes = (WAL.encode history).size := by
    change before.installed.walBytes + WAL.frameSize * rows.length = _
    rw [ready.resumed.bytes, size]
  have starts := retainedAppendStart ready
  obtain ⟨target, pair, range, first, contents, filesReady⟩ :=
    resumedAppendTarget ready.resumed.ready ready.resumed.through starts batch bytes measured fits settled
  have replayed := (prepareBatch_spec prepared).2.1
  obtain ⟨nextModel, replay, refined⟩ := replay_refines refines replayed
  have historyFits : (WAL.encode history).size < UInt64.size := measured ▸ fits
  have accepted := before.published.acceptsVersioned_extend_history (suffix := batch) ready.resumed.accepted historyFits
  have resumed : ResumedAppendReady installed files target history before.published before.checkpoint := by
    refine ⟨filesReady, congrArg MarkedWalRange.through range, first.symm, measured, ?_,
      ready.resumed.generation, ?_, ?_, ordered, replay_rowBounds ready.resumed.bounds replayed,
      nextModel, refined, represents.append replay⟩
    · rw [contents, first]
    · rw [pair]
      exact ready.resumed.selected
    · rw [pair]
      exact accepted
  have oldRange : before.wal.directory.active.walRange = some ⟨before.target.range.watermark, before.history.length⟩ := by
    rw [ready.walPair, ← ready.resumed.through]
    exact before.target.decoded
  have visible : files.directory.active = target.pair := filesReady.selected
  have durable : files.directory.crashImages = [files.directory.active] :=
    filesReady.settled.trans (congrArg (fun pair => [pair]) visible.symm)
  have newRange : files.directory.active.walRange = some ⟨before.target.range.watermark, history.length⟩ := by
    rw [visible, ← range]
    exact target.decoded
  obtain ⟨layout, valid, _, _⟩ :=
    ready.layout.afterRetainedSuffix ready.valid oldRange files.directory.active batch newRange
  let after := before.afterAppend installed batch written target
  have nextReady : ResumedAppendReady after.installed after.files after.target after.history
      after.published after.checkpoint :=
    ⟨resumed.ready, resumed.through, resumed.keeper, resumed.bytes, resumed.contents, resumed.generation,
      resumed.selected, resumed.accepted, resumed.ordered, resumed.bounds, resumed.canonical⟩
  have retainedLayout : after.wal.ReadLayout after.history :=
    ⟨layout.ordered, layout.forward, layout.activeEnd, layout.activeBytes⟩
  refine ⟨target, ⟨filesReady.selected.symm, first, ?_⟩,
    nextReady, retainedLayout, ?_, ready.spans, rfl, ready.sealedFiles, ?_, rfl, ready.held⟩
  · rw [contents, first]
  · intro candidate chosen
    apply valid candidate
    change candidate ∈ files.directory.active :: files.directory.crashImages at chosen
    change candidate ∈ files.directory.active :: [files.directory.active]
    rwa [durable] at chosen
  · exact first.trans (ready.resumed.keeper.trans ready.active)

/-- The normalized append endpoint stores just the appended bytes. The
keeper was read as a whole, and the settled marker has no staged payload. -/
def _root_.Alvoki.WAL.Boundary.WriteFiles.ofPublishedPayloads (prior keeper marker : ByteArray) : WriteFiles :=
  let tail := keeper.extract prior.size keeper.size
  ⟨tail, [tail], Publication.Image.settled (some marker), by simp⟩

private theorem extractAppendedTail {prior keeper tail : ByteArray} (added : keeper = prior ++ tail) :
    keeper.extract prior.size keeper.size = tail := by
  rw [added, ByteArray.extract_append]
  have empty : prior.extract prior.size (prior.size + tail.size) = ByteArray.empty :=
    ByteArray.extract_eq_empty_iff.mpr (Nat.min_le_right ..)
  simp [empty]

/-- Rebuild retained readiness from the exact keeper and marker payloads
of a settled publication. The local file effects supply those observations. -/
theorem SegmentedWriterState.RetainedReady.advancePublished {directory : DiskDirectory} {descriptor : Nat}
    {before : SegmentedWriterState} (ready : before.RetainedReady directory descriptor)
    {rows : List (UInt64 × Option UInt64)} {batch : List WAL.Write} {table : PackedTable}
    (prepared : prepareBatch before.installed.table rows = some (batch, table))
    (fits : before.installed.walBytes + WAL.frameSize * rows.length < UInt64.size)
    {keeperBytes markerBytes : ByteArray}
    (keeper : keeperBytes = before.wal.active.bytes ++ WAL.encodeBatch batch)
    (marker : markerBytes = WAL.Boundary.encode (before.installed.walBytes + WAL.frameSize * rows.length).toUInt64) :
    let count := before.installed.walBytes + WAL.frameSize * rows.length
    let installed : Installed := { before.installed with table, walBytes := count }
    let written := WriteFiles.ofPublishedPayloads before.wal.active.bytes keeperBytes markerBytes
    ∃ target, let after := before.afterAppend installed batch written target
      target.pair = ⟨before.target.pair.manifest, some markerBytes⟩ ∧
      target.first = before.installed.activeFirst ∧ after.wal.active.bytes = keeperBytes ∧
      after.RetainedReady directory descriptor := by
  intro count installed written
  let files := resumedAppendFiles before.files before.history before.installed.activeFirst written
  have starts := retainedAppendStart ready
  have suffix : WAL.encode ((before.history ++ batch).drop before.installed.activeFirst) =
      WAL.encode (before.history.drop before.installed.activeFirst) ++ WAL.encodeBatch batch := by
    rw [List.drop_append_of_le_length starts, WAL.encode_append, WAL.encodeBatch_eq]
  have actual : WAL.encode ((before.history ++ batch).drop before.installed.activeFirst) = keeperBytes := by
    rw [suffix, keeper, ready.layout.activeBytes, ← ready.active, ← ready.resumed.keeper]
  have contents : files.keeper.active = some (WAL.encode ((before.history ++ batch).drop before.installed.activeFirst)) := by
    change some (WAL.encode (before.history.drop before.installed.activeFirst) ++
      keeperBytes.extract before.wal.active.bytes.size keeperBytes.size) = _
    rw [extractAppendedTail keeper, suffix]
  have pair : files.directory.active = ⟨before.files.directory.active.manifest, some markerBytes⟩ := rfl
  obtain ⟨target, selects, next⟩ := ready.advanceSettled (written := written) prepared fits
    ⟨by rw [pair, marker], rfl, contents, rfl⟩
  refine ⟨target, ?_, selects.2.1, ?_, next⟩
  · rw [selects.1, pair, ready.resumed.ready.selected]
  · change WAL.encode ((before.history ++ batch).drop before.wal.active.first) = _
    rw [← ready.active, ← ready.resumed.keeper]
    exact actual

/-- A successful publication leaves the exact table and a single selected
keeper, including when collection has removed earlier sealed files. -/
theorem SegmentedBatchAppendReport.preservesRetained {directory descriptor before}
    (report : SegmentedBatchAppendReport directory before)
    (ready : before.RetainedReady directory descriptor) :
    ∃ target, report.Selects target ∧ (report.next target).RetainedReady directory descriptor := by
  have starts := retainedAppendStart ready
  have measured : report.nextInstalled.walBytes = (WAL.encode (before.history ++ report.batch)).size := by
    simp [SegmentedBatchAppendReport.nextInstalled, ready.resumed.bytes, WAL.encode_size, List.length_append, Nat.mul_add,
      (prepareBatch_spec report.prepared).1]
  have settled := report.reports.settled_of_success measured starts report.committed before.files.directory.active.manifest
  rw [← measured] at settled
  exact ready.advanceSettled report.prepared report.fits settled

end Alvoki.Storage.DiskSession
