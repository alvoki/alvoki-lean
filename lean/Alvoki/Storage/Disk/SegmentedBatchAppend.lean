import Alvoki.Storage.Disk.WalBatchCommitReports
import Alvoki.Storage.Disk.RetainedWriterState
import Alvoki.Storage.Disk.AppendGroupedReports

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

private theorem BatchActiveGuard.checked {image : Type} {directory : DiskDirectory} {installed : Installed}
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

private theorem runBatchWrite_acknowledges {image : Type} {directory : DiskDirectory}
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

/-- Reports project the actual reached append and marker callbacks to the
file effects used by the retained-writer proof. The reached cache is
threaded through all callbacks, including the two consecutive file syncs. -/
structure ObservedBatchWrite {directory before} (report : SegmentedBatchAppendReport directory before)
    (handle : Type) where
  guard : BatchActiveGuard directory before.installed
  cache : Cache handle
  append : FilePath → ByteArray → EStateM IO.Error (Cache handle × WriteFiles) Unit
  stage : FilePath → ByteArray → EStateM IO.Error (Cache handle × WriteFiles) Unit
  sync : Array FilePath → EStateM IO.Error (Cache handle × WriteFiles) Unit
  rename : FilePath → FilePath → EStateM IO.Error (Cache handle × WriteFiles) Unit
  appendProjects :
    let files := WriteFiles.initial before.history (before.files.directory.staged .walBoundary)
    let keeper := directory.file (.walSegment before.installed.activeFirst)
    withoutWriteGroupCache (append keeper (WAL.encodeBatch report.batch) (cache, files)) =
      report.append keeper (WAL.encodeBatch report.batch) files
  markerProjects : ∀ appended : Cache handle × WriteFiles,
    append (directory.file (.walSegment before.installed.activeFirst)) (WAL.encodeBatch report.batch)
      (cache, WriteFiles.initial before.history (before.files.directory.staged .walBoundary)) = .ok () appended →
    ∀ (prior : List Publication.Step) step remaining reached, Publication.steps = prior ++ step :: remaining →
      let native := performMarkerAt directory before.installed.activeFirst report.nextInstalled.walBytes stage sync rename
      (prior.forM native) appended = .ok () reached →
      withoutWriteGroupCache (native step reached) =
        performMarkerAt directory before.installed.activeFirst report.nextInstalled.walBytes
          report.stage report.sync report.rename step reached.2

private theorem markerRun_projects {handle : Type}
    (actual : Publication.Step → EStateM IO.Error (Cache handle × WriteFiles) Unit)
    (projected : Publication.Step → EStateM IO.Error WriteFiles Unit)
    (steps : List Publication.Step) (initial : Cache handle × WriteFiles)
    (agrees : ∀ (prior : List Publication.Step) step remaining reached, steps = prior ++ step :: remaining →
      (prior.forM actual) initial = .ok () reached →
      withoutWriteGroupCache (actual step reached) = projected step reached.2) :
    withoutWriteGroupCache ((steps.forM actual) initial) = (steps.forM projected) initial.2 := by
  induction steps generalizing initial with
  | nil => rfl
  | cons step rest ih =>
    have first := agrees [] step rest initial rfl rfl
    change withoutWriteGroupCache (EStateM.bind (actual step) (fun _ => rest.forM actual) initial) =
      EStateM.bind (projected step) (fun _ => rest.forM projected) initial.2
    unfold EStateM.bind
    rw [← first]
    cases next : actual step initial with
    | error cause reached => rfl
    | ok value after =>
      cases value
      change withoutWriteGroupCache ((rest.forM actual) after) = (rest.forM projected) after.2
      apply ih
      intro prior action remaining reached schedule recorded
      apply agrees (step :: prior) action remaining reached (congrArg (List.cons step) schedule)
      change EStateM.bind (actual step) (fun _ => prior.forM actual) initial = .ok () reached
      simpa only [EStateM.bind, next] using recorded

private theorem ObservedBatchWrite.publisherProjects {handle : Type} {directory before}
    {report : SegmentedBatchAppendReport directory before} (observed : ObservedBatchWrite report handle) :
    let first := before.installed.activeFirst
    let bytes := WAL.encodeBatch report.batch
    let count := report.nextInstalled.walBytes
    let initial := WriteFiles.initial before.history (before.files.directory.staged .walBoundary)
    withoutWriteGroupCache (commitBytesAt directory first bytes count
      observed.append observed.stage observed.sync observed.rename (observed.cache, initial)) =
      commitBytesAt directory first bytes count report.append report.stage report.sync report.rename initial := by
  let initial := WriteFiles.initial before.history (before.files.directory.staged .walBoundary)
  let keeper := directory.file (.walSegment before.installed.activeFirst)
  change withoutWriteGroupCache (EStateM.bind (observed.append keeper (WAL.encodeBatch report.batch)) (fun _ =>
      Publication.run (performMarkerAt directory before.installed.activeFirst report.nextInstalled.walBytes
        observed.stage observed.sync observed.rename)) (observed.cache, initial)) =
    EStateM.bind (report.append keeper (WAL.encodeBatch report.batch)) (fun _ =>
      Publication.run (performMarkerAt directory before.installed.activeFirst report.nextInstalled.walBytes
        report.stage report.sync report.rename)) initial
  unfold EStateM.bind
  rw [← observed.appendProjects]
  cases ran : observed.append keeper (WAL.encodeBatch report.batch) (observed.cache, initial) with
  | error cause reached => rfl
  | ok value appended =>
    cases value
    exact markerRun_projects _ _ _ appended (observed.markerProjects appended ran)

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
  have projected := observed.publisherProjects
  dsimp only at projected
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

def SegmentedBatchAppendReport.next {directory before} (report : SegmentedBatchAppendReport directory before)
    (target : Target) : SegmentedWriterState :=
  let history := before.history ++ report.batch
  let wal := before.wal.appendSelectedView report.files.directory.active history
  SegmentedWriterState.ofReopen report.nextInstalled wal history before.published target before.checkpoint
    ⟨report.files, before.owners⟩

def SegmentedBatchAppendReport.Selects {directory before} (report : SegmentedBatchAppendReport directory before)
    (target : Target) : Prop :=
  target.pair = report.files.directory.active ∧ target.first = before.installed.activeFirst ∧
    target.trimmed = WAL.encode ((before.history ++ report.batch).drop target.first)

/-- A successful publication leaves the exact table and a single selected
keeper, including when collection has removed earlier sealed files. -/
theorem SegmentedBatchAppendReport.preservesRetained {directory descriptor before}
    (report : SegmentedBatchAppendReport directory before)
    (ready : before.RetainedReady directory descriptor) :
    ∃ target, report.Selects target ∧ (report.next target).RetainedReady directory descriptor := by
  let history := before.history ++ report.batch
  let installed := report.nextInstalled
  let bytes := installed.walBytes
  let files := report.files
  let wal := before.wal.appendSelectedView files.directory.active history
  obtain ⟨model, refines, represents⟩ := ready.resumed.canonical
  have clock : before.history.length = before.installed.table.committed.toNat :=
    represents.committed_count.symm.trans (congrArg UInt64.toNat refines.committed).symm
  obtain ⟨_, ordered, _, size⟩ := prepareBatch_extends_history ready.resumed.ordered clock report.prepared
  have count : bytes = (WAL.encode history).size := by
    change before.installed.walBytes + WAL.frameSize * report.rows.length = _
    rw [ready.resumed.bytes, size]
  have starts : before.installed.activeFirst ≤ before.history.length := by
    rw [ready.resumed.keeper, ← ready.resumed.through]
    exact before.target.firstCovered
  have settled := report.reports.settled_of_success count starts report.committed before.files.directory.active.manifest
  rw [← count] at settled
  obtain ⟨target, pair, range, first, contents, filesReady⟩ :=
    resumedAppendTarget ready.resumed.ready ready.resumed.through starts report.batch bytes count report.fits settled
  have replayed := (prepareBatch_spec report.prepared).2.1
  obtain ⟨nextModel, replay, refined⟩ := replay_refines refines replayed
  have historyFits : (WAL.encode history).size < UInt64.size := count ▸ report.fits
  have accepted := before.published.acceptsVersioned_extend_history (suffix := report.batch) ready.resumed.accepted historyFits
  have resumed : ResumedAppendReady installed files target history before.published before.checkpoint := by
    refine ⟨filesReady, congrArg MarkedWalRange.through range, first.symm, count, ?_,
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
    ready.layout.afterRetainedSuffix ready.valid oldRange files.directory.active report.batch newRange
  let after := SegmentedWriterState.ofReopen installed wal history before.published target before.checkpoint
    ⟨files, before.owners⟩
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

end Alvoki.Storage.DiskSession
