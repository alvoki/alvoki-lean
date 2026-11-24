import Alvoki.Storage.Disk.WalBatchCommitReports
import Alvoki.Storage.Disk.RetainedWriterState

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WalSegmentCommit WAL.Boundary

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
