import Alvoki.Storage.Disk.SegmentedWriterState

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WalSegmentCommit WAL.Boundary
open WAL (frameSize)

/-- A reached successful append schedule after the active file guard.
The file operations are the shared append, staged write, sync and rename
callbacks. Their reports classify the physical effects at reached states. -/
structure SegmentedAppendReport (directory : DiskDirectory) (before : SegmentedWriterState) where
  event : WAL.Write
  table : PackedTable
  effects : WriteEffects
  append : FilePath → ByteArray → EStateM IO.Error WriteFiles Unit
  write : FilePath → ByteArray → EStateM IO.Error WriteFiles Unit
  sync : Array FilePath → EStateM IO.Error WriteFiles Unit
  rename : FilePath → FilePath → EStateM IO.Error WriteFiles Unit
  written : WriteFiles
  prepared : prepareWrite before.installed.table event.key event.value = some (event, table)
  fits : before.installed.walBytes + frameSize < UInt64.size
  reports : AppendCommitReports directory before.installed.activeFirst before.history event
    (before.installed.walBytes + frameSize) effects (before.files.directory.staged .walBoundary) append write sync rename
  committed : commitAt directory before.installed.activeFirst event (before.installed.walBytes + frameSize)
    append write sync rename (WriteFiles.initial before.history (before.files.directory.staged .walBoundary)) = .ok () written

def SegmentedAppendReport.files {directory before} (report : SegmentedAppendReport directory before) : FileImage :=
  resumedAppendFiles before.files before.history before.installed.activeFirst report.written

def SegmentedAppendReport.nextInstalled {directory before} (report : SegmentedAppendReport directory before) : Installed :=
  { before.installed with table := report.table, walBytes := before.installed.walBytes + frameSize }

def SegmentedAppendReport.next {directory before} (report : SegmentedAppendReport directory before)
    (target : Target) : SegmentedWriterState :=
  let history := before.history ++ [report.event]
  let wal := before.wal.appendSelectedView report.files.directory.active history
  SegmentedWriterState.ofReopen report.nextInstalled wal history before.published target before.checkpoint
    ⟨report.files, before.owners⟩

/-- The submission and the old state identify the unique next target. -/
def SegmentedAppendReport.Selects {directory before} (report : SegmentedAppendReport directory before)
    (target : Target) : Prop :=
  target.pair = ⟨before.target.pair.manifest, some (WAL.Boundary.encode report.nextInstalled.walBytes.toUInt64)⟩ ∧
  target.range = ⟨before.target.range.watermark, (before.history ++ [report.event]).length⟩ ∧
    target.first = before.installed.activeFirst ∧
    target.trimmed = WAL.encode ((before.history ++ [report.event]).drop before.installed.activeFirst)

private theorem sameSelectedTarget {left right : Target}
    (pair : left.pair = right.pair) (range : left.range = right.range) (start : left.first = right.first)
    (bytes : left.trimmed = right.trimmed) : left = right := by
  cases left
  cases right
  cases pair
  cases range
  cases start
  cases bytes
  rfl

theorem SegmentedAppendReport.selectsUnique {directory before} (report : SegmentedAppendReport directory before)
    {left right : Target} (a : report.Selects left) (b : report.Selects right) : left = right := by
  exact sameSelectedTarget (a.1.trans b.1.symm) (a.2.1.trans b.2.1.symm)
    (a.2.2.1.trans b.2.2.1.symm) (a.2.2.2.trans b.2.2.2.symm)

/-- The successful native publication tail returns the submitted sequence
and records the exact next phase and file effects under the original lock. -/
theorem SegmentedAppendReport.acknowledges {directory before} (report : SegmentedAppendReport directory before) :
    let commit := commitAt directory before.installed.activeFirst report.event report.nextInstalled.walBytes
      report.append report.write report.sync report.rename
    let initial := WriteFiles.initial before.history (before.files.directory.staged .walBoundary)
    runPreparedWrite report.nextInstalled report.event.sequence commit (.ready before.installed, ⟨initial, before.owners⟩) =
      .ok report.event.sequence (.ready report.nextInstalled, ⟨report.written, before.owners⟩) :=
  runPreparedWrite_success before.installed report.nextInstalled report.event.sequence report.committed

theorem SegmentedAppendReport.selectedReady {directory descriptor before}
    (report : SegmentedAppendReport directory before) (ready : before.Ready directory descriptor) :
    report.event.sequence.toNat = before.history.length + 1 ∧
    ∃ target, report.Selects target ∧
      ResumedAppendReady report.nextInstalled report.files target (before.history ++ [report.event])
        before.published before.checkpoint := by
  obtain ⟨_, ordinal, target, pair, range, nextReady⟩ := ready.resumed.acknowledged directory report.prepared
    report.fits report.effects report.append report.write report.sync report.rename report.reports report.committed
  exact ⟨ordinal, target, ⟨pair, range, nextReady.keeper.symm, nextReady.contents.trans
    (congrArg (fun first => WAL.encode ((before.history ++ [report.event]).drop first)) nextReady.keeper.symm)⟩, nextReady⟩

theorem SegmentedAppendReport.preservesReady {directory descriptor before}
    (report : SegmentedAppendReport directory before) (ready : before.Ready directory descriptor)
    {target : Target} (selected : report.Selects target) : (report.next target).Ready directory descriptor := by
  obtain ⟨_, chosen, chosenBy, resumed⟩ := report.selectedReady ready
  have same := report.selectsUnique chosenBy selected
  subst chosen
  obtain ⟨layout, chain, _, _⟩ := ready.layout.afterAcknowledgedAppend ready.chain report.files.directory.active report.event
  refine ⟨⟨resumed.ready, resumed.through, resumed.keeper, resumed.bytes, resumed.contents, resumed.generation,
      resumed.selected, resumed.accepted, resumed.ordered, resumed.bounds, resumed.canonical⟩,
    ⟨layout.ordered, layout.forward, layout.activeEnd, layout.activeBytes⟩, chain, rfl, ?_, ?_, rfl, ready.held⟩
  · exact ready.sealedFiles
  · exact resumed.keeper.symm.trans (ready.resumed.keeper.trans ready.active)

/-- A finite sequence of reported native append acknowledgments threads
the exact produced image and installed state into the next write. -/
inductive SegmentedAppendTrace (directory : DiskDirectory) (descriptor : Nat) (initial : SegmentedWriterState) :
    List WAL.Write → SegmentedWriterState → Prop where
  | empty : SegmentedAppendTrace directory descriptor initial [] initial
  | append {events before target} (prior : SegmentedAppendTrace directory descriptor initial events before)
      (report : SegmentedAppendReport directory before) (selected : report.Selects target) :
      SegmentedAppendTrace directory descriptor initial (events ++ [report.event]) (report.next target)

theorem SegmentedAppendTrace.preservesReady {directory descriptor initial events last}
    (trace : SegmentedAppendTrace directory descriptor initial events last)
    (ready : initial.Ready directory descriptor) :
    last.Ready directory descriptor ∧ last.history = initial.history ++ events ∧
      last.owners = initial.owners ∧ last.published.durable = initial.published.durable ∧
      last.installed.generation = initial.installed.generation := by
  induction trace with
  | empty => exact ⟨ready, by simp, rfl, rfl, rfl⟩
  | append _ report selected ih =>
    obtain ⟨valid, history, owners, checkpoints, generation⟩ := ih
    exact ⟨report.preservesReady valid selected, by
      change _ ++ [report.event] = _
      rw [history, List.append_assoc], owners, checkpoints, generation⟩

end Alvoki.Storage.DiskSession
