import Alvoki.Storage.Disk.SegmentedAppendTrace

namespace Alvoki.Storage.DiskSession

open WalSegmentRepair

/-- A successful shared append schedule threads the actual file image and
installed table through the retained WAL invariant. The earlier sealed
files can have gaps strictly before the selected read suffix. -/
theorem SegmentedAppendReport.preservesRetained {directory descriptor before}
    (report : SegmentedAppendReport directory before)
    (ready : ResumedAppendReady before.installed before.files before.target before.history
      before.published before.checkpoint)
    (layout : before.wal.ReadLayout before.history) (valid : before.wal.Valid before.history)
    (directoryFiles : before.files.directory = before.wal.directory)
    (sealedFiles : before.files.kept = (before.wal.checkpointReopenFiles before.wal.directory none).kept)
    (active : before.target.first = before.wal.active.first)
    (held : before.owners.Owns directory descriptor) :
    report.event.sequence.toNat = before.history.length + 1 ∧ ∃ target, report.Selects target ∧
      let after := report.next target
      ResumedAppendReady after.installed after.files after.target after.history after.published after.checkpoint ∧
      after.wal.ReadLayout after.history ∧ after.wal.Valid after.history ∧
      after.files.directory = after.wal.directory ∧
      after.files.kept = (after.wal.checkpointReopenFiles after.wal.directory none).kept ∧
      after.target.first = after.wal.active.first ∧ after.owners.Owns directory descriptor ∧
      after.wal.sealed = before.wal.sealed ∧
      after.wal.active.bytes = before.wal.active.bytes ++ WAL.encodeFrame report.event ∧
      after.files.keeper.active = some after.wal.active.bytes ∧
      after.files.keeper.crashImages = [some after.wal.active.bytes] := by
  obtain ⟨_, ordinal, target, pair, range, resumed⟩ :=
    ready.acknowledged directory report.prepared report.fits report.effects
      report.append report.write report.sync report.rename report.reports report.committed
  have oldRange : before.wal.directory.active.walRange = some ⟨before.target.range.watermark, before.history.length⟩ := by
    rw [← directoryFiles, ready.ready.selected, ← ready.through]
    exact before.target.decoded
  have visible : report.files.directory.active = target.pair := resumed.ready.selected
  have settled : report.files.directory.crashImages = [report.files.directory.active] :=
    resumed.ready.settled.trans (congrArg (fun pair => [pair]) visible.symm)
  have newRange : report.files.directory.active.walRange =
      some ⟨before.target.range.watermark, (before.history ++ [report.event]).length⟩ := by
    rw [visible, ← range]
    exact target.decoded
  obtain ⟨nextLayout, nextValid, sameSeals, nextActive⟩ :=
    layout.afterRetainedAppend valid oldRange report.files.directory.active report.event newRange
  let after := report.next target
  have retainedLayout : after.wal.ReadLayout after.history :=
    ⟨nextLayout.ordered, nextLayout.forward, nextLayout.activeEnd, nextLayout.activeBytes⟩
  -- The actual directory also carries staging state. Selection depends on
  -- the same visible pair and singleton crash choice as the settled view.
  have retainedValid : after.wal.Valid after.history := by
    intro candidate chosen
    apply nextValid candidate
    change candidate ∈ report.files.directory.active :: report.files.directory.crashImages at chosen
    change candidate ∈ report.files.directory.active :: [report.files.directory.active]
    rw [settled] at chosen
    exact chosen
  have first : target.first = after.wal.active.first := resumed.keeper.symm.trans (ready.keeper.trans active)
  have bytes : target.trimmed = after.wal.active.bytes := by
    rw [resumed.contents, first, retainedLayout.activeBytes]
    rfl
  have selected : report.Selects target :=
    ⟨pair, range, resumed.keeper.symm, resumed.contents.trans
      (congrArg (fun first => WAL.encode ((before.history ++ [report.event]).drop first)) resumed.keeper.symm)⟩
  have nextReady : ResumedAppendReady after.installed after.files after.target after.history
      after.published after.checkpoint :=
    ⟨resumed.ready, resumed.through, resumed.keeper, resumed.bytes, resumed.contents, resumed.generation,
      resumed.selected, resumed.accepted, resumed.ordered, resumed.bounds, resumed.canonical⟩
  exact ⟨ordinal, target, selected, nextReady, retainedLayout, retainedValid, rfl, sealedFiles, first, held,
    sameSeals, congrArg WalSegment.bytes nextActive,
    resumed.ready.keeper.trans (congrArg some bytes),
    resumed.ready.keeperDurable.trans (congrArg (fun payload => [some payload]) bytes)⟩

end Alvoki.Storage.DiskSession
