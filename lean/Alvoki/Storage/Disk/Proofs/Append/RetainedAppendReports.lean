import Alvoki.Storage.Disk.Proofs.Append.SegmentedAppendTrace
import Alvoki.Storage.Disk.RetainedWriterState

namespace Alvoki.Storage.DiskSession

open WalSegmentRepair

/-- A successful shared append schedule threads the actual file image and
installed table through the retained WAL invariant. The earlier sealed
files can have gaps strictly before the selected read suffix. -/
theorem SegmentedAppendReport.preservesRetained {directory descriptor before}
    (report : SegmentedAppendReport directory before)
    (ready : before.RetainedReady directory descriptor) :
    report.event.sequence.toNat = before.history.length + 1 ∧ ∃ target, report.Selects target ∧
      let after := report.next target
      after.RetainedReady directory descriptor ∧
      after.wal.sealed = before.wal.sealed ∧
      after.wal.active.bytes = before.wal.active.bytes ++ WAL.encodeFrame report.event ∧
      after.files.keeper.active = some after.wal.active.bytes ∧
      after.files.keeper.crashImages = [some after.wal.active.bytes] := by
  obtain ⟨_, ordinal, target, pair, range, resumed⟩ :=
    ready.resumed.acknowledged directory report.prepared report.fits report.effects
      report.append report.write report.sync report.rename report.reports report.committed
  have oldRange : before.wal.directory.active.walRange = some ⟨before.target.range.watermark, before.history.length⟩ := by
    rw [ready.walPair, ← ready.resumed.through]
    exact before.target.decoded
  have visible : report.files.directory.active = target.pair := resumed.ready.selected
  have settled : report.files.directory.crashImages = [report.files.directory.active] :=
    resumed.ready.settled.trans (congrArg (fun pair => [pair]) visible.symm)
  have newRange : report.files.directory.active.walRange =
      some ⟨before.target.range.watermark, (before.history ++ [report.event]).length⟩ := by
    rw [visible, ← range]
    exact target.decoded
  obtain ⟨nextLayout, nextValid, sameSeals, nextActive⟩ :=
    ready.layout.afterRetainedAppend ready.valid oldRange report.files.directory.active report.event newRange
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
  have first : target.first = after.wal.active.first :=
    resumed.keeper.symm.trans (ready.resumed.keeper.trans ready.active)
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
  have seals : after.wal.sealed = before.wal.sealed := sameSeals
  have spans : ∀ segment ∈ after.wal.sealed, segment.bytes.size = (segment.last - segment.first) * WAL.frameSize := by
    rw [seals]
    exact ready.spans
  exact ⟨ordinal, target, selected,
    ⟨nextReady, retainedLayout, retainedValid, spans, rfl, ready.sealedFiles, first, rfl, ready.held⟩,
    seals, congrArg WalSegment.bytes nextActive,
    resumed.ready.keeper.trans (congrArg some bytes),
    resumed.ready.keeperDurable.trans (congrArg (fun payload => [some payload]) bytes)⟩

/-- Append acknowledgments preserve the retained layout and the session.
If the original inventory contains the full WAL chain, the result does too. -/
theorem SegmentedAppendTrace.preservesRetainedWithChain {directory descriptor initial events last}
    (trace : SegmentedAppendTrace directory descriptor initial events last)
    (initialReady : initial.RetainedReady directory descriptor) :
    last.RetainedReady directory descriptor ∧ last.history = initial.history ++ events ∧
      last.owners = initial.owners ∧ last.installed.generation = initial.installed.generation ∧
      (WalSegment.Chain initial.history 0 initial.wal.segments →
        WalSegment.Chain last.history 0 last.wal.segments) := by
  induction trace with
  | empty => exact ⟨initialReady, by simp, rfl, rfl, id⟩
  | append _ report selected ih =>
    obtain ⟨ready, history, owners, generation, chain⟩ := ih
    obtain ⟨_, target, chosen, next, _⟩ := report.preservesRetained ready
    cases report.selectsUnique chosen selected
    refine ⟨next, ?_, owners, generation, ?_⟩
    · change _ ++ [report.event] = _
      rw [history, List.append_assoc]
    · intro initialChain
      exact (ready.layout.afterAcknowledgedAppend (chain initialChain) report.files.directory.active report.event).2.1

/-- Continue with the existing append trace from a retained writer. All
acknowledgments in the trace extend the history and preserve readiness. -/
theorem SegmentedAppendTrace.preservesRetained {directory descriptor initial events last}
    (trace : SegmentedAppendTrace directory descriptor initial events last)
    (initialReady : initial.RetainedReady directory descriptor) :
    last.RetainedReady directory descriptor ∧ last.history = initial.history ++ events := by
  obtain ⟨ready, history, _, _, _⟩ := trace.preservesRetainedWithChain initialReady
  exact ⟨ready, history⟩

end Alvoki.Storage.DiskSession
