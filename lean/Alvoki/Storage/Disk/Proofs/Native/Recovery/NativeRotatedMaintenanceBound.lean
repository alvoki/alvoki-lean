import Alvoki.Storage.Disk.Proofs.Native.Execution.NativeExecutionTrace
import Alvoki.Storage.Disk.Proofs.Session.MaintainedRecoveryWork

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open Compaction.Model (retentionRowBound)

/-- A successful public rotation leaves an empty keeper at the end of
the acknowledged history. The no-op branch already had such a keeper.
Any old positive seal stays positive, and a new seal is nonempty. -/
theorem NativeExecutionStep.rotatedWalKeeper {before rotated : NativeExecutionPosition}
    (step : NativeExecutionStep before .rotatedWal rotated) :
    rotated.ready.state.writer.wal.active = ⟨rotated.history.length, rotated.history.length, ByteArray.empty⟩ ∧
    (before.ready.state.writer.wal.PositiveSeals → rotated.ready.state.writer.wal.PositiveSeals) := by
  cases step with
  | rotateCreated _ report next returned =>
    refine ⟨returned.frame.keeper, ?_⟩
    intro positive segment present
    rw [returned.frame.sealed] at present
    exact (positive.rotated (before.ready.readPrefix.refines.1.retained.rotationInput report.parent.nonempty).nonempty)
      segment present
  | rotateExisting _ report next returned =>
    refine ⟨returned.frame.keeper, ?_⟩
    intro positive segment present
    rw [returned.frame.sealed] at present
    exact (positive.rotated (before.ready.readPrefix.refines.1.retained.rotationInput report.opened.nonempty).nonempty)
      segment present
  | rotateEmpty _ returned =>
    -- A failing lookup distinguishes the guard-skipping return.
    obtain ⟨valid, history, _⟩ := before.ready.readPrefix.refines
    let refused := IO.userError "active WAL metadata unavailable"
    have unchanged := returned () (fun _ => .error refused) (fun _ => pure none)
      (fun _ => pure ()) (fun _ => pure ()) (fun _ _ => ())
    dsimp only at unchanged
    rw [valid.phase] at unchanged
    have empty : before.ready.state.writer.installed.walBytes / WAL.frameSize ≤
        before.ready.state.writer.installed.activeFirst := by
      by_cases nonempty : before.ready.state.writer.installed.activeFirst <
          before.ready.state.writer.installed.walBytes / WAL.frameSize
      · simp [runObservedRotationWithReset, rotateWalSchedule, Phase.installed, nonempty,
          checkActiveSegmentWith, liftExcept, Bind.bind, EStateM.bind, Pure.pure, Except.pure] at unchanged
        change EStateM.Result.error refused _ = .ok () _ at unchanged
        contradiction
      · exact Nat.le_of_not_gt nonempty
    let ready := valid.retained
    have activeFirst : before.ready.state.writer.wal.active.first = before.ready.state.writer.installed.activeFirst :=
      ready.active.symm.trans ready.resumed.keeper.symm
    have ends : before.ready.state.writer.wal.active.last = before.history.length :=
      ready.layout.activeEnd.trans (congrArg List.length history)
    have endAt : before.ready.state.writer.installed.walBytes / WAL.frameSize = before.history.length :=
      ready.rotationAtEnd.trans (congrArg List.length history)
    have startsAtEnd : before.ready.state.writer.wal.active.first = before.history.length := by
      rw [endAt, ← activeFirst] at empty
      exact Nat.le_antisymm (ends ▸ ready.layout.forward _ (List.mem_append_right _ (by simp))) empty
    have bytes : before.ready.state.writer.wal.active.bytes = ByteArray.empty := by
      rw [ready.layout.activeBytes, startsAtEnd, history, List.drop_length]
      rfl
    refine ⟨?_, id⟩
    generalize before.ready.state.writer.wal.active = keeper at startsAtEnd ends bytes ⊢
    cases keeper
    exact WalSegment.mk.injEq _ _ _ _ _ _ |>.mpr ⟨startsAtEnd, ends, bytes⟩

/-- With a caller-scheduled successful rotation immediately before the
maintenance cycle, a completed checkpoint and both collectors leave
just the empty keeper under the canonical WAL names. Old seals are
positive on the reachable path from bootstrap. -/
theorem MaintainedRecoveryBounds.afterScheduledRotation {before rotated : NativeExecutionPosition}
    (step : NativeExecutionStep before .rotatedWal rotated)
    {maintained : SegmentedWriterState} (bounds : MaintainedRecoveryBounds rotated.ready.state.writer maintained)
    (positive : before.ready.state.writer.wal.PositiveSeals) :
    maintained.wal.segments = [⟨rotated.history.length, rotated.history.length, ByteArray.empty⟩] ∧
    WalSegment.concatenate maintained.wal.segments = ByteArray.empty ∧
    ∀ {directory owners descriptor readerDescriptor tail}, maintained.RetainedReady directory descriptor →
      ∀ (observed : HealthyBoundedWalReports directory owners readerDescriptor maintained.wal maintained.target.pair
        maintained.target.range.watermark maintained.published.durable tail),
      (observed.entries.toList.map (·.fileName)).filterMap parseWalSegmentName = [rotated.history.length] := by
  obtain ⟨keeper, seals⟩ := step.rotatedWalKeeper
  have names := (bounds.singleSegment (seals positive)).trans (congrArg (fun segment => [segment]) (bounds.keeper.trans keeper))
  refine ⟨names, by simp [names, WalSegment.concatenate], ?_⟩
  intro directory owners descriptor readerDescriptor tail ready observed
  have listed := observed.canonicalWalNames ready.layout
  rw [names, List.map_cons, List.map_nil] at listed
  exact listed.eq_singleton

/-- After that scheduled rotation and completed maintenance, the next
held reopen needs at most the retained checkpoint's preparation bytes.
The reported healthy open and stable handoff remain required. -/
theorem MaintainedRecoveryBounds.closeAndReopenAfterRotation {before rotated : NativeExecutionPosition}
    (step : NativeExecutionStep before .rotatedWal rotated)
    {directory descriptor input} {maintained : SegmentedWriterState}
    (bounds : MaintainedRecoveryBounds rotated.ready.state.writer maintained)
    (ready : maintained.RetainedReady directory descriptor) (closed : CleanUnlockReports directory descriptor)
    (observed : closed.HeldReopenObservations (before := maintained) input) :
    ∃ (layout : CanonicalKeeperLayout (SegmentedCleanReopenReport.released directory maintained).image maintained.history)
      (opened : CheckpointHeldOpen input directory layout maintained.published)
      (after : SegmentedWriterState) (session : SegmentedSession) (final : LockedFileState FileImage),
      AdmittedCleanReopen closed opened.chunkReports opened.admission after ∧
      opened.wal.operations.runWithAdmission opened.admission = .ok session final ∧
      session.descriptor = opened.calls.slot.description ∧ session.phase = .ready after.installed ∧
      after.files = final.image ∧ after.owners = final.owners ∧
      opened.preparationRequests ≤ 16 * rotated.ready.state.writer.installed.table.runs.length +
        32 * (rotated.ready.state.writer.installed.table.runs.map (fun run =>
          retentionRowBound run.history.rows rotated.ready.state.writer.installed.table.pins.floor)).sum := by
  have width : rotated.ready.state.writer.wal.active.last - rotated.ready.state.writer.wal.active.first ≤ 0 := by
    simp [step.rotatedWalKeeper.1]
  simpa only [Nat.zero_mul, Nat.add_zero] using bounds.closeAndReopen ready closed observed width

end Alvoki.Storage.DiskSession
