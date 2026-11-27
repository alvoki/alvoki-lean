import Alvoki.Storage.Disk.Proofs.WAL.MaintainedDirectoryWork
import Alvoki.Storage.Disk.NativeRotatedMaintenanceBound
import Alvoki.Storage.Disk.Proofs.WAL.WalReplayWork

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair
open WAL (frameSize)
open Compaction.Model (retentionRowBound)

variable {input : FilePath} {directory : DiskDirectory} {descriptor : Nat} {before : SegmentedWriterState}
  {layout : CanonicalKeeperLayout (SegmentedCleanReopenReport.released directory before).image before.history}

/-- The marker and selected WAL callbacks of this held open supply an
empty keeper. The counters follow the same marked decoder and replay. -/
def CheckpointHeldOpen.EmptyWalWork
    (opened : CheckpointHeldOpen input directory layout before.published) : Prop :=
  let image := (SegmentedCleanReopenReport.released directory before).image
  let reported := opened.wal.operations.reported
  let files := [(layout.keeper.first, ByteArray.empty)]
  ∃ marker count,
    reported.inventory.reports.readOptional (directory.file .walBoundary) = .ok (some marker) ∧
    WAL.Boundary.decode marker = .ok count ∧
    (readSelectedWithCachedExtents (m := EStateM IO.Error FileImage) directory layout.range.watermark count
      (fun path => liftExcept (reported.list path))
      (fun path => liftExcept (.ok (reported.inventory.reports.lstat path) : Except IO.Error _))
      (fun path size => liftExcept (reported.readSeal path size))
      (fun path size physical => liftExcept (reported.readKeeper path size physical))) image =
      .ok (⟨files, []⟩, 0) image ∧
    markedWalDecodeWork count files = ⟨0, 0⟩ ∧
    (recoverMarkedWalSegmentsWithReplayWork (before.checkpoint.getD (.empty, 0)).1 count files).2 = 0

/-- A full checkpoint and an empty prior keeper yield one empty payload
from the admitted open's actual cached reader, with no frame decoding
or replay attempts. The keeper is still opened and checked. -/
theorem AdmittedCleanReopen.emptyWalWork
    {closed : CleanUnlockReports directory descriptor}
    {opened : CheckpointHeldOpen input directory layout before.published} {after : SegmentedWriterState}
    (endpoint : AdmittedCleanReopen closed opened.chunkReports opened.admission after)
    (ready : before.RetainedReady directory descriptor)
    (full : before.target.range.watermark = before.history.length)
    (empty : before.wal.active = ⟨before.history.length, before.history.length, ByteArray.empty⟩) :
    opened.EmptyWalWork := by
  let image := (SegmentedCleanReopenReport.released directory before).image
  obtain ⟨range, noSeals, _⟩ := endpoint.selectedKeeperAfterFullCheckpoint ready full
  have keeper := endpoint.writer.keeper.trans empty
  have later : (SegmentedCleanReopenReport.released directory before).image.later.visible = [] :=
    ready.resumed.ready.pruned.1
  obtain ⟨watermark, _, marker, count, visible, decoded, absolute⟩ :=
    DirectoryPublication.Bindings.walRange_accounting layout.decoded
  have atThrough : count.toNat / frameSize = layout.range.through := by
    rw [absolute, Nat.mul_div_cancel _ (by decide : 0 < frameSize)]
  have covered : layout.range.watermark = layout.range.through :=
    (congrArg MarkedWalRange.watermark range).trans (full.trans layout.through.symm)
  have selected : SelectedIntegrityCheckpoint before.published.durable image.directory.active.manifest before.checkpoint := by
    change SelectedIntegrityCheckpoint before.published.durable before.files.directory.active.manifest before.checkpoint
    rw [ready.resumed.ready.selected]
    exact ready.resumed.selected
  have clock := Option.some.inj (selected.watermark.symm.trans watermark)
  let reported := opened.wal.operations.reported
  have reads := reported.readSelected (by simp [noSeals]) (by simp [later]) absolute image
  have observedMarker := opened.metadata.callbackMetadata.markerRead.trans (congrArg Except.ok visible)
  let files := [(layout.keeper.first, ByteArray.empty)]
  have decodedWork := (markedWalDecodeWork_spec (before.checkpoint.getD (.empty, 0)).1 count files)
  dsimp only at decodedWork
  have frameBound : (markedWalDecodeWork count files).frames ≤ 0 := by
    simpa [files, atThrough, keeper, layout.through] using decodedWork.2.1
  have ordinalBound := Nat.le_trans decodedWork.1 frameBound
  have counter := (recoverMarkedWalSegmentsWithReplayWork_spec (before.checkpoint.getD (.empty, 0)).1 count files).2.1
  have attempts : (recoverMarkedWalSegmentsWithReplayWork (before.checkpoint.getD (.empty, 0)).1 count files).2 ≤ 0 := by
    simpa only [atThrough, clock, covered, Nat.sub_self] using counter
  refine ⟨marker, count, observedMarker, decoded, ?_, ?_, Nat.eq_zero_of_le_zero attempts⟩
  · simpa [noSeals, keeper, later, endpoint.writer.aligned] using reads
  · cases work : markedWalDecodeWork count files with
    | mk frames ordinals =>
      rw [work] at frameBound ordinalBound
      have exactFrames : frames = 0 := Nat.eq_zero_of_le_zero frameBound
      have exactOrdinals : ordinals = 0 := Nat.eq_zero_of_le_zero ordinalBound
      simp only [exactFrames, exactOrdinals]

/-- The caller schedules a healthy rotation and complete maintenance.
One observed clean handoff gives the selected run read budget, actual
checked directory and inventory counts, and zero WAL decode or replay
work. The call counts use separate units. -/
theorem MaintainedRecoveryBounds.closeAndReopenWorkAfterRotation {start rotated : NativeExecutionPosition}
    (step : NativeExecutionStep start .rotatedWal rotated)
    {maintained : SegmentedWriterState} (bounds : MaintainedRecoveryBounds rotated.ready.state.writer maintained)
    (positive : start.ready.state.writer.wal.PositiveSeals)
    (ready : maintained.RetainedReady directory descriptor) (closed : CleanUnlockReports directory descriptor)
    {catalog : List RunAddress} (unique : catalog.Nodup)
    (covered : ∀ generation index bytes, maintained.published.durable generation index = some bytes →
      (generation, index) ∈ catalog)
    {managedRunCap unmanagedCap : Nat}
    (runs : maintained.published.durable.namedRunTotal (fun _ => 1) catalog ≤ managedRunCap)
    (observed : closed.HeldReopenObservations (before := maintained) input (fun opened =>
      opened.ManagedDirectoryNames maintained.wal ∧ opened.held.listing.scan.unmanagedNameCount ≤ unmanagedCap)) :
    ∃ (layout : CanonicalKeeperLayout (SegmentedCleanReopenReport.released directory maintained).image maintained.history)
      (opened : CheckpointHeldOpen input directory layout maintained.published) (after : SegmentedWriterState),
      AdmittedCleanReopen closed opened.chunkReports opened.admission after ∧
      opened.DirectoryWorkBound catalog managedRunCap unmanagedCap ∧
      opened.preparationRequests ≤ 16 * rotated.ready.state.writer.installed.table.runs.length +
        32 * (rotated.ready.state.writer.installed.table.runs.map (fun run =>
          retentionRowBound run.history.rows rotated.ready.state.writer.installed.table.pins.floor)).sum ∧
      opened.EmptyWalWork := by
  obtain ⟨keeper, sealed⟩ := step.rotatedWalKeeper
  have active := bounds.keeper.trans keeper
  have endAt : maintained.history.length = rotated.history.length :=
    ready.layout.activeEnd.symm.trans (congrArg WalSegment.last active)
  rw [← endAt] at active
  obtain ⟨layout, opened, after, endpoint, names, unmanaged⟩ :=
    ready.closeWithHeldEvidence closed _ observed
  have directoryWork := opened.maintainedDirectoryWork names (bounds.singleSegment (sealed positive)) unique covered
    runs unmanaged
  have selected := endpoint.preparationRequests_le ready bounds.fullCheckpoint
  rw [active] at selected
  exact ⟨layout, opened, after, endpoint, directoryWork,
    Nat.le_trans (by simpa using selected) bounds.selectedRuns, endpoint.emptyWalWork ready bounds.fullCheckpoint active⟩

end Alvoki.Storage.DiskSession
