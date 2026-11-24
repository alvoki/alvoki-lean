import Alvoki.Storage.Disk.SegmentedBatchPowerLoss

namespace Alvoki.Storage.DiskSession.SegmentedBatchMarkerPowerLossReport

open System WalSegmentCommit WalSegmentRepair WAL.Boundary

variable {directory : DiskDirectory} {before : SegmentedWriterState} {writer : Nat}

/-- The observed process-table exit step preserves the live marker cut,
including pending scratch and keeper crash choices. Later file effects
need their own observations. Under the complete reference census a
surviving alias excludes a successful cooperating acquisition. The
visible marker selects the old history or the complete batch over the
unchanged checkpoint binding. -/
theorem Reached.processExit {report : SegmentedBatchMarkerPowerLossReport directory before writer}
    (observed : report.Reached) (ready : before.RetainedReady directory writer)
    (references : HeldLockReferences writer) (process : Nat) :
    let exited := references.afterFileDrops [.exited process] directory report.inFlight
    BoundedReopenTrace directory (BatchRetryTarget before.history report.batch before.wal.active.first)
      report.inFlight exited ∧
    exited.image = report.physical ∧
    (TryLockObserves exited.owners directory (.ok true) ↔ references.remaining [.exited process] = []) ∧
    ∃ history bytes, (history = before.history ∨ history = before.history ++ report.batch) ∧
      exited.image.directory.active.manifest = before.wal.directory.active.manifest ∧
      exited.image.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64) ∧
      exited.image.keeper.active = some bytes ∧
      selectRetained before.wal.active.first (WAL.encode history).size.toUInt64 bytes =
        .ok (WAL.encode (history.drop before.wal.active.first)) := by
  intro exited
  have held : report.inFlight.owners.Owns directory writer := ready.held
  have admission := references.afterFileDrops_admits (drops := [.exited process]) held
  let scratch := before.wal.directory.staged .walBoundary
  let effects := report.cut.writeEffects report.appendCrashTails scratch
  let modeled := (writeFilesAfter (runBatchEffects before.history report.batch effects scratch)).reopenSegment
    before.wal.active.first before.history before.wal.directory.active.manifest
  let marker := WAL.Boundary.encode (WAL.encode (before.history ++ report.batch)).size.toUInt64
  let tail := (report.cut.interrupt marker report.reached).visibleTail
  let bytes := WAL.encode (before.history.drop before.wal.active.first) ++ tail
  have visibleBytes : report.physical.keeper.active = some bytes := rfl
  obtain ⟨sameTail, _, sameMarker, _⟩ :=
    report.cut.matchesBatchEffects before.history report.batch report.appendCrashTails scratch
  have pair : report.physical.directory.active = modeled.directory.active :=
    congrArg (DirectoryPublication.Bindings.mk before.wal.directory.active.manifest) sameMarker
  have keeper : some bytes = modeled.wal.active :=
    congrArg (fun tail => some (WAL.encode (before.history.drop before.wal.active.first) ++ tail)) sameTail
  have starts : before.wal.active.first ≤ before.history.length := by
    rw [← ready.layout.activeEnd]
    exact ready.layout.forward before.wal.active (List.mem_append_right _ (by simp))
  obtain ⟨history, whole, manifest, boundary, selected⟩ :=
    selectSegment_atReportedBatchCut starts (observed.preparedHistory ready).2.1 effects
      before.wal.directory.active.manifest scratch report.physical.directory.active bytes
      (pair.symm ▸ List.mem_cons_self ..) (keeper.symm ▸ List.mem_cons_self ..)
  exact ⟨.referenceDrops .empty references [.exited process], rfl, admission, history, bytes, whole,
    manifest, boundary, visibleBytes, selected⟩

end Alvoki.Storage.DiskSession.SegmentedBatchMarkerPowerLossReport
