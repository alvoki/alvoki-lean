import Alvoki.Storage.Disk.Proofs.Append.SegmentedBatchAppendPowerLoss
import Alvoki.Storage.Disk.Proofs.Append.WalBatchAppendProcessExit

namespace Alvoki.Storage.DiskSession

open WalSegmentRepair

/-- An observed writer-process exit during batch append. The next retry
starts from the live image and the observed reference drops. -/
structure SegmentedBatchAppendProcessExitReport (directory : DiskDirectory) (before : SegmentedWriterState)
    (writer descriptor : Nat) where
  process : Nat
  references : HeldLockReferences writer
  reopen : SegmentedBatchAppendReopenReport directory before descriptor fun cut =>
    references.afterFileDrops [.exited process] directory ⟨cut.physical before, before.owners⟩

/-- Continuing from the actual live image and lock ownership, the cached
opener repairs the old keeper and installs the pre-batch history. A retry
can cross further observed drops if an inherited lock reference survives. -/
theorem SegmentedBatchAppendProcessExitReport.installs {directory before writer descriptor}
    (report : SegmentedBatchAppendProcessExitReport directory before writer descriptor)
    (observed : report.reopen.Valid) (ready : before.RetainedReady directory writer) :
    ∃ after, report.reopen.Installs after := by
  have release := report.reopen.cut.batchProcessExit ready report.reopen.batch report.references report.process
  obtain ⟨fixed, emptyLater, source, target, keeper, _, descriptors, offsets, prepared⟩ :=
    report.reopen.cut.liveLayout ready
  exact report.reopen.installsFromFixedAuthority observed ready release.1 source target keeper descriptors offsets
    prepared fixed emptyLater rfl

end Alvoki.Storage.DiskSession
