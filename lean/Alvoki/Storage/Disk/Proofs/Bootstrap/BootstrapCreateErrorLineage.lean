import Alvoki.Storage.Disk.Proofs.Bootstrap.BootstrapZeroCreateRetry

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

private abbrev BootstrapFiles := LockedFileState WalSegmentRotation.State
private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat

/-- One failed first-create attempt, together with its observed cleanup
and the descriptor events that make the next admission possible. -/
structure ReleasedBootstrapCreateError (directory : DiskDirectory) (before : BootstrapFiles) where
  input : FilePath
  calls : BootstrapOpenCalls (Cache Handle) directory before
  captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls
  listed : BootstrapCheckedListing captured
  error : BootstrapZeroCreateError listed
  cleanup : error.Cleanup
  admission : OpenAdmissionReports input directory calls.slot
  inventory : DescriptorInventory
  retry : BootstrapFiles
  disposed : error.DisposedForRetry inventory retry

namespace ReleasedBootstrapCreateError

variable {directory : DiskDirectory} {before : BootstrapFiles}

theorem returned (attempt : ReleasedBootstrapCreateError directory before) :
    attempt.calls.run attempt.admission = .error attempt.error.diagnostic attempt.error.final ∧
    ∀ continuation, attempt.error.runCleanup attempt.cleanup continuation =
      .error attempt.error.diagnostic (attempt.captured.cache, attempt.listed.scan.afterClose, attempt.error.final) :=
  let observed := attempt.error.returns attempt.cleanup attempt.admission
  ⟨observed.1, observed.2.1⟩

private theorem lockAt (attempt : ReleasedBootstrapCreateError directory before) :
    ∃ lock, attempt.captured.view.child attempt.captured.root "LOCK" = some lock ∧
      attempt.captured.view.modelObject lock = attempt.inventory.inode attempt.calls.slot.description := by
  obtain ⟨lock, bound, identified⟩ := attempt.listed.canonicalLock
  have before := Option.some.inj (attempt.captured.lockObject.symm.trans identified)
  have inodes := attempt.disposed.released.2.1
  rw [attempt.listed.scan.afterClose_eq] at inodes
  exact ⟨lock, bound, before.symm.trans (congrArg (fun inode => inode attempt.calls.slot.description) inodes).symm⟩

private theorem directoryAt (attempt : ReleasedBootstrapCreateError directory before) :
    attempt.captured.view.modelObject attempt.captured.root =
      attempt.inventory.inode attempt.captured.cached.description := by
  have inodes := attempt.disposed.released.2.1
  rw [attempt.listed.scan.afterClose_eq] at inodes
  exact attempt.captured.captures.2.2.2.2.trans
    (congrArg (fun inode => inode attempt.captured.cached.description) inodes).symm

end ReleasedBootstrapCreateError

/-- A sequence of failed first-create calls before the first installed
session. Every subsequent call starts with the previous disposition's
exact files and descriptor inventory. It recaptures the stable root and
LOCK and checks the markerless route under its new owner. -/
inductive BootstrapCreateErrorLineage {directory : DiskDirectory} {before : BootstrapFiles}
    (first : ReleasedBootstrapCreateError directory before) :
    List ((atFiles : BootstrapFiles) × ReleasedBootstrapCreateError directory atFiles) →
    {atFiles : BootstrapFiles} → ReleasedBootstrapCreateError directory atFiles → Prop where
  | start : BootstrapCreateErrorLineage first [⟨before, first⟩] first
  | append {attempts : List ((atFiles : BootstrapFiles) × ReleasedBootstrapCreateError directory atFiles)}
      {atFiles : BootstrapFiles} {previous : ReleasedBootstrapCreateError directory atFiles}
      (earlier : BootstrapCreateErrorLineage first attempts previous)
      (next : ReleasedBootstrapCreateError directory previous.retry)
      (acquired : CapturedBootstrapAdmission next.captured next.admission previous.inventory)
      (view : next.captured.view = previous.error.afterView)
      (root : next.captured.root = previous.captured.root) :
      BootstrapCreateErrorLineage first (attempts ++ [⟨previous.retry, next⟩]) next

variable {directory : DiskDirectory} {before atFiles : BootstrapFiles}
  {first : ReleasedBootstrapCreateError directory before} {last : ReleasedBootstrapCreateError directory atFiles}

/-- The recorded requests and diagnostics are exactly the attempts'
returns, including the unlock error when cleanup takes precedence. -/
theorem BootstrapCreateErrorLineage.returns
    (reported : BootstrapCreateErrorLineage first attempts last) :
    ∀ receipt ∈ attempts,
      receipt.2.calls.run receipt.2.admission = .error receipt.2.error.diagnostic receipt.2.error.final ∧
      ∀ continuation, receipt.2.error.runCleanup receipt.2.cleanup continuation =
        .error receipt.2.error.diagnostic (receipt.2.captured.cache, receipt.2.listed.scan.afterClose, receipt.2.error.final) := by
  induction reported with
  | start =>
    intro receipt included
    obtain rfl := List.mem_singleton.mp included
    exact first.returned
  | append _ next _ _ _ previous =>
    intro receipt included
    rcases List.mem_append.mp included with earlier | final
    · exact previous receipt earlier
    · obtain rfl := List.mem_singleton.mp final
      exact next.returned

/-- Every later admission uses the same vacant empty image and the same
physical directory and lock objects. No keeper or marker was installed. -/
theorem BootstrapCreateErrorLineage.frames (reported : BootstrapCreateErrorLineage first attempts last) :
    last.retry.image = before.image ∧ TryLockObserves last.retry.owners directory (.ok true) ∧
    last.captured.view = first.captured.view ∧ last.captured.root = first.captured.root ∧
    last.inventory.inode last.calls.slot.description = first.inventory.inode first.calls.slot.description ∧
    last.inventory.inode last.captured.cached.description = first.inventory.inode first.captured.cached.description ∧
    last.error.afterView.child last.captured.root (renderWalSegmentName 0) = none ∧
    last.error.afterView.child last.captured.root "WAL.commit" = none ∧
    last.error.afterView.child last.captured.root "WAL.commit.next" = none := by
  induction reported with
  | start =>
    obtain ⟨image, _, available⟩ := first.disposed.released
    exact ⟨image, available, rfl, rfl, rfl, rfl, first.error.unchanged.symm ▸ first.error.keeperMissing,
      first.error.unchanged.symm ▸ first.error.markerMissing, first.error.unchanged.symm ▸ first.error.stageMissing⟩
  | @append _ _ previous _ next _ view root reached =>
    obtain ⟨image, _, available⟩ := next.disposed.released
    have sameView := view.trans previous.error.unchanged
    obtain ⟨lock, lockBound, locked⟩ := previous.lockAt
    obtain ⟨nextLock, nextLockBound, nextLocked⟩ := next.lockAt
    rw [sameView, root] at nextLockBound
    have sameLock := Option.some.inj (nextLockBound.symm.trans lockBound)
    rw [sameView, sameLock] at nextLocked
    have nextRoot := next.directoryAt
    rw [sameView, root] at nextRoot
    exact ⟨image.trans reached.1, available, sameView.trans reached.2.2.1, root.trans reached.2.2.2.1,
      nextLocked.symm.trans (locked.trans reached.2.2.2.2.1),
      nextRoot.symm.trans (previous.directoryAt.trans reached.2.2.2.2.2.1),
      next.error.unchanged.symm ▸ next.error.keeperMissing,
      next.error.unchanged.symm ▸ next.error.markerMissing, next.error.unchanged.symm ▸ next.error.stageMissing⟩

end Alvoki.Storage.DiskSession
