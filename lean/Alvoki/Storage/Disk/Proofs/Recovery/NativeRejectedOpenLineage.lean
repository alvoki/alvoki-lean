import Alvoki.Storage.Disk.Proofs.Recovery.NativeOpenListingError
import Alvoki.Storage.Disk.Proofs.Recovery.NativeManifestDecodeError
import Alvoki.Storage.Disk.Proofs.Read.NativeReadRecoveryTrace
import Alvoki.Storage.Disk.Proofs.Native.Execution.NativeReadyClose

import Alvoki.Storage.Disk.Proofs.Recovery.NativeCacheOpenRejection

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- Observations after an early open error use that call's exact census.
With a successful explicit unlock only the descriptor slots can change.
With a failed unlock the same description can keep the lock until its
last observed reference drops. The trace can also stop at the return. -/
inductive NativeOpenErrorDisposal
    {directory : DiskDirectory} {inventory : DescriptorInventory} {retry : LockedFileState FileImage}
    {admission : CensusOpenAdmissionReports input directory inventory retry} {census : DescriptorInventory}
    (cleanup : NativeOpenErrorUnlock admission census) : CensusOpenState → Prop where
  | returned : NativeOpenErrorDisposal cleanup (census, cleanup.files)
  | released (success : cleanup.result = .ok ()) (drops : List LockReferenceDrop) :
      NativeOpenErrorDisposal cleanup (census.afterDrops drops, cleanup.files)
  | failed {cause : IO.Error} {after : CensusOpenState} (error : cleanup.result = .error cause)
      (slots : LockCensusTrace directory admission.owner.description census cleanup.files after.1 after.2) :
      NativeOpenErrorDisposal cleanup after

namespace NativeOpenErrorDisposal

variable {directory : DiskDirectory} {inventory : DescriptorInventory} {retry : LockedFileState FileImage}
  {admission : CensusOpenAdmissionReports input directory inventory retry} {census : DescriptorInventory}
  {cleanup : NativeOpenErrorUnlock admission census} {after : CensusOpenState}

theorem preserves (observed : NativeOpenErrorDisposal cleanup after) :
    after.1.inode = census.inode ∧ after.2.image = retry.image := by
  cases observed with
  | returned | released => exact ⟨rfl, cleanup.keepsFiles⟩
  | failed error slots => exact ⟨slots.reached.2.1, (cleanup.admitsAfterFailedUnlock error slots).2.1⟩

/-- Later admission cannot proceed after a failed unlock while that same
description still has a reference. A successful explicit unlock makes
the lock vacant regardless of any surviving references. -/
theorem admits (observed : NativeOpenErrorDisposal cleanup after) :
    TryLockObserves after.2.owners directory (.ok true) ↔
      cleanup.result = .ok () ∨ after.1.references admission.owner.description = [] := by
  cases observed with
  | returned =>
    have live : census.references admission.owner.description ≠ [] :=
      List.ne_nil_of_mem (census.mem_references.mpr ⟨admission.owner, cleanup.ownerLive, rfl, rfl⟩)
    simpa only [live, or_false] using cleanup.admits
  | released success _ =>
    simp only [cleanup.admits, success, true_or]
  | failed error slots =>
    simpa [error] using (cleanup.admitsAfterFailedUnlock error slots).2.2

end NativeOpenErrorDisposal

/-- Whether the reached error and disposal leave the stable lock vacant. -/
def NativeOpenErrorUnlock.canRetry {directory : DiskDirectory} {inventory : DescriptorInventory}
    {retry : LockedFileState FileImage}
    {admission : CensusOpenAdmissionReports input directory inventory retry} {census : DescriptorInventory}
    (cleanup : NativeOpenErrorUnlock admission census) (after : DescriptorInventory) : Bool :=
  match cleanup.result with
  | .ok () => true
  | .error _ => (after.references admission.owner.description).isEmpty

theorem NativeOpenErrorDisposal.canRetry_iff {directory : DiskDirectory} {inventory : DescriptorInventory}
    {retry : LockedFileState FileImage}
    {admission : CensusOpenAdmissionReports input directory inventory retry} {census : DescriptorInventory}
    {cleanup : NativeOpenErrorUnlock admission census} {after : CensusOpenState}
    (observed : NativeOpenErrorDisposal cleanup after) :
    TryLockObserves after.2.owners directory (.ok true) ↔ cleanup.canRetry after.1 = true := by
  rw [observed.admits]
  cases result : cleanup.result with
  | ok value => cases value; simp [NativeOpenErrorUnlock.canRetry, result]
  | error cause => simp [NativeOpenErrorUnlock.canRetry, result]

/-- One caller-supplied input reaches the held route check through its
actual admission. Its original worker and installation callbacks are
carried along even though neither can be reached on this branch. -/
structure NativeEarlyOpenRejection (input : FilePath) (directory : DiskDirectory) (before : CensusOpenState) where
  admission : CensusOpenAdmissionReports input directory before.1 before.2
  route : NativeMarkerRouteError admission
  marked : DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened
  bootstrap : DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened
  install : DiskDirectory → DescriptorSlot → CensusDirectoryCache → Reopened →
    EStateM IO.Error CensusOpenState SegmentedSession

namespace NativeEarlyOpenRejection

variable {input : FilePath} {directory : DiskDirectory} {before : CensusOpenState}

def diagnostic (attempt : NativeEarlyOpenRejection input directory before) : IO.Error :=
  attempt.route.cleanup.diagnostic attempt.route.cause

theorem returns (attempt : NativeEarlyOpenRejection input directory before) :
    attempt.route.run attempt.marked attempt.bootstrap attempt.install =
      .error attempt.diagnostic (attempt.admission.reached, attempt.route.cleanup.files) :=
  (attempt.route.returns attempt.marked attempt.bootstrap attempt.install).1

/-- The raw lock child and captured directory are the same physical
objects as in the last installed session, even though each attempt
obtains new descriptions and can reuse numeric descriptor slots. -/
def sameObjects (attempt : NativeEarlyOpenRejection input directory before) (lock root : Nat) : Prop :=
  attempt.admission.view.modelObject attempt.route.lock = lock ∧
  attempt.admission.view.modelObject attempt.admission.root = root

theorem captures (attempt : NativeEarlyOpenRejection input directory before)
    (same : attempt.sameObjects lock root) :
    attempt.admission.reached.inode attempt.admission.owner.description = lock ∧
    attempt.admission.reached.inode attempt.admission.cached.description = root := by
  have opened := attempt.route.returns attempt.marked attempt.bootstrap attempt.install
  exact ⟨opened.2.2.2.2.2.2.1.symm.trans same.1, opened.2.2.2.2.1.symm.trans same.2⟩

end NativeEarlyOpenRejection

/-- A held open can stop at the marker route check, at manifest decoding
or at the marked worker's checked listing. Each branch retains the
reached census through its temporary reads and uses local cleanup. -/
inductive NativeOpenRejectionRoute {input : FilePath} {directory : DiskDirectory}
    {inventory : DescriptorInventory} {retry : LockedFileState FileImage}
    (admission : CensusOpenAdmissionReports input directory inventory retry) where
  | marker (seen : NativeMarkerRouteError admission)
      (marked : DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened)
  | manifest (seen : NativeManifestDecodeError admission) (cleanup : NativeOpenErrorUnlock admission seen.afterRead)
      (readSize : FilePath → EStateM IO.Error CensusOpenState Nat)
      (readPrefix : FilePath → Nat → EStateM IO.Error CensusOpenState ByteArray) (tail : RejectedMarkerTail)
  | listing (seen : NativeMarkedListingError admission) (rest : NativeMarkedListingError.Remainder)
      (inodes : seen.atListing.inode = admission.reached.inode)

namespace NativeOpenRejectionRoute

variable {retry : LockedFileState FileImage}
  {admission : CensusOpenAdmissionReports input directory inventory retry}

def census : NativeOpenRejectionRoute admission → DescriptorInventory
  | .marker _ _ => admission.reached
  | .manifest seen _ _ _ _ => seen.afterRead
  | .listing seen _ _ => seen.atListing

def cleanup (route : NativeOpenRejectionRoute admission) : NativeOpenErrorUnlock admission route.census :=
  match route with
  | .marker seen _ => seen.cleanup
  | .manifest _ cleanup _ _ _ => cleanup
  | .listing seen _ _ => seen.cleanup

def cause : NativeOpenRejectionRoute admission → IO.Error
  | .marker seen _ => seen.cause
  | .manifest seen _ _ _ _ => IO.userError seen.cause
  | .listing seen _ _ => seen.listing.cause

def lock : NativeOpenRejectionRoute admission → DeviceInode
  | .marker seen _ => seen.lock
  | .manifest seen _ _ _ _ => seen.lock
  | .listing seen _ _ => seen.lock

theorem censusInodes (route : NativeOpenRejectionRoute admission) : route.census.inode = inventory.inode := by
  cases route with
  | marker => rfl
  | manifest => rfl
  | listing _ _ inodes => exact inodes

theorem captures (route : NativeOpenRejectionRoute admission) :
    admission.view.child admission.root "LOCK" = some route.lock ∧
    route.census.inode admission.owner.description = admission.view.modelObject route.lock ∧
    route.census.inode admission.cached.description = admission.view.modelObject admission.root := by
  cases route with
  | marker seen _ => exact ⟨seen.lockEntry, seen.lockInode.symm, admission.opened.captures.2.2.2.2.1.symm⟩
  | manifest seen _ _ _ _ =>
    exact ⟨seen.lockEntry, seen.lockObject.symm, admission.opened.captures.2.2.2.2.1.symm⟩
  | listing seen _ _ => exact ⟨seen.lockEntry, seen.lockObject, seen.rootObject⟩

end NativeOpenRejectionRoute

/-- The original open and its actual failing route, keeping the called
bootstrap and installation callbacks as parameters to the schedule. -/
structure NativeRejectedOpenAttempt (input : FilePath) (directory : DiskDirectory) (before : CensusOpenState) where
  admission : CensusOpenAdmissionReports input directory before.1 before.2
  route : NativeOpenRejectionRoute admission
  bootstrap : DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened
  install : DiskDirectory → DescriptorSlot → CensusDirectoryCache → Reopened →
    EStateM IO.Error CensusOpenState SegmentedSession

namespace NativeRejectedOpenAttempt

variable {input : FilePath} {directory : DiskDirectory} {before : CensusOpenState}

def diagnostic (attempt : NativeRejectedOpenAttempt input directory before) : IO.Error :=
  attempt.route.cleanup.diagnostic attempt.route.cause

def run (attempt : NativeRejectedOpenAttempt input directory before) :
    EStateM.Result IO.Error CensusOpenState SegmentedSession :=
  match attempt.route with
  | .marker seen marked => seen.run marked attempt.bootstrap attempt.install
  | .manifest seen _ readSize readPrefix tail =>
      attempt.admission.run (seen.recover readSize readPrefix tail attempt.bootstrap attempt.install)
  | .listing seen rest _ => attempt.admission.run (seen.recover rest attempt.bootstrap attempt.install)

theorem returns (attempt : NativeRejectedOpenAttempt input directory before) :
    attempt.run = .error attempt.diagnostic (attempt.route.census, attempt.route.cleanup.files) := by
  rcases attempt with ⟨admission, route, bootstrap, install⟩
  cases route with
  | marker seen marked => exact (seen.returns marked bootstrap install).1
  | manifest seen cleanup readSize readPrefix tail =>
    exact (seen.returns cleanup readSize readPrefix tail bootstrap install).1
  | listing seen rest _ => exact (seen.returns rest bootstrap install).1

def sameObjects (attempt : NativeRejectedOpenAttempt input directory before) (lock root : Nat) : Prop :=
  attempt.admission.view.modelObject attempt.route.lock = lock ∧
  attempt.admission.view.modelObject attempt.admission.root = root

theorem captures (attempt : NativeRejectedOpenAttempt input directory before) (same : attempt.sameObjects lock root) :
    attempt.admission.view.child attempt.admission.root "LOCK" = some attempt.route.lock ∧
    attempt.route.census.inode attempt.admission.owner.description = lock ∧
    attempt.route.census.inode attempt.admission.cached.description = root := by
  obtain ⟨child, lockIdentity, directoryIdentity⟩ := attempt.route.captures
  exact ⟨child, lockIdentity.trans same.1, directoryIdentity.trans same.2⟩

end NativeRejectedOpenAttempt

def NativeEarlyOpenRejection.attempt (seen : NativeEarlyOpenRejection input directory before) :
    NativeRejectedOpenAttempt input directory before :=
  ⟨seen.admission, .marker seen.route seen.marked, seen.bootstrap, seen.install⟩

/-- Every next admitted attempt starts at the preceding error's reached
files and census, after any reported disposal. The two lists keep the
requested paths and actual returned errors in the same order. Each
failed route must be supported by that attempt's reached image. -/
inductive NativeRejectedOpenLineage (directory : DiskDirectory) (lock root : Nat) (first : CensusOpenState) :
    List FilePath → List IO.Error → CensusOpenState → Bool → Prop where
  | start (vacant : TryLockObserves first.2.owners directory (.ok true)) :
      NativeRejectedOpenLineage directory lock root first [] [] first true
  | attempted {inputs errors before after}
      (prior : NativeRejectedOpenLineage directory lock root first inputs errors before true)
      (input : FilePath)
      (attempt : NativeRejectedOpenAttempt input directory before) (objects : attempt.sameObjects lock root)
      (disposal : NativeOpenErrorDisposal attempt.route.cleanup after) :
      NativeRejectedOpenLineage directory lock root first (inputs ++ [input]) (errors ++ [attempt.diagnostic])
        after (attempt.route.cleanup.canRetry after.1)

  | cacheInitializationFailed {inputs errors before}
      (prior : NativeRejectedOpenLineage directory lock root first inputs errors before true)
      (input : FilePath) (attempt : NativeCacheOpenRejection input directory before)
      (objects : attempt.sameObjects lock root) (drops : List LockReferenceDrop) :
      NativeRejectedOpenLineage directory lock root first (inputs ++ [input])
        (errors ++ [attempt.failure.projectedFailure.error]) (attempt.afterDrops drops) (attempt.availableAfter drops)

/-- Keep the direct marker-route entry for callers with that specific report. -/
theorem NativeRejectedOpenLineage.rejected
    (prior : NativeRejectedOpenLineage directory lock root first inputs errors before true) (input : FilePath)
    (seen : NativeEarlyOpenRejection input directory before) (objects : seen.sameObjects lock root)
    (disposal : NativeOpenErrorDisposal seen.route.cleanup after) :
    NativeRejectedOpenLineage directory lock root first (inputs ++ [input]) (errors ++ [seen.diagnostic])
      after (seen.route.cleanup.canRetry after.1) :=
  .attempted prior input seen.attempt objects disposal

theorem NativeRejectedOpenLineage.preserves
    (reported : NativeRejectedOpenLineage directory lock root first inputs errors after available) :
    after.1.inode = first.1.inode ∧ after.2.image = first.2.image ∧ errors.length = inputs.length ∧
    (TryLockObserves after.2.owners directory (.ok true) ↔ available = true) := by
  induction reported with
  | start vacant => exact ⟨rfl, rfl, rfl, ⟨fun _ => rfl, fun _ => vacant⟩⟩
  | attempted _ _ attempt _ disposal prior =>
    obtain ⟨inodes, image⟩ := disposal.preserves
    exact ⟨inodes.trans (attempt.route.censusInodes.trans prior.1),
      image.trans prior.2.1, by simp [prior.2.2.1], disposal.canRetry_iff⟩

  | cacheInitializationFailed _ _ attempt _ drops prior =>
    have disposed := attempt.disposes drops
    exact ⟨(attempt.censusInodes drops).trans prior.1, disposed.1.trans prior.2.1,
      by simp [prior.2.2.1], disposed.2.1⟩

theorem NativeReadPosition.startsRejectedOpenLineage (current : NativeReadPosition history log)
    (close : NativeReadyClose current.state) (success : close.report.result = .ok ()) :
    NativeRejectedOpenLineage current.state.session.directory
      (current.state.census.inode current.state.owner.description)
      (current.state.census.inode current.state.directorySlot.description)
      (close.report.finished.descriptors, current.state.releasedFiles) [] []
      (close.report.finished.descriptors, current.state.releasedFiles) true :=
  .start (close.closes current.readPrefix.refines.1 success).2.2.2.2

/-- A finite prefix can end after unsuccessful open attempts following
an actual successful close. The exact file image of the original
checkpoint and WAL still explains all of the client's earlier reads. -/
theorem NativeReadPosition.rejectedOpensAfterClose (current : NativeReadPosition history log)
    (close : NativeReadyClose current.state) (success : close.report.result = .ok ())
    (reported : NativeRejectedOpenLineage current.state.session.directory
      (current.state.census.inode current.state.owner.description)
      (current.state.census.inode current.state.directorySlot.description)
      (close.report.finished.descriptors, current.state.releasedFiles) inputs errors after available) :
    close.report.run = .ok () close.report.finished ∧ close.report.finished.phase = .closed ∧
    close.report.finished.descriptors = current.state.census.afterDrops
      (close.report.drops .active ++ close.report.drops .pending ++ close.report.drops .directory) ∧
    TryLockObserves current.state.releasedFiles.owners current.state.session.directory (.ok true) ∧
    after.1.inode = current.state.census.inode ∧ after.2.image = current.state.files.image ∧
    (TryLockObserves after.2.owners current.state.session.directory (.ok true) ↔ available = true) ∧
    errors.length = inputs.length ∧ PendingClientReplay log current.reads history ∧
    ∀ read ∈ current.reads, read.BoundedBy history.length := by
  obtain ⟨closed, phase, _, descriptors, vacant⟩ := close.closes current.readPrefix.refines.1 success
  obtain ⟨inodes, selected, count, allowed⟩ := reported.preserves
  have stable := congrArg DescriptorInventory.inode descriptors
  exact ⟨closed, phase, descriptors, vacant, inodes.trans stable,
    selected, allowed, count, current.readPrefix.refines.2.2, current.readPrefix.readsBounded⟩

end Alvoki.Storage.DiskSession
