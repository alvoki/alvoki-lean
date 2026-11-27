import Alvoki.Storage.Disk.Proofs.Recovery.NativeMarkedFirstBarrierWork

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

variable {directory : DiskDirectory} {history : List WAL.Write}
  {published : CheckpointPublication.Image} {checkpoint : Option (PackedTable × UInt64)}

/-- One marked open issued on the exact files and census left by its
predecessor. The selected checkpoint is fixed across the retry series.
Each attempt supplies its actual preparation and cleanup reports. -/
structure NativeMarkedBarrierAttempt (directory : DiskDirectory) (input : FilePath)
    (before : CensusOpenState) (history : List WAL.Write) (published : CheckpointPublication.Image)
    (checkpoint : Option (PackedTable × UInt64)) where
  admission : CensusOpenAdmissionReports input directory before.1 before.2
  layout : CanonicalKeeperLayout before.2.image history
  selected : SelectedIntegrityCheckpoint published.durable before.2.image.directory.active.manifest checkpoint
  reads : CapturedMarkedReadReports admission layout published
  keeper : CapturedKeeperOpenReports reads
  chronology : CapturedMarkedReadCensus reads keeper
  barrier : NativeMarkedFirstBarrierError reads keeper
  prepared : Prepared before.2.image layout.target layout.plan
  following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1, layout.range.watermark < start
  accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
    before.2.image.directory.active.manifest
  ordered : WAL.OrdinalsFrom 1 history
  flat : optionalMetadataWith (admission.lookup (directory.file .wal)) (admission.reached, admission.held) =
    .ok none (admission.reached, admission.held)
  marker : IO.FS.Metadata
  found : optionalMetadataWith (admission.lookup (directory.file .walBoundary)) (admission.reached, admission.held) =
    .ok (some marker) (admission.reached, admission.held)
  unlock : Except IO.Error Unit
  unlocked : admission.unlock admission.owner () (keeper.afterRead, barrier.reachedFiles) = match unlock with
    | .ok () => .ok () (keeper.afterRead, barrier.afterUnlock unlock)
    | .error cause => .error cause (keeper.afterRead, barrier.afterUnlock unlock)
  bootstrap : DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened
  install : DiskDirectory → DescriptorSlot → CensusDirectoryCache → Reopened →
    EStateM IO.Error CensusOpenState SegmentedSession

/-- The work recorded for an issued failed marked open. Readdir work
uses raw names, including those ignored by the WAL extent filter. -/
structure NativeMarkedBarrierEvent where
  input : FilePath
  diagnostic : IO.Error
  settled : Bool
  chunkRequests : Nat
  listedNames : Nat
  directoryRequests : Nat
  repairRequests : Nat

namespace NativeMarkedBarrierAttempt

variable {input : FilePath} {before : CensusOpenState}
  (attempt : NativeMarkedBarrierAttempt directory input before history published checkpoint)

noncomputable def event : NativeMarkedBarrierEvent :=
  let scan := attempt.reads.directoryWork
  ⟨input, attempt.barrier.openDiagnostic attempt.unlock, attempt.barrier.settled,
    attempt.reads.metadataReadRequests + attempt.reads.payloadReadRequests, attempt.reads.listing.scan.names.length,
    scan.opendirCalls + scan.readdirCalls + scan.closedirCalls, 1⟩

def returnedFiles : LockedFileState FileImage := attempt.barrier.afterUnlock attempt.unlock

def run : EStateM.Result IO.Error CensusOpenState SegmentedSession :=
  attempt.barrier.run attempt.chronology attempt.bootstrap attempt.install

def chunkBudget (image : FileImage) (history : List WAL.Write) (checkpoint : Option (PackedTable × UInt64)) : Nat :=
  (image.directory.active.manifest.map ByteArray.size).getD 0 + WAL.Boundary.acquisitionLimit +
    (((checkpoint.getD (.empty, 0)).1.runs.map (·.run.bytes.size)).sum + history.length * WAL.frameSize)

theorem returns :
    attempt.run = .error attempt.event.diagnostic (attempt.keeper.afterRead, attempt.returnedFiles) ∧
    attempt.returnedFiles.image =
      (if attempt.event.settled then before.2.image.syncDirectory else before.2.image) ∧
    attempt.event.chunkRequests ≤ chunkBudget before.2.image history checkpoint ∧
    attempt.event.directoryRequests = attempt.event.listedNames + 3 ∧ attempt.event.repairRequests = 1 ∧
    attempt.barrier.countedFinish attempt.layout.boundedPlan attempt.layout.plan.keeperBytes.size
      ((NativeMarkedFirstBarrierError.keeperCache (reads := attempt.reads), attempt.keeper.afterRead, attempt.admission.held), 0) =
        .error attempt.barrier.diagnostic
          ((NativeMarkedFirstBarrierError.keeperCache (reads := attempt.reads), attempt.keeper.afterRead,
            attempt.barrier.reachedFiles), attempt.event.repairRequests) := by
  obtain ⟨ran, files, _, chunks, listed, repair⟩ :=
    attempt.barrier.returnsWithWork attempt.chronology attempt.selected attempt.prepared attempt.following attempt.accepted
      attempt.ordered attempt.flat attempt.found attempt.unlock attempt.unlocked attempt.bootstrap attempt.install
  refine ⟨ran, files, Nat.le_trans chunks ?_, listed, rfl, repair⟩
  unfold chunkBudget
  rw [attempt.layout.through]
  exact Nat.add_le_add_left
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le ..)) _) _

/-- All observed finalizers follow the returned error. A preceding
successful unlock has already cleared the owner. A failed unlock leaves
the exact returned owner to be released by its last observed slot drop. -/
def afterDrops (drops : List LockReferenceDrop) : CensusOpenState :=
  let census := attempt.keeper.afterRead
  (census.afterDrops drops, match attempt.unlock with
    | .ok () => attempt.returnedFiles
    | .error _ => census.dropLockState attempt.admission.owner.description drops directory attempt.returnedFiles)

def availableAfter (drops : List LockReferenceDrop) : Bool :=
  match attempt.unlock with
  | .ok () => true
  | .error _ => ((attempt.afterDrops drops).1.references attempt.admission.owner.description).isEmpty

theorem disposal (drops : List LockReferenceDrop) :
    (attempt.afterDrops drops).2.image = attempt.returnedFiles.image ∧
    (TryLockObserves (attempt.afterDrops drops).2.owners directory (.ok true) ↔ attempt.availableAfter drops = true) := by
  cases unlocked : attempt.unlock with
  | ok value =>
    cases value
    simp [afterDrops, availableAfter, unlocked, returnedFiles, NativeMarkedFirstBarrierError.afterUnlock,
      NativeMarkedFirstBarrierError.reachedFiles, LockOwners.set, TryLockObserves]
  | error cause =>
    have own : attempt.returnedFiles.owners.Owns directory attempt.admission.owner.description := by
      simpa only [returnedFiles, unlocked, NativeMarkedFirstBarrierError.afterUnlock,
        NativeMarkedFirstBarrierError.reachedFiles, CensusOpenAdmissionReports.held] using attempt.admission.opened.held
    have live : attempt.keeper.afterRead.references attempt.admission.owner.description ≠ [] :=
      List.ne_nil_of_mem (attempt.keeper.afterRead.mem_references.mpr
        ⟨attempt.admission.owner, attempt.keeper.ownerRetained, rfl, rfl⟩)
    have dropped := (LockCensusTrace.start own live).drops drops
    have frame := congrArg LockedFileState.image dropped.reached.2.2
    have available := dropped.freshFlockAllowed
    simp only [afterDrops, availableAfter, unlocked, List.isEmpty_iff]
    refine ⟨?_, available⟩
    split at frame <;> exact frame

theorem censusInodes : attempt.keeper.afterRead.inode = before.1.inode := by
  unfold CapturedKeeperOpenReports.afterRead
  rw [attempt.keeper.opened]
  rfl

def sameObjects (lock root : Nat) : Prop :=
  attempt.admission.view.modelObject attempt.reads.lock = lock ∧
    attempt.admission.view.modelObject attempt.admission.root = root

theorem captures (same : attempt.sameObjects lock root) :
    attempt.keeper.afterRead.inode attempt.admission.owner.description = lock ∧
    attempt.keeper.afterRead.inode attempt.admission.cached.description = root := by
  rw [attempt.censusInodes]
  exact ⟨attempt.reads.identifiesLock.symm.trans same.1, attempt.admission.opened.captures.2.2.2.2.1.symm.trans same.2⟩


end NativeMarkedBarrierAttempt

/-- A retry starts only from the exact file and descriptor state of the
preceding observed attempt and its reported finalizers. An after-effect
error can settle the directory's crash choices at any edge. -/
inductive NativeMarkedBarrierRetries (directory : DiskDirectory) (lock root : Nat)
    (history : List WAL.Write) (published : CheckpointPublication.Image) (checkpoint : Option (PackedTable × UInt64))
    (first : CensusOpenState) : List NativeMarkedBarrierEvent → CensusOpenState → Bool → Prop where
  | start (vacant : TryLockObserves first.2.owners directory (.ok true)) :
      NativeMarkedBarrierRetries directory lock root history published checkpoint first [] first true
  | attempted {events before}
      (prior : NativeMarkedBarrierRetries directory lock root history published checkpoint first events before true)
      (input : FilePath)
      (attempt : NativeMarkedBarrierAttempt directory input before history published checkpoint)
      (objects : attempt.sameObjects lock root) (drops : List LockReferenceDrop) :
      NativeMarkedBarrierRetries directory lock root history published checkpoint first
        (events ++ [attempt.event]) (attempt.afterDrops drops) (attempt.availableAfter drops)

namespace NativeMarkedBarrierRetries

/-- The directory barrier does not change the selected visible bindings
or the kept and keeper bytes. Its exact settlement is idempotent. -/
theorem preserves
    (trace : NativeMarkedBarrierRetries directory lock root history published checkpoint first events after available) :
    after.2.image = (if events.any (·.settled) then first.2.image.syncDirectory else first.2.image) ∧
    after.2.image.directory.active = first.2.image.directory.active ∧
    after.2.image.kept = first.2.image.kept ∧ after.2.image.keeper = first.2.image.keeper ∧
    after.2.image.later.visible = first.2.image.later.visible ∧
    after.1.inode = first.1.inode ∧
    (TryLockObserves after.2.owners directory (.ok true) ↔ available = true) := by
  induction trace with
  | start vacant => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, ⟨fun _ => rfl, fun _ => vacant⟩⟩
  | @attempted earlier before prior input attempt objects drops ih =>
    have reached := (attempt.disposal drops).1.trans attempt.returns.2.1
    rw [ih.1] at reached
    have twice : first.2.image.syncDirectory.syncDirectory = first.2.image.syncDirectory := rfl
    have exactImage : (attempt.afterDrops drops).2.image =
        (if (earlier ++ [attempt.event]).any (·.settled) then first.2.image.syncDirectory else first.2.image) := by
      rw [List.any_append]
      simp only [List.any_cons, List.any_nil, Bool.or_false]
      cases past : earlier.any (·.settled) <;> cases now : attempt.event.settled <;>
        simpa only [past, now, Bool.false_or, Bool.true_or, Bool.false_eq_true, ite_false, ite_true, twice] using reached
    have inode : (attempt.afterDrops drops).1.inode = first.1.inode :=
      attempt.censusInodes.trans ih.2.2.2.2.2.1
    refine ⟨exactImage, ?_, ?_, ?_, ?_, inode, (attempt.disposal drops).2⟩ <;> rw [exactImage] <;> split <;> rfl

/-- The same exact checkpoint is still selected when the last reported
disposal permits admission. No new logical selection is needed. -/
theorem retainsSelected
    (trace : NativeMarkedBarrierRetries directory lock root history published checkpoint first events after available)
    (original : SelectedIntegrityCheckpoint published.durable first.2.image.directory.active.manifest checkpoint) :
    SelectedIntegrityCheckpoint published.durable after.2.image.directory.active.manifest checkpoint := by
  rw [trace.preserves.2.1]
  exact original

theorem vacant
    (trace : NativeMarkedBarrierRetries directory lock root history published checkpoint first events after true) :
    TryLockObserves after.2.owners directory (.ok true) :=
  trace.preserves.2.2.2.2.2.2.mpr rfl

/-- Work from a finite actual sequence has one selected chunk budget
per attempt, and precisely one repair request per attempt. No cap on
the number of attempts or the raw listing lengths is assumed. -/
theorem boundedWork
    (trace : NativeMarkedBarrierRetries directory lock root history published checkpoint first events after available) :
    (events.map (·.chunkRequests)).sum ≤ events.length * NativeMarkedBarrierAttempt.chunkBudget first.2.image history checkpoint ∧
    (events.map (·.directoryRequests)).sum = (events.map (·.listedNames)).sum + 3 * events.length ∧
    (events.map (·.repairRequests)).sum = events.length := by
  induction trace with
  | start => simp
  | @attempted _ before prior _ attempt _ _ ih =>
    obtain ⟨_, _, budget, listed, repairs, _⟩ := attempt.returns
    have selected := prior.preserves.2.1
    have sameBudget : NativeMarkedBarrierAttempt.chunkBudget before.2.image history checkpoint =
        NativeMarkedBarrierAttempt.chunkBudget first.2.image history checkpoint := by
      simp only [NativeMarkedBarrierAttempt.chunkBudget, selected]
    rw [sameBudget] at budget
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
      Nat.add_zero, List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]
    exact ⟨by omega, by omega, by omega⟩

end NativeMarkedBarrierRetries
end Alvoki.Storage.DiskSession
