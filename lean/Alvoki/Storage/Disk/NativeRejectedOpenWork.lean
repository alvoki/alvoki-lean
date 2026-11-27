import Alvoki.Storage.Disk.Proofs.Recovery.NativeMarkedRecoveryWork
import Alvoki.Storage.Disk.NativeMarkedListingWork
import Alvoki.Storage.Disk.NativeRejectedOpenLineage

namespace Alvoki.Storage.DiskSession

open System Manifest RecoveryRequestCount WalSegmentRepair WAL.Boundary

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}

namespace NativeManifestDecodeError

/-- Count the same optional manifest reader, on its reported open and
cursor, before the decoder consumes the reached prefix. -/
def countedManifest (fault : NativeManifestDecodeError admission) : EStateM.Result IO.Error (Nat × Nat) (Option ByteArray) :=
  fault.reads.countMetadata directory (directory.file .manifest) (0, 0)

theorem countedManifest_projects (fault : NativeManifestDecodeError admission) :
    forgetRecoveryChunkCount fault.countedManifest =
      .ok (some (fault.bytes.extract 0 (IntegrityCheckpoint.acquisitionSize fault.bytes)))
        (IntegrityCheckpoint.acquisitionSize fault.bytes) := by
  rw [countedManifest, fault.reads.countMetadata_projects]
  exact fault.manifest.manifestPrefix fault.fits

theorem countedManifest_le (fault : NativeManifestDecodeError admission) :
    recoveryCalls Prod.snd fault.countedManifest ≤ fault.bytes.size := by
  have different : (directory.file .manifest == directory.file .walBoundary) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro same
    have paths := congrArg FilePath.toString same
    change (directory.path.toString ++ "/") ++ "MANIFEST" =
      (directory.path.toString ++ "/") ++ "WAL.commit" at paths
    exact (by decide : "MANIFEST" ≠ "WAL.commit") ((String.append_right_inj _).mp paths)
  let seen := fault.manifest.observesFile
  have bound := fault.reads.countMetadata_le directory (directory.file .manifest) (0, 0)
  simpa [countedManifest, different, seen.stat, seen.extent, Except.toOption] using bound

end NativeManifestDecodeError

def selectedManifestExtent (state : LockedFileState FileImage) : Nat :=
  (state.image.directory.active.manifest.map ByteArray.size).getD 0

/-- These errors stop before directory and repair requests. An early
marker probe uses no payload callback. A malformed manifest charges its
own bounded reader. The listing branch uses its separate read report. -/
def NativeOpenRejectionRoute.chunkRequests : NativeOpenRejectionRoute admission → Option Nat
  | .marker _ _ => some 0
  | .manifest fault _ _ _ _ => some (recoveryCalls Prod.snd fault.countedManifest)
  | .listing _ _ _ => none

theorem NativeOpenRejectionRoute.chunkRequests_le (route : NativeOpenRejectionRoute admission)
    (counted : route.chunkRequests = some requests) : requests ≤ selectedManifestExtent retry := by
  cases route with
  | marker =>
    simp only [chunkRequests, Option.some.injEq] at counted
    exact counted ▸ Nat.zero_le _
  | manifest fault _ _ _ _ =>
    simp only [chunkRequests, Option.some.injEq] at counted
    simpa only [selectedManifestExtent, fault.selected, Option.map_some, Option.getD_some, ← counted]
      using fault.countedManifest_le
  | listing => cases counted

structure NativeRejectedOpenWorkEvent where
  input : FilePath
  diagnostic : IO.Error
  chunks : Nat
  directoryRequests : Nat
  runAndMarkerBudget : Nat

structure NativeCountedListingAttempt (input : FilePath) (directory : DiskDirectory) (before : CensusOpenState) where
  admission : CensusOpenAdmissionReports input directory before.1 before.2
  failure : NativeMarkedListingError admission
  work : NativeListingWork failure
  rest : NativeMarkedListingError.Remainder
  bootstrap : DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened
  install : DiskDirectory → DescriptorSlot → CensusDirectoryCache → Reopened →
    EStateM IO.Error CensusOpenState SegmentedSession

namespace NativeCountedListingAttempt

variable {input : FilePath} {directory : DiskDirectory} {before : CensusOpenState}

def attempt (seen : NativeCountedListingAttempt input directory before) : NativeRejectedOpenAttempt input directory before :=
  ⟨seen.admission, .listing seen.failure seen.rest seen.work.listingInodes, seen.bootstrap, seen.install⟩

noncomputable def event (seen : NativeCountedListingAttempt input directory before) : NativeRejectedOpenWorkEvent :=
  ⟨input, seen.attempt.diagnostic, seen.work.chunkRequests, seen.work.directoryRequests,
    seen.work.selectedRunBytes + WAL.Boundary.acquisitionLimit⟩

theorem chunks_le (seen : NativeCountedListingAttempt input directory before) :
    seen.event.chunks ≤ selectedManifestExtent before.2 + seen.event.runAndMarkerBudget := by
  exact seen.work.chunkRequests_le

end NativeCountedListingAttempt

/-- Store the count computed from each actual rejected route alongside
its caller input and error. Every attempt uses the preceding reached
files and descriptor inventory and the same physical directory and lock. -/
inductive NativeRejectedOpenWorkTrace (directory : DiskDirectory) (lock root : Nat) (first : CensusOpenState) :
    List NativeRejectedOpenWorkEvent → CensusOpenState → Bool → Prop where
  | start (vacant : TryLockObserves first.2.owners directory (.ok true)) :
      NativeRejectedOpenWorkTrace directory lock root first [] first true
  | step {events before after requests}
      (prior : NativeRejectedOpenWorkTrace directory lock root first events before true) (input : FilePath)
      (attempt : NativeRejectedOpenAttempt input directory before) (objects : attempt.sameObjects lock root)
      (disposed : NativeOpenErrorDisposal attempt.route.cleanup after)
      (counted : attempt.route.chunkRequests = some requests) :
      NativeRejectedOpenWorkTrace directory lock root first
        (events ++ [⟨input, attempt.diagnostic, requests, 0, 0⟩]) after (attempt.route.cleanup.canRetry after.1)
  | listing {events before after}
      (prior : NativeRejectedOpenWorkTrace directory lock root first events before true) (input : FilePath)
      (seen : NativeCountedListingAttempt input directory before) (objects : seen.attempt.sameObjects lock root)
      (disposed : NativeOpenErrorDisposal seen.attempt.route.cleanup after) :
      NativeRejectedOpenWorkTrace directory lock root first
        (events ++ [seen.event]) after (seen.attempt.route.cleanup.canRetry after.1)

theorem NativeRejectedOpenWorkTrace.lineage
    (trace : NativeRejectedOpenWorkTrace directory lock root first events after available) :
    NativeRejectedOpenLineage directory lock root first (events.map (·.input)) (events.map (·.diagnostic)) after available := by
  induction trace with
  | start vacant => exact .start vacant
  | step _ input attempt objects disposed _ earlier =>
    simpa only [List.map_append, List.map_cons, List.map_nil] using
      earlier.attempted input attempt objects disposed
  | listing _ input seen objects disposed earlier =>
    simpa only [List.map_append, List.map_cons, List.map_nil, NativeCountedListingAttempt.event] using
      earlier.attempted input seen.attempt objects disposed

/-- For a finite reported sequence, the selected chunk count has one
initial manifest extent per attempt. A listing failure adds the declared
run bytes and marker cap. Failed marker probes reach zero chunk reads. -/
theorem NativeRejectedOpenWorkTrace.chunkRequests_le
    (trace : NativeRejectedOpenWorkTrace directory lock root first events after available) :
    (events.map (·.chunks)).sum ≤ events.length * selectedManifestExtent first.2 +
      (events.map (·.runAndMarkerBudget)).sum := by
  induction trace with
  | start => simp
  | step prior _ attempt _ _ counted earlier =>
    have image := prior.lineage.preserves.2.1
    have bounded := attempt.route.chunkRequests_le counted
    change _ ≤ selectedManifestExtent _ at bounded
    simp only [selectedManifestExtent, image] at bounded
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
      Nat.add_zero, List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul, selectedManifestExtent] at earlier ⊢
    omega
  | listing prior _ seen _ _ earlier =>
    have image := prior.lineage.preserves.2.1
    have bounded := seen.chunks_le
    simp only [selectedManifestExtent, image] at bounded
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
      Nat.add_zero, List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul, selectedManifestExtent] at earlier ⊢
    omega

/-- The completed trace supplies actual vacancy for a later admitted
call after successful unlock or observed final reference release. -/
theorem NativeRejectedOpenWorkTrace.vacant
    (trace : NativeRejectedOpenWorkTrace directory lock root first events after true) :
    TryLockObserves after.2.owners directory (.ok true) :=
  trace.lineage.preserves.2.2.2.mpr rfl

/-- A healthy marked attempt can follow the charged failures when the
reached files admit a valid checkpoint and WAL selection. Its counts
are derived from the same report that returns the installed session. -/
theorem NativeRejectedOpenWorkTrace.finishesWithWork
    (trace : NativeRejectedOpenWorkTrace directory lock root first events after true)
    {history : List WAL.Write} {layout : CanonicalKeeperLayout after.2.image history}
    {published : CheckpointPublication.Image} {checkpoint : Option (PackedTable × UInt64)}
    {selected : SelectedIntegrityCheckpoint published.durable after.2.image.directory.active.manifest checkpoint}
    (finish : MarkedReadyOpenObservations input directory after.1 after.2 layout published trace.vacant selected)
    (objects : finish.admission.view.modelObject finish.reads.lock = lock ∧
      finish.admission.view.modelObject finish.admission.root = root)
    (prepared : Prepared after.2.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      after.2.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    let finishChunks := selectedManifestExtent after.2 + WAL.Boundary.acquisitionLimit +
      (((checkpoint.getD (.empty, 0)).1.runs.map (·.run.bytes.size)).sum +
        (layout.range.through - layout.first) * WAL.frameSize)
    let finishDirectory := finish.reads.listing.scan.names.length + 3
    let finishRepair := after.2.image.later.visible.length + 6
    ∃ session final repairs,
      finish.finish.run finish.chronology = .ok session (finish.finish.census, final) ∧
      final.image.directory.active = first.2.image.directory.active ∧
      CachedRetryInstalled (before := after.2) finish.reads.walReads finish.admission.reached
        finish.admission.owner finish.reads.bindings published finish.callbacks.liveRefs (.ok session final) ∧
      finish.admission.reached.inode finish.admission.owner.description = lock ∧
      finish.admission.reached.inode finish.admission.cached.description = root ∧
      countBoundedRepairCallbacks directory layout.boundedPlan finish.reads.wal.keeper.calls.metadata.byteSize.toNat =
        .ok repairs ∧
      ((events.map (·.chunks)).sum + (events.map (·.directoryRequests)).sum) +
        (finish.metadataReadRequests + finish.payloadReadRequests) +
        (finish.directoryWork.opendirCalls + finish.directoryWork.readdirCalls + finish.directoryWork.closedirCalls) + repairs ≤
        (events.length * selectedManifestExtent first.2 + (events.map (·.runAndMarkerBudget)).sum +
          (events.map (·.directoryRequests)).sum) + finishChunks + finishDirectory + finishRepair := by
  obtain ⟨session, final, repairs, returned, pair, installed, chunks, listed, repairCount, repairBound⟩ :=
    finish.installsWithWork prepared following accepted ordered
  have earlier := Nat.add_le_add_right trace.chunkRequests_le (events.map (·.directoryRequests)).sum
  have image := trace.lineage.preserves.2.1
  refine ⟨session, final, repairs, returned, pair.trans (congrArg (·.directory.active) image), installed,
    finish.reads.identifiesLock.symm.trans objects.1, finish.admission.opened.captures.2.2.2.2.1.symm.trans objects.2,
    repairCount, ?_⟩
  simp only [selectedManifestExtent]
  rw [listed]
  exact Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add earlier chunks) _) repairBound

end Alvoki.Storage.DiskSession
