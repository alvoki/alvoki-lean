import Alvoki.Storage.Disk.CapturedAlignedInstallation
import Alvoki.Storage.Disk.NativeMarkedRecoveryWork

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {reads : CapturedMarkedReadReports admission layout published}

private abbrev RepairState := CensusDirectoryCache × CensusOpenState
private abbrev CapturedHandle := DescriptorInventory × DescriptorSlot × Nat

/-- The first required repair barrier reports an error either before or
after settling the directory. No keeper or later-name effects precede it. -/
structure NativeMarkedFirstBarrierError (reads : CapturedMarkedReadReports admission layout published)
    (keeper : CapturedKeeperOpenReports reads) where
  openRead : FilePath → EStateM IO.Error CensusOpenState CapturedHandle
  fsync : CapturedHandle → EStateM IO.Error CensusOpenState Unit
  removeFile : FilePath → EStateM IO.Error RepairState (Except IO.Error Unit)
  write : FilePath → ByteArray → EStateM IO.Error RepairState Unit
  renameFile : FilePath → FilePath → EStateM IO.Error RepairState Unit
  cause : IO.Error
  settled : Bool
  failed : fsync (admission.reached, admission.cached, 0) (keeper.afterRead, admission.held) =
    .error cause (keeper.afterRead, { admission.held with image :=
      if settled then retry.image.syncDirectory else retry.image })

namespace NativeMarkedFirstBarrierError

variable {keeper : CapturedKeeperOpenReports reads}
  (seen : NativeMarkedFirstBarrierError reads keeper)

def reachedFiles : LockedFileState FileImage :=
  { admission.held with image := if seen.settled then retry.image.syncDirectory else retry.image }

def diagnostic : IO.Error :=
  IO.userError s!"sync failed for '{directory.path}': {seen.cause}"

def keeperCache : CensusDirectoryCache :=
  admission.cache.captureKeeper (directory.file (.walSegment layout.keeper.first))
    (reads.wal.keeper.calls.inventory, reads.wal.keeper.calls.slot, 0)
    layout.keeper.bytes.size reads.wal.keeper.calls.metadata.byteSize.toNat

def groupedSync : Array FilePath → EStateM IO.Error RepairState Unit :=
  SyncPathGroup.run (SyncHandleRouting.sync directory.path seen.openRead seen.fsync)

theorem syncFails :
    seen.groupedSync #[directory.path] (keeperCache (reads := reads), keeper.afterRead, admission.held) =
      .error seen.diagnostic (keeperCache (reads := reads), keeper.afterRead, seen.reachedFiles) := by
  unfold groupedSync
  rw [SyncPathGroup.run_single]
  have captures : (keeperCache (reads := reads)).directory = some (admission.reached, admission.cached, 0) := by
    unfold keeperCache Cache.captureKeeper
    split <;> rfl
  simp [SyncHandleRouting.sync, Cache.resolve, captures, withCache, seen.failed, reachedFiles, diagnostic]
  rfl

private def countCallback (act : EStateM IO.Error RepairState α) :
    EStateM IO.Error (RepairState × Nat) α :=
  fun (before, calls) => match act before with
  | .ok result after => .ok result (after, calls + 1)
  | .error cause after => .error cause (after, calls + 1)

def countedFinish (plan : Plan) (measure : Nat) : EStateM IO.Error (RepairState × Nat) Unit :=
  finishBoundedMarkedOpen directory plan measure
    (fun path => countCallback (seen.removeFile path))
    (fun path bytes => countCallback (seen.write path bytes))
    (fun paths => countCallback (seen.groupedSync paths))
    (fun source target => countCallback (seen.renameFile source target))

/-- The same required first sync is reached on the aligned, prune and trim
branches. Starting with any count, the reported error charges exactly
one group (here one directory fsync), with the same reached file image. -/
theorem finishes (prepared : Prepared retry.image layout.target layout.plan) (calls : Nat) :
    let before : RepairState := (keeperCache (reads := reads), keeper.afterRead, admission.held)
    let after : RepairState := (keeperCache (reads := reads), keeper.afterRead, seen.reachedFiles)
    finishBoundedMarkedOpen directory layout.boundedPlan layout.plan.keeperBytes.size
      seen.removeFile seen.write seen.groupedSync seen.renameFile before = .error seen.diagnostic after ∧
    seen.countedFinish layout.boundedPlan layout.plan.keeperBytes.size (before, calls) =
      .error seen.diagnostic (after, calls + 1) := by
  dsimp only [countedFinish]
  rw [layout.boundedPlan_eq_extract]
  exact ⟨finishBoundedMarkedOpen_authorizationError directory _ prepared.valid _ _ _ _ seen.syncFails,
    finishBoundedMarkedOpen_authorizationError directory _ prepared.valid _ _ _ _ (by
      simp [countCallback, seen.syncFails])⟩

/-- The real prepared-read schedule reaches that barrier with the owner
and cached directory still live. Its error keeps the reached census,
never produces an opened table, and projects the one charged group. -/
theorem stopsRecovery
    (chronology : CapturedMarkedReadCensus reads keeper)
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint)
    (prepared : Prepared retry.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    let prepare := reads.prepareFromCensus chronology.metadataRelease chronology.runs.released
      chronology.sealRelease keeper.readKeeperAt
    finishPreparedWithCensus prepare (fun plan measure =>
      finishBoundedMarkedOpen directory plan measure seen.removeFile seen.write seen.groupedSync seen.renameFile)
      admission.cache (admission.reached, admission.held) =
        .error seen.diagnostic (keeper.afterRead, seen.reachedFiles) ∧
    admission.owner ∈ keeper.afterRead.slots ∧ admission.cached ∈ keeper.afterRead.slots := by
  dsimp only
  have extent : reads.wal.keeper.calls.metadata.byteSize.toNat = (layout.keeper.bytes ++ layout.tail).size :=
    reads.wal.keeper.observesFile.extent
  have fits : layout.keeper.bytes.size ≤ reads.wal.keeper.calls.metadata.byteSize.toNat := by
    rw [extent]
    change layout.keeper.bytes.size ≤ (layout.keeper.bytes ++ layout.tail).size
    simp
  obtain ⟨opened, reached, _⟩ := reads.preparesFromCensus chronology.manifest chronology.runs selected
    chronology.marker chronology.beforeListing keeper chronology.seals chronology.offsets chronology.retained
    following prepared.newer accepted ordered keeper.readKeeperAt (keeper.reads fits)
  refine ⟨?_, keeper.ownerRetained, keeper.directoryRetained⟩
  unfold finishPreparedWithCensus
  rw [reached]
  dsimp only
  have failed := (seen.finishes prepared 0).1
  simp only [keeperCache] at failed
  rw [failed]

/-- The returned error acts on the reached lock state. Unlock success
only releases this owner, while a failed unlock returns its own cause. -/
def afterUnlock (unlock : Except IO.Error Unit) : LockedFileState FileImage :=
  match unlock with
  | .ok () => { seen.reachedFiles with owners := seen.reachedFiles.owners.set (directory.file .lock) none }
  | .error _ => seen.reachedFiles

def openDiagnostic (unlock : Except IO.Error Unit) : IO.Error :=
  match unlock with
  | .ok () => seen.diagnostic
  | .error cause => cause

def run (chronology : CapturedMarkedReadCensus reads keeper)
    (bootstrap : DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened)
    (install : DiskDirectory → DescriptorSlot → CensusDirectoryCache → Reopened →
      EStateM IO.Error CensusOpenState SegmentedSession) :
    EStateM.Result IO.Error CensusOpenState SegmentedSession :=
  admission.run fun path owner cache =>
    admission.recoverWithMarked path
      (finishPreparedWithCensus (reads.prepareFromCensus chronology.metadataRelease chronology.runs.released
        chronology.sealRelease keeper.readKeeperAt) (fun plan measure =>
          finishBoundedMarkedOpen path plan measure seen.removeFile seen.write seen.groupedSync seen.renameFile) cache)
      (bootstrap path cache) >>= install path owner cache

/-- This admitted marked open returns from the actual cleanup of the
first barrier's reached census and files. The same callback reports
determine the bounded chunk work and exact directory listing and repair
charges. The markerless worker and the installer are unreachable. -/
theorem returnsWithWork
    (chronology : CapturedMarkedReadCensus reads keeper)
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint)
    (prepared : Prepared retry.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (flat : optionalMetadataWith (admission.lookup (directory.file .wal)) (admission.reached, admission.held) =
      .ok none (admission.reached, admission.held))
    {marker : IO.FS.Metadata}
    (found : optionalMetadataWith (admission.lookup (directory.file .walBoundary))
      (admission.reached, admission.held) = .ok (some marker) (admission.reached, admission.held))
    (unlock : Except IO.Error Unit)
    (unlocked : admission.unlock admission.owner () (keeper.afterRead, seen.reachedFiles) = match unlock with
      | .ok () => .ok () (keeper.afterRead, seen.afterUnlock unlock)
      | .error cause => .error cause (keeper.afterRead, seen.afterUnlock unlock))
    (bootstrap : DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened)
    (install : DiskDirectory → DescriptorSlot → CensusDirectoryCache → Reopened →
      EStateM IO.Error CensusOpenState SegmentedSession) :
    seen.run chronology bootstrap install = .error (seen.openDiagnostic unlock) (keeper.afterRead, seen.afterUnlock unlock) ∧
    (seen.afterUnlock unlock).image = seen.reachedFiles.image ∧
    (TryLockObserves (seen.afterUnlock unlock).owners directory (.ok true) ↔ unlock = .ok ()) ∧
    reads.metadataReadRequests + reads.payloadReadRequests ≤
      (retry.image.directory.active.manifest.map ByteArray.size).getD 0 + WAL.Boundary.acquisitionLimit +
        (((checkpoint.getD (.empty, 0)).1.runs.map (·.run.bytes.size)).sum +
          (layout.range.through - layout.first) * WAL.frameSize) ∧
    reads.directoryWork.opendirCalls + reads.directoryWork.readdirCalls + reads.directoryWork.closedirCalls =
      reads.listing.scan.names.length + 3 ∧
    seen.countedFinish layout.boundedPlan layout.plan.keeperBytes.size
      ((keeperCache (reads := reads), keeper.afterRead, admission.held), 0) =
        .error seen.diagnostic ((keeperCache (reads := reads), keeper.afterRead, seen.reachedFiles), 1) := by
  obtain ⟨opened, read, closed, _⟩ := reads.directoryWork_exact
  have stopped := (seen.stopsRecovery chronology selected prepared following accepted ordered).1
  have returned : seen.run chronology bootstrap install =
      .error (seen.openDiagnostic unlock) (keeper.afterRead, seen.afterUnlock unlock) := by
    unfold run
    rw [admission.run_reachesRecovery]
    simp only [Bind.bind, EStateM.bind, admission.recoverWithMarked_selects flat found, Option.isSome_some,
      ↓reduceIte, stopped, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, EStateM.Backtrackable.restore,
      EStateM.dummyRestore, unlocked]
    cases unlock with
    | ok result =>
      cases result
      rfl
    | error cause => rfl
  refine ⟨returned, ?_, ?_, Nat.add_le_add reads.metadataReadRequests_le
    (reads.payloadReadRequests_le selected prepared following), by omega, (seen.finishes prepared 0).2⟩
  · cases unlock <;> rfl
  · cases unlock <;> simp [afterUnlock, reachedFiles, TryLockObserves, LockOwners.set, CensusOpenAdmissionReports.held]

end NativeMarkedFirstBarrierError
end Alvoki.Storage.DiskSession
