import Alvoki.Storage.Disk.Proofs.Bootstrap.ObservedBootstrapRetry

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat

namespace BootstrapCheckedListing

variable {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {calls : BootstrapOpenCalls (Cache Handle) directory before}
  {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}

/-- A missing canonical marker in the captured physical root is absent
from the same complete listing used by the markerless worker. -/
theorem markerAbsentFromScan (listed : BootstrapCheckedListing captured)
    (missing : captured.view.child captured.root "WAL.commit" = none) :
    "WAL.commit" ∉ ((listed.scan.scan.entries directory.path).toList.map (·.fileName)) := by
  obtain ⟨_, names⟩ := CheckedDirectoryReadReport.scan_complete directory.path
    listed.scan.eof listed.scan.closed listed.scan.complete
  rw [listed.scan.sameRoot, listed.sameRoot, listed.sameView] at names
  intro seen
  obtain ⟨object, bound⟩ := (captured.view.namesExact captured.root "WAL.commit").mp (names.mem_iff.mp seen)
  rw [missing] at bound
  cases bound

/-- The successful retry uses the reported cache and canonical listing at
its own admitted root. The installed empty writer starts the mixed trace. -/
def MarkerlessRetryInstalled (listed : BootstrapCheckedListing captured) {input : FilePath}
    (admission : OpenAdmissionReports input directory calls.slot) (allowCollection : Bool) : Prop :=
  before.image.metadata.active.walBoundary = none ∧
  listed.lifetime.namespaceView = captured.view ∧ listed.lifetime.root = captured.root ∧
  "WAL.commit" ∉ ((listed.scan.scan.entries directory.path).toList.map (·.fileName)) ∧
  (∃ lock, captured.view.child captured.root "LOCK" = some lock ∧
    captured.bindings (directory.file .lock) = some (captured.view.modelObject lock)) ∧
  calls.openFiles directory.path before.image = .ok captured.cache before.image ∧
  calls.slot ∈ listed.scan.afterClose.slots ∧ captured.cached ∈ listed.scan.afterClose.slots ∧
  ∃ after, ∃ ready : BootstrapReady after.image,
      let writer := ready.writerState after.owners
      calls.run admission =
        .ok ⟨directory, calls.slot.description, .ready writer.installed, calls.nextRef, calls.nextRef + 1⟩ after ∧
      writer.RetainedReady directory calls.slot.description ∧
      SegmentedBatchDatabaseTrace directory calls.slot.description writer allowCollection [] calls.slot.description writer

/-- Apply the existing observed markerless worker to the admitted retry.
The inputs are reached reads and successful publication effects. The
exact installation is derived, including the mixed trace's first writer. -/
theorem installsMarkerlessRetry {input : FilePath} (listed : BootstrapCheckedListing captured)
    (admission : OpenAdmissionReports input directory calls.slot) (valid : BootstrapValid before.image)
    (missing : captured.view.child captured.root "WAL.commit" = none)
    (rotation : calls.RotationHealthy captured.cache) (marker : calls.MarkerHealthy captured.cache)
    (allowCollection : Bool) : listed.MarkerlessRetryInstalled admission allowCollection := by
  exact ⟨calls.markerAbsent.1, listed.sameView, listed.sameRoot, listed.markerAbsentFromScan missing, listed.canonicalLock,
    SegmentedBatchDatabaseTrace.fromBootstrapWithCapturedCache captured listed admission valid rotation marker
      allowCollection⟩

end BootstrapCheckedListing

/-- After a reported bootstrap publication failure, a newly admitted
markerless retry starts at the exact returned image and owner map. Its
raw marker probe and canonical listing show absence in the reached root. -/
theorem BootstrapCheckedListing.installsMarkerlessAfterPublicationError
    {input nextInput : FilePath} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
    {calls : BootstrapOpenCalls (Cache Handle) directory before}
    {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}
    (listed : BootstrapCheckedListing captured) (admission : OpenAdmissionReports input directory calls.slot)
    (valid : BootstrapValid before.image) (localUnlock : calls.unlock.LocalFlock)
    (effects : BootstrapPublicationEffects calls captured.cache) {error : IO.Error}
    {after : LockedFileState WalSegmentRotation.State} (failed : calls.run admission = .error error after)
    {retry : BootstrapOpenCalls (Cache Handle) directory after}
    {nextCache : BootstrapCacheOpen retry.toBootstrapAdmissionCalls} (nextListing : BootstrapCheckedListing nextCache)
    (nextAdmission : OpenAdmissionReports nextInput directory retry.slot)
    (missing : nextCache.view.child nextCache.root "WAL.commit" = none)
    (rotation : retry.RotationHealthy nextCache.cache) (marker : retry.MarkerHealthy nextCache.cache)
    (allowCollection : Bool) : nextListing.MarkerlessRetryInstalled nextAdmission allowCollection :=
  nextListing.installsMarkerlessRetry nextAdmission
    (listed.validAfterPublicationError admission valid localUnlock effects failed) missing rotation marker allowCollection

/-- When an admitted crash survivor of that error has no marker, its
settled image supplies the exact next markerless install. The lock is
reacquired from the crash state and the retry reports use that state. -/
theorem BootstrapCheckedListing.installsMarkerlessAfterPublicationCrash
    {input nextInput : FilePath} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
    {calls : BootstrapOpenCalls (Cache Handle) directory before}
    {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}
    (listed : BootstrapCheckedListing captured) (admission : OpenAdmissionReports input directory calls.slot)
    (valid : BootstrapValid before.image) (localUnlock : calls.unlock.LocalFlock)
    (effects : BootstrapPublicationEffects calls captured.cache) {error : IO.Error}
    {after : LockedFileState WalSegmentRotation.State} (failed : calls.run admission = .error error after)
    {pair : DirectoryPublication.Bindings} (selected : pair ∈ after.image.metadata.crashImages)
    {keeperSurvives : Bool} (keeper : after.image.successor.MaySurvive keeperSurvives)
    {retry : BootstrapOpenCalls (Cache Handle) directory (bootstrapPowerLoss directory after pair keeperSurvives)}
    {nextCache : BootstrapCacheOpen retry.toBootstrapAdmissionCalls} (nextListing : BootstrapCheckedListing nextCache)
    (nextAdmission : OpenAdmissionReports nextInput directory retry.slot)
    (missing : nextCache.view.child nextCache.root "WAL.commit" = none)
    (rotation : retry.RotationHealthy nextCache.cache) (marker : retry.MarkerHealthy nextCache.cache)
    (allowCollection : Bool) :
    pair.walBoundary = none ∧ nextListing.MarkerlessRetryInstalled nextAdmission allowCollection := by
  have reached := listed.validAfterPublicationCrash admission valid localUnlock effects failed selected keeper
  exact ⟨retry.markerAbsent.1,
    nextListing.installsMarkerlessRetry nextAdmission reached missing rotation marker allowCollection⟩

end Alvoki.Storage.DiskSession
