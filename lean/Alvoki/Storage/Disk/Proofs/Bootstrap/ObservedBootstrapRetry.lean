import Alvoki.Storage.Disk.Proofs.Bootstrap.ObservedBootstrapFailure

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

private abbrev BootstrapHandle := DescriptorInventory × DescriptorSlot × Nat

/-- The next locked marker probe observes the canonical entry in the
exact reached image. Only the raw ENOENT result selects its absence. -/
inductive BootstrapRetryMarker {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
    (calls : BootstrapAdmissionCalls (Cache BootstrapHandle) directory before) : Prop where
  | absent {name message : String}
      (visible : before.image.metadata.active.walBoundary = none)
      (returned : calls.lookup (directory.file .walBoundary) = .error (.noFileOrDirectory name 2 message))
  | present {metadata : IO.FS.Metadata}
      (visible : before.image.metadata.active.walBoundary ≠ none)
      (returned : calls.lookup (directory.file .walBoundary) = .ok metadata)

/-- The admitted call chooses its worker from the visible canonical marker
and passes the same captured cache and acquired lock to that worker. -/
def BootstrapCacheOpen.RetrySelection
    {input : FilePath} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
    {calls : BootstrapAdmissionCalls (Cache BootstrapHandle) directory before}
    (captured : BootstrapCacheOpen calls) (admission : OpenAdmissionReports input directory calls.slot)
    (bootstrap : DiskDirectory → Cache BootstrapHandle → EStateM IO.Error WalSegmentRotation.State Reopened) : Prop :=
    before.owners (directory.file .lock) = none ∧ before.image.metadata.active.manifest = none ∧
    ((before.image.metadata.active.walBoundary = none ∧
        calls.run bootstrap admission = runOpenWithInstallation directory calls.slot.description calls.nextRef (.ok true)
          calls.unlock (bootstrap directory captured.cache) before) ∨
      (before.image.metadata.active.walBoundary = some (WAL.Boundary.encode 0) ∧ before.image.successor = .durable ∧
        calls.run bootstrap admission = runOpenWithInstallation directory calls.slot.description calls.nextRef (.ok true)
          calls.unlock (calls.marked directory captured.cache) before))

/-- With a surviving zero marker, the next admitted open enters marked
recovery with a durable empty segment. With the marker absent, it enters
markerless initialization. The equations cover success and error. -/
theorem BootstrapCacheOpen.retrySelects
    {input : FilePath} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
    {calls : BootstrapAdmissionCalls (Cache BootstrapHandle) directory before}
    (captured : BootstrapCacheOpen calls) (admission : OpenAdmissionReports input directory calls.slot)
    (valid : BootstrapValid before.image) (marker : BootstrapRetryMarker calls)
    (bootstrap : DiskDirectory → Cache BootstrapHandle → EStateM IO.Error WalSegmentRotation.State Reopened) :
    captured.RetrySelection admission bootstrap := by
  obtain ⟨manifest, selected⟩ := valid.nextSelection
  have vacant : before.owners (directory.file .lock) = none :=
    calls.acquisition calls.acquired
  refine ⟨vacant, manifest, ?_⟩
  cases marker with
  | absent visible returned =>
    exact .inl ⟨visible, calls.runSelected bootstrap admission captured.captures.1 (marker := none)
      (by simp [optionalMetadataWith, Bind.bind, EStateM.bind, returned, Pure.pure, EStateM.pure])⟩
  | @present metadata visible returned =>
    obtain ⟨zero, durable⟩ := selected.resolve_left visible
    exact .inr ⟨zero, durable, calls.runSelected bootstrap admission captured.captures.1 (marker := some metadata)
      (by simp [optionalMetadataWith, Bind.bind, EStateM.bind, returned, Pure.pure, EStateM.pure])⟩

/-- The next admitted attempt uses the exact state returned by publication
failure and local cleanup. A successful next lock grant requires the prior
owner to have been cleared. -/
theorem BootstrapCheckedListing.retryAfterPublicationError
    {input nextInput : FilePath} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
    {calls : BootstrapOpenCalls (Cache BootstrapHandle) directory before}
    {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}
    (listed : BootstrapCheckedListing captured) (admission : OpenAdmissionReports input directory calls.slot)
    (valid : BootstrapValid before.image) (localUnlock : calls.unlock.LocalFlock)
    (effects : BootstrapPublicationEffects calls captured.cache) {error : IO.Error}
    {after : LockedFileState WalSegmentRotation.State} (failed : calls.run admission = .error error after)
    {retry : BootstrapAdmissionCalls (Cache BootstrapHandle) directory after}
    (nextCache : BootstrapCacheOpen retry) (nextAdmission : OpenAdmissionReports nextInput directory retry.slot)
    (nextMarker : BootstrapRetryMarker retry)
    (bootstrap : DiskDirectory → Cache BootstrapHandle → EStateM IO.Error WalSegmentRotation.State Reopened) :
    nextCache.RetrySelection nextAdmission bootstrap :=
  nextCache.retrySelects nextAdmission (listed.validAfterPublicationError admission valid localUnlock effects failed)
    nextMarker bootstrap

/-- A reported power-loss survivor has its selected metadata settled.
The empty segment can survive if the preceding binding permits it. -/
def bootstrapPowerLoss (directory : DiskDirectory) (before : LockedFileState WalSegmentRotation.State)
    (pair : DirectoryPublication.Bindings) (keeperSurvives : Bool) : LockedFileState WalSegmentRotation.State :=
  ⟨⟨.settled pair, if keeperSurvives then .durable else .absent⟩,
    before.owners.set (directory.file .lock) none⟩

/-- Either retry route starts from the same admitted crash selection of
the exact failed publication's returned file image. -/
theorem BootstrapCheckedListing.validAfterPublicationCrash
    {input : FilePath} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
    {calls : BootstrapOpenCalls (Cache BootstrapHandle) directory before}
    {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}
    (listed : BootstrapCheckedListing captured) (admission : OpenAdmissionReports input directory calls.slot)
    (valid : BootstrapValid before.image) (localUnlock : calls.unlock.LocalFlock)
    (effects : BootstrapPublicationEffects calls captured.cache) {error : IO.Error}
    {after : LockedFileState WalSegmentRotation.State} (failed : calls.run admission = .error error after)
    {pair : DirectoryPublication.Bindings} (selected : pair ∈ after.image.metadata.crashImages)
    {keeperSurvives : Bool} (keeper : after.image.successor.MaySurvive keeperSurvives) :
    BootstrapValid (bootstrapPowerLoss directory after pair keeperSurvives).image :=
  (listed.validAfterPublicationError admission valid localUnlock effects failed).crash selected keeper

end Alvoki.Storage.DiskSession
