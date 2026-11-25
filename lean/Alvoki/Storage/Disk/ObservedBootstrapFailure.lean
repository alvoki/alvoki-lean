import Alvoki.Storage.Disk.ObservedBootstrapCache
import Alvoki.Storage.Disk.BoundedOpenReadFailure

namespace Alvoki.Storage.WalSegmentRepair

/-- An admitted bootstrap image selects markerless initialization, or a
zero marker with the durable empty segment it names. The same statement
applies to any admitted power-loss survivor by `BootstrapValid.crash`. -/
theorem BootstrapValid.nextSelection {image : WalSegmentRotation.State} (valid : BootstrapValid image) :
    image.metadata.active.manifest = none ∧
      (image.metadata.active.walBoundary = none ∨
        (image.metadata.active.walBoundary = some (WAL.Boundary.encode 0) ∧ image.successor = .durable)) := by
  obtain ⟨manifest, absent | zero⟩ := valid.metadata.activeValid
  · exact ⟨manifest, .inl absent⟩
  · exact ⟨manifest, .inr ⟨zero, valid.marked _ valid.metadata.activeMaySurvive (by simp [zero])⟩⟩

end Alvoki.Storage.WalSegmentRepair

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

private abbrev BootstrapHandle := DescriptorInventory × DescriptorSlot × Nat

/-- The primitive filesystem effects of publishing a bootstrap image with
the exact captured cache. -/
structure BootstrapPublicationEffects {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
    (calls : BootstrapOpenCalls (Cache BootstrapHandle) directory before) (cache : Cache BootstrapHandle) : Prop where
  rotation : WalSegmentRotation.EffectReports (WalSegmentRotation.performPaths directory 0
    (calls.createEmpty cache) (fun path => calls.sync cache #[path]))
  marker : BootstrapMarkerReports (Publication.performReplacement
    (calls.write cache · (WAL.Boundary.encode 0)) (calls.sync cache) calls.renameFile
    (directory.file .stagedWalBoundary) directory.path (fun _ => directory.file .walBoundary) #[])

private abbrev publish {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
    (calls : BootstrapOpenCalls (Cache BootstrapHandle) directory before) (cache : Cache BootstrapHandle) :=
  bootstrapEmptyWith directory before.image.observeSuccessor (calls.createEmpty cache)
    (calls.write cache) (calls.sync cache) calls.renameFile

/-- An admitted markerless worker error preserves its exact reached
image through the local lock cleanup. -/
theorem BootstrapOpenCalls.runWorkerError
    {input : FilePath} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
    {calls : BootstrapOpenCalls (Cache BootstrapHandle) directory before}
    (captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls)
    (admission : OpenAdmissionReports input directory calls.slot) (localUnlock : calls.unlock.LocalFlock)
    {cause : IO.Error} {reached : WalSegmentRotation.State}
    (worker : calls.bootstrapAt directory captured.cache before.image = .error cause reached) :
    calls.run admission = (match calls.unlock with
      | .success => .error cause ⟨reached, before.owners.set (directory.file .lock) none⟩
      | .failure cleanup _ =>
        .error cleanup ⟨reached, before.owners.set (directory.file .lock) (some calls.slot.description)⟩) := by
  have exactRun := runOpenWithInstallation_acquiredRecoveryError directory calls.slot.description calls.nextRef
    calls.unlock (calls.bootstrapAt directory captured.cache) before worker
  rw [calls.runMarkerless admission captured.captures.1, exactRun]
  cases outcome : calls.unlock with
  | success => rfl
  | failure cleanup released =>
    have retained : released = false := by simpa [outcome, UnlockReport.LocalFlock] using localUnlock
    subst released
    rfl

/-- If segment-zero creation or marker publication fails after admission,
the same directory cache and acquired lock reach that publication attempt.
Cleanup returns the exact reached image. A failed local unlock takes
precedence and retains ownership. The image remains eligible for the
bootstrap or zero-marker path, according to its reached manifest and marker. -/
theorem BootstrapCheckedListing.publicationError
    {input : FilePath} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
    {calls : BootstrapOpenCalls (Cache BootstrapHandle) directory before}
    {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}
    (listed : BootstrapCheckedListing captured) (admission : OpenAdmissionReports input directory calls.slot)
    (valid : BootstrapValid before.image) (localUnlock : calls.unlock.LocalFlock)
    (effects : BootstrapPublicationEffects calls captured.cache) :
    calls.slot ∈ listed.scan.afterClose.slots ∧ captured.cached ∈ listed.scan.afterClose.slots ∧
    match publish calls captured.cache before.image with
    | .ok _ _ => True
    | .error cause reached =>
      calls.run admission = (match calls.unlock with
        | .success => .error cause ⟨reached, before.owners.set (directory.file .lock) none⟩
        | .failure cleanup _ =>
          .error cleanup ⟨reached, before.owners.set (directory.file .lock) (some calls.slot.description)⟩) ∧
      BootstrapValid reached ∧ reached.metadata.active.manifest = none ∧
      (reached.metadata.active.walBoundary = none ∨
        (reached.metadata.active.walBoundary = some (WAL.Boundary.encode 0) ∧ reached.successor = .durable)) := by
  refine ⟨listed.retained.1, listed.retained.2.1, ?_⟩
  cases returned : publish calls captured.cache before.image with
  | ok _ _ => trivial
  | error cause reached =>
    have worker : calls.bootstrapAt directory captured.cache before.image = .error cause reached :=
      (calls.reachesPublication captured.cache listed.entries.1 listed.entries.2).trans returned
    have safe := bootstrapEmptyWith_safe directory before.image valid before.image.observeSuccessor rfl
      (calls.createEmpty captured.cache) (calls.write captured.cache) (calls.sync captured.cache) calls.renameFile
      effects.rotation effects.marker
    change (match publish calls captured.cache before.image with
      | .ok reopened after => reopened = ⟨.empty, 0, 0, 0⟩ ∧ BootstrapReady after
      | .error _ after => BootstrapValid after) at safe
    rw [returned] at safe
    exact ⟨BootstrapOpenCalls.runWorkerError captured admission localUnlock worker, safe, safe.nextSelection⟩

/-- The exact state returned by the failed admitted open supplies the
bootstrap invariant for the next attempt, even if cleanup changed the error. -/
theorem BootstrapCheckedListing.validAfterPublicationError
    {input : FilePath} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
    {calls : BootstrapOpenCalls (Cache BootstrapHandle) directory before}
    {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}
    (listed : BootstrapCheckedListing captured) (admission : OpenAdmissionReports input directory calls.slot)
    (valid : BootstrapValid before.image) (localUnlock : calls.unlock.LocalFlock)
    (effects : BootstrapPublicationEffects calls captured.cache) {error : IO.Error}
    {after : LockedFileState WalSegmentRotation.State} (failed : calls.run admission = .error error after) :
    BootstrapValid after.image := by
  have report := (listed.publicationError admission valid localUnlock effects).2.2
  cases publication : publish calls captured.cache before.image with
  | ok opened reached =>
    have finished : calls.bootstrapAt directory captured.cache before.image = .ok opened reached :=
      (calls.reachesPublication captured.cache listed.entries.1 listed.entries.2).trans publication
    rw [calls.runMarkerless admission captured.captures.1, runOpenWithInstallation_outcome,
      runOpenWithImage_acquired, finished] at failed
    cases failed
  | error cause reached =>
    rw [publication] at report
    rw [report.1] at failed
    have image : after.image = reached := by
      cases unlock : calls.unlock <;>
        simp only [unlock] at failed <;>
        exact (congrArg LockedFileState.image (EStateM.Result.error.inj failed).2).symm
    exact image.symm ▸ report.2.1

end Alvoki.Storage.DiskSession
