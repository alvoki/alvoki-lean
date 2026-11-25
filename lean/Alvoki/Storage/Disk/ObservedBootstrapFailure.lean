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

/-- If segment-zero creation or marker publication fails after admission,
the same directory cache and acquired lock reach that publication attempt.
Cleanup returns the exact reached image. A failed local unlock takes
precedence and retains ownership. The image remains eligible for the
bootstrap or zero-marker path, according to its reached manifest and marker. -/
theorem BootstrapCheckedListing.publicationError
    {input : FilePath} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
    {calls : BootstrapOpenCalls (Cache BootstrapHandle) directory before} {captured : BootstrapCacheOpen calls}
    (listed : BootstrapCheckedListing captured) (admission : OpenAdmissionReports input directory calls.slot)
    (valid : BootstrapValid before.image) (localUnlock : calls.unlock.LocalFlock)
    (rotation : WalSegmentRotation.EffectReports (WalSegmentRotation.performPaths directory 0
      (calls.createEmpty captured.cache) (fun path => calls.sync captured.cache #[path])))
    (marker : BootstrapMarkerReports (Publication.performReplacement
      (calls.write captured.cache · (WAL.Boundary.encode 0)) (calls.sync captured.cache) calls.renameFile
      (directory.file .stagedWalBoundary) directory.path (fun _ => directory.file .walBoundary) #[])) :
    let publication := bootstrapEmptyWith directory before.image.observeSuccessor (calls.createEmpty captured.cache)
      (calls.write captured.cache) (calls.sync captured.cache) calls.renameFile
    calls.slot ∈ listed.scan.afterClose.slots ∧ captured.cached ∈ listed.scan.afterClose.slots ∧
    match publication before.image with
    | .ok _ _ => True
    | .error cause reached =>
      calls.run admission = (match calls.unlock with
        | .success => .error cause ⟨reached, before.owners.set (directory.file .lock) none⟩
        | .failure cleanup _ =>
          .error cleanup ⟨reached, before.owners.set (directory.file .lock) (some calls.slot.description)⟩) ∧
      BootstrapValid reached ∧ reached.metadata.active.manifest = none ∧
      (reached.metadata.active.walBoundary = none ∨
        (reached.metadata.active.walBoundary = some (WAL.Boundary.encode 0) ∧ reached.successor = .durable)) := by
  intro publication
  refine ⟨listed.retained.1, listed.retained.2.1, ?_⟩
  cases returned : publication before.image with
  | ok _ _ => trivial
  | error cause reached =>
    have worker : calls.bootstrapAt directory captured.cache before.image = .error cause reached :=
      (calls.reachesPublication captured.cache listed.entries.1 listed.entries.2).trans returned
    have exactRun := runOpenWithInstallation_acquiredRecoveryError directory calls.slot.description calls.nextRef
      calls.unlock (calls.bootstrapAt directory captured.cache) before worker
    have safe := bootstrapEmptyWith_safe directory before.image valid before.image.observeSuccessor rfl
      (calls.createEmpty captured.cache) (calls.write captured.cache) (calls.sync captured.cache) calls.renameFile
      rotation marker
    change (match publication before.image with
      | .ok reopened after => reopened = ⟨.empty, 0, 0, 0⟩ ∧ BootstrapReady after
      | .error _ after => BootstrapValid after) at safe
    rw [returned] at safe
    refine ⟨?_, safe, safe.nextSelection⟩
    rw [calls.runMarkerless admission captured.captures.1, exactRun]
    cases outcome : calls.unlock with
    | success => rfl
    | failure cleanup released =>
      have retained : released = false := by simpa [outcome, UnlockReport.LocalFlock] using localUnlock
      subst released
      rfl

end Alvoki.Storage.DiskSession
