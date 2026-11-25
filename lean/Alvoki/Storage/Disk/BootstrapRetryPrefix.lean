import Alvoki.Storage.Disk.BootstrapClientTrace
import Alvoki.Storage.Disk.BootstrapKeeperDirectoryError
import Alvoki.Storage.Disk.BootstrapKeeperFileError
import Alvoki.Storage.Disk.BootstrapMarkerDetachError
import Alvoki.Storage.Disk.BootstrapMarkerDirectoryError
import Alvoki.Storage.Disk.BootstrapMarkerFlushError
import Alvoki.Storage.Disk.BootstrapMarkerOpenError
import Alvoki.Storage.Disk.BootstrapMarkerRenameError
import Alvoki.Storage.Disk.BootstrapMarkerSyncError
import Alvoki.Storage.Disk.BootstrapScratchRetry

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat
private abbrev BootstrapState := LockedFileState WalSegmentRotation.State

/-- The reached report of an unsuccessful markerless publication. A raw
fault report determines the exact returned endpoint from its own
operations. The general publication model can also certify an error when
the effects and the actual return were already reported. -/
inductive BootstrapReturnedFault {input : FilePath} {directory : DiskDirectory} {before : BootstrapState}
    {calls : BootstrapOpenCalls (Cache Handle) directory before}
    (captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls)
    (admission : OpenAdmissionReports input directory calls.slot) : BootstrapState → Prop where
  | keeperFile {listed : BootstrapCheckedListing captured} {route : BootstrapZeroKeeperOpened listed}
      (report : BootstrapKeeperFileError route) : BootstrapReturnedFault captured admission report.final
  | keeperDirectory {listed : BootstrapCheckedListing captured} {route : BootstrapZeroKeeperFilePrefix listed}
      (report : BootstrapKeeperDirectoryError route) : BootstrapReturnedFault captured admission report.final
  | markerDetach {listed : BootstrapCheckedListing captured} {keeper : BootstrapZeroKeeperRoute listed}
      (report : BootstrapMarkerDetachError keeper) : BootstrapReturnedFault captured admission report.final
  | markerOpen {listed : BootstrapCheckedListing captured} {keeper : BootstrapZeroKeeperRoute listed}
      (report : BootstrapMarkerOpenError keeper) : BootstrapReturnedFault captured admission report.final
  | markerFlush {listed : BootstrapCheckedListing captured} {keeper : BootstrapZeroKeeperRoute listed}
      (report : BootstrapMarkerFlushError keeper) : BootstrapReturnedFault captured admission report.final
  | markerSync {listed : BootstrapCheckedListing captured} {keeper : BootstrapZeroKeeperRoute listed}
      {marker : BootstrapMarkerStaging listed} {handoff : BootstrapKeeperMarkerStaging keeper marker}
      (report : BootstrapMarkerSyncError handoff) : BootstrapReturnedFault captured admission report.final
  | markerRename {listed : BootstrapCheckedListing captured} {keeper : BootstrapZeroKeeperRoute listed}
      {marker : BootstrapMarkerSynced listed}
      {handoff : BootstrapKeeperMarkerStaging keeper marker.toBootstrapMarkerStaging}
      (report : BootstrapMarkerRenameError handoff) : BootstrapReturnedFault captured admission report.final
  | markerDirectory {listed : BootstrapCheckedListing captured} {keeper : BootstrapZeroKeeperRoute listed}
      {marker : BootstrapMarkerRenamed listed} {handoff : BootstrapKeeperMarkerRename keeper marker}
      (report : BootstrapMarkerDirectoryError handoff) : BootstrapReturnedFault captured admission report.final
  | publication (listed : BootstrapCheckedListing captured) (effects : BootstrapPublicationEffects calls captured.cache)
      {cause : IO.Error} {after : BootstrapState} (returned : calls.run admission = .error cause after) :
      BootstrapReturnedFault captured admission after

/-- The failure branch derives the original admitted call's error and
bootstrap validity at the exact state after local cleanup. -/
theorem BootstrapReturnedFault.returns {input : FilePath} {directory : DiskDirectory}
    {before after : BootstrapState} {calls : BootstrapOpenCalls (Cache Handle) directory before}
    {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls} {admission : OpenAdmissionReports input directory calls.slot}
    (fault : BootstrapReturnedFault captured admission after) (valid : BootstrapValid before.image)
    (localUnlock : calls.unlock.LocalFlock) :
    ∃ cause, calls.run admission = .error cause after ∧ BootstrapValid after.image := by
  have reached {cause : IO.Error} {final : BootstrapState} {rest : Prop}
      (reported : calls.run admission = .error cause final ∧ BootstrapValid final.image ∧ rest) :
      ∃ cause, calls.run admission = .error cause final ∧ BootstrapValid final.image :=
    ⟨cause, reported.1, reported.2.1⟩
  cases fault with
  | keeperFile report => exact reached (report.returns admission valid localUnlock)
  | keeperDirectory report => exact reached (report.returns admission valid localUnlock)
  | markerDetach report => exact reached (report.returns admission valid localUnlock)
  | markerOpen report => exact reached (report.returns admission valid localUnlock)
  | markerFlush report => exact reached (report.returns admission valid localUnlock)
  | markerSync report => exact reached (report.returns admission valid localUnlock)
  | markerRename report => exact reached (report.returns admission valid localUnlock)
  | markerDirectory report => exact reached (report.returns admission valid localUnlock)
  | publication listed effects returned =>
    exact ⟨_, returned, listed.validAfterPublicationError admission valid localUnlock effects returned⟩

/-- Finite observed operations before the first installed client writer.
Each returned fault ends at its actual returned state. A crash can
choose only the file image's admitted survivors. A reference drop can
release the held owner without changing files. -/
inductive BootstrapRetryPrefix (directory : DiskDirectory) (initial : BootstrapState) : BootstrapState → Prop where
  | start : BootstrapRetryPrefix directory initial initial
  | returnedFault {input : FilePath} {before after : BootstrapState}
      (prior : BootstrapRetryPrefix directory initial before)
      {calls : BootstrapOpenCalls (Cache Handle) directory before}
      {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}
      {admission : OpenAdmissionReports input directory calls.slot}
      (fault : BootstrapReturnedFault captured admission after) (localUnlock : calls.unlock.LocalFlock) :
      BootstrapRetryPrefix directory initial after
  | markedAuthorizationError {input : FilePath} {before : BootstrapState}
      (prior : BootstrapRetryPrefix directory initial before)
      {retry : BootstrapAdmissionCalls (Cache Handle) directory before} {captured : BootstrapCacheOpen retry}
      {zero : BootstrapMarkedZero before.image} (fault : BootstrapMarkedAuthorizationError captured zero)
      (admission : OpenAdmissionReports input directory retry.slot)
      {metadata : IO.FS.Metadata} (returned : retry.lookup (directory.file .walBoundary) = .ok metadata)
      (bootstrap : DiskDirectory → Cache Handle → EStateM IO.Error WalSegmentRotation.State Reopened) :
      BootstrapRetryPrefix directory initial fault.final
  | dropped {before : BootstrapState} {description : Nat}
      (prior : BootstrapRetryPrefix directory initial before) (owned : before.owners.Owns directory description)
      (references : HeldLockReferences description) (drops : List LockReferenceDrop) :
      BootstrapRetryPrefix directory initial (references.afterFileDrops drops directory before)
  | powerLoss {before : BootstrapState} {pair : DirectoryPublication.Bindings} {keeperSurvives : Bool}
      (prior : BootstrapRetryPrefix directory initial before) (selected : pair ∈ before.image.metadata.crashImages)
      (keeper : before.image.successor.MaySurvive keeperSurvives) :
      BootstrapRetryPrefix directory initial (bootstrapPowerLoss directory before pair keeperSurvives)
  | survivingMarkerFlush {input : FilePath} {before : BootstrapState}
      (prior : BootstrapRetryPrefix directory initial before)
      {calls : BootstrapOpenCalls (Cache Handle) directory before}
      {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls} {listed : BootstrapCheckedListing captured}
      {keeper : BootstrapZeroKeeperRoute listed} {source : BootstrapMarkerFlushError keeper}
      (survivor : BootstrapMarkerFlushSurvivor source) (admission : OpenAdmissionReports input directory calls.slot)
      (localUnlock : calls.unlock.LocalFlock) :
      BootstrapRetryPrefix directory initial survivor.state

theorem BootstrapRetryPrefix.preservesValid {directory : DiskDirectory} {initial after : BootstrapState}
    (attempts : BootstrapRetryPrefix directory initial after) (valid : BootstrapValid initial.image) :
    BootstrapValid after.image := by
  induction attempts with
  | start => exact valid
  | returnedFault _ fault localUnlock healthy =>
    obtain ⟨_, _, validAfter⟩ := fault.returns healthy localUnlock
    exact validAfter
  | markedAuthorizationError _ fault admission returned bootstrap healthy =>
    exact (fault.returns admission healthy returned bootstrap).2
  | dropped _ _ _ _ healthy => exact healthy
  | powerLoss _ selected keeper healthy => exact healthy.crash selected keeper
  | survivingMarkerFlush _ survivor admission localUnlock healthy =>
    exact (survivor.afterError admission healthy localUnlock).2.1

/-- A fresh managed image establishes the retry invariant even if the
prefix ends before a writer has ever been installed. -/
theorem BootstrapRetryPrefix.validFromEmpty {directory : DiskDirectory} {initial after : BootstrapState}
    (attempts : BootstrapRetryPrefix directory initial after)
    (empty : initial.image = ⟨DirectoryPublication.Image.settled ⟨none, none⟩, .absent⟩) :
    BootstrapValid after.image :=
  attempts.preservesValid (empty.symm ▸ bootstrap_fresh)

/-- The final admitted attempt has either checked marker absence and
reported a complete bootstrap publication, or observed the existing
canonical marker and reported both marked recovery barriers. Each
constructor uses the same reached bootstrap state. -/
inductive BootstrapRetryFinish (directory : DiskDirectory) (before : BootstrapState) :
    Nat → EStateM.Result IO.Error BootstrapState SegmentedSession → Prop where
  | markerless {input : FilePath} {calls : BootstrapOpenCalls (Cache Handle) directory before}
      {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}
      (listed : BootstrapCheckedListing captured) (admission : OpenAdmissionReports input directory calls.slot)
      (missing : captured.view.child captured.root "WAL.commit" = none)
      (rotation : calls.RotationHealthy captured.cache) (marker : calls.MarkerHealthy captured.cache) :
      BootstrapRetryFinish directory before calls.slot.description (calls.run admission)
  | marked {input : FilePath} {calls : BootstrapAdmissionCalls (Cache Handle) directory before}
      (captured : BootstrapCacheOpen calls) (admission : OpenAdmissionReports input directory calls.slot)
      {metadata : IO.FS.Metadata} (returned : calls.lookup (directory.file .walBoundary) = .ok metadata)
      (visible : before.image.metadata.active.walBoundary ≠ none)
      (reads : ∀ zero : BootstrapMarkedZero before.image, Nonempty (BootstrapMarkedRetryOpen captured zero))
      (bootstrap : DiskDirectory → Cache Handle → EStateM IO.Error WalSegmentRotation.State Reopened) :
      BootstrapRetryFinish directory before calls.slot.description (calls.run bootstrap admission)

/-- Start the same client execution from the exact returned markerless
or marked attempt after any finite supported fault and crash prefix from
the empty managed image. Successful next I/O comes from the final
attempt's reports. -/
theorem BootstrapRetryPrefix.installsFromEmpty {directory : DiskDirectory} {initial before : BootstrapState}
    {descriptor : Nat} {result : EStateM.Result IO.Error BootstrapState SegmentedSession}
    (attempts : BootstrapRetryPrefix directory initial before)
    (empty : initial.image = ⟨DirectoryPublication.Image.settled ⟨none, none⟩, .absent⟩)
    (finish : BootstrapRetryFinish directory before descriptor result) :
    Nonempty (BootstrapClientStart directory descriptor result) := by
  have valid := attempts.validFromEmpty empty
  cases finish with
  | markerless listed admission missing rotation marker =>
    exact BootstrapClientStart.ofMarkerlessRetry
      (listed.installsMarkerlessRetry admission valid missing rotation marker false)
  | marked captured admission returned visible reads bootstrap =>
    obtain ⟨observed⟩ := reads (valid.markedZero visible)
    exact BootstrapClientStart.ofMarkedRetry (observed.installs admission valid (.present visible returned) bootstrap)

end Alvoki.Storage.DiskSession
