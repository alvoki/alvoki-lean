import Alvoki.Storage.Disk.Proofs.Read.ClientReadTrace
import Alvoki.Storage.Disk.Proofs.Bootstrap.MarkedBootstrapRetryInstallation
import Alvoki.Storage.Disk.Proofs.Bootstrap.MarkerlessBootstrapRetryInstallation

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open Sequential (SnapshotTable)
open scoped List

/-- The admitted bootstrap call returns this session and file state.
The client trace starts at the writer installed in that same session. -/
structure BootstrapClientStart (directory : DiskDirectory) (descriptor : Nat)
    (result : EStateM.Result IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession) where
  session : SegmentedSession
  final : LockedFileState WalSegmentRotation.State
  bootstrap : BootstrapReady final.image
  returned : result = .ok session final
  canonicalDirectory : session.directory = directory
  lockDescription : session.descriptor = descriptor
  installed : session.phase = .ready (bootstrap.writerState final.owners).installed
  held : final.owners.Owns directory descriptor

namespace BootstrapClientStart

variable {directory : DiskDirectory} {descriptor : Nat}
  {result : EStateM.Result IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession}

abbrev writer (start : BootstrapClientStart directory descriptor result) : SegmentedWriterState :=
  start.bootstrap.writerState start.final.owners

theorem starts (start : BootstrapClientStart directory descriptor result) (allowCollection : Bool) :
    SegmentedClientReadTrace directory descriptor start.writer allowCollection [] [] descriptor start.writer :=
  .start

/-- The same admitted start gives the existing one-replay guarantee for
any subsequent client trace, with no extra bootstrap premise. -/
theorem keyValueRefinement (start : BootstrapClientStart directory descriptor result)
    {allowCollection : Bool} {log : List DatabaseSubmissions} {reads : List RecordedSnapshotRead}
    {lastDescriptor : Nat} {last : SegmentedWriterState}
    (trace : SegmentedClientReadTrace directory descriptor start.writer allowCollection log reads lastDescriptor last) :
    ∃ reference : SnapshotTable UInt64,
      SnapshotWalReplay .empty last.history reference ∧
      DatabaseBatchRetention log last.history ∧
      log.flatMap DatabaseSubmissions.acknowledged <+ last.history ∧
      last.history <+ log.flatMap DatabaseSubmissions.submitted ∧
      ∀ read ∈ reads, read.agrees reference :=
  trace.keyValueRefinement start.bootstrap start.held

/-- Immediate and crash-selected marked retries share the same exact
returned installation. -/
theorem ofMarkedRetry (installed : BootstrapMarkedRetryOpen.Installed directory descriptor result) :
    Nonempty (BootstrapClientStart directory descriptor result) := by
  obtain ⟨session, final, returned, path, description, phase, held, ready⟩ := installed
  exact ⟨⟨session, final, ready, returned, path, description, phase, held⟩⟩

end BootstrapClientStart

private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat

/-- Either exact markerless installation, immediate or after an admitted
power loss, supplies the client trace with the same returned session. -/
theorem BootstrapClientStart.ofMarkerlessRetry
    {input : FilePath} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
    {calls : BootstrapOpenCalls (SyncHandleRouting.Cache Handle) directory before}
    {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls} {listed : BootstrapCheckedListing captured}
    {admission : OpenAdmissionReports input directory calls.slot} {allowCollection : Bool}
    (installed : listed.MarkerlessRetryInstalled admission allowCollection) :
    Nonempty (BootstrapClientStart directory calls.slot.description (calls.run admission)) := by
  obtain ⟨_, _, _, _, _, _, _, _, final, ready, returned, retained, _⟩ := installed
  exact ⟨⟨_, final, ready, returned, rfl, rfl, rfl, retained.held⟩⟩

/-- When a failed bootstrap publication left the zero marker visible,
the exact admitted marked retry supplies the client trace's empty writer. -/
theorem SegmentedClientReadTrace.fromMarkedBootstrapRetry
    {input nextInput : FilePath} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
    {calls : BootstrapOpenCalls (SyncHandleRouting.Cache Handle) directory before}
    {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}
    (listed : BootstrapCheckedListing captured) (admission : OpenAdmissionReports input directory calls.slot)
    (valid : BootstrapValid before.image) (localUnlock : calls.unlock.LocalFlock)
    (effects : BootstrapPublicationEffects calls captured.cache) {error : IO.Error}
    {after : LockedFileState WalSegmentRotation.State} (failed : calls.run admission = .error error after)
    {retry : BootstrapAdmissionCalls (SyncHandleRouting.Cache Handle) directory after}
    (nextCache : BootstrapCacheOpen retry) (nextAdmission : OpenAdmissionReports nextInput directory retry.slot)
    {metadata : IO.FS.Metadata} (marker : retry.lookup (directory.file .walBoundary) = .ok metadata)
    (visible : after.image.metadata.active.walBoundary ≠ none)
    (reports : ∀ zero : BootstrapMarkedZero after.image, Nonempty (BootstrapMarkedRetryOpen nextCache zero))
    (bootstrap : DiskDirectory → SyncHandleRouting.Cache Handle → EStateM IO.Error WalSegmentRotation.State Reopened) :
    Nonempty (BootstrapClientStart directory retry.slot.description (retry.run bootstrap nextAdmission)) :=
  BootstrapClientStart.ofMarkedRetry (listed.installsMarkedZeroAfterPublicationError admission valid localUnlock effects
    failed nextCache nextAdmission marker visible reports bootstrap)

/-- When the crash selection after the failed bootstrap keeps its zero
marker, the client trace starts at that exact marked retry's result. -/
theorem SegmentedClientReadTrace.fromMarkedBootstrapCrashRetry
    {input nextInput : FilePath} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
    {calls : BootstrapOpenCalls (SyncHandleRouting.Cache Handle) directory before}
    {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}
    (listed : BootstrapCheckedListing captured) (admission : OpenAdmissionReports input directory calls.slot)
    (valid : BootstrapValid before.image) (localUnlock : calls.unlock.LocalFlock)
    (effects : BootstrapPublicationEffects calls captured.cache) {error : IO.Error}
    {after : LockedFileState WalSegmentRotation.State} (failed : calls.run admission = .error error after)
    {pair : DirectoryPublication.Bindings} (selected : pair ∈ after.image.metadata.crashImages)
    {keeperSurvives : Bool} (keeper : after.image.successor.MaySurvive keeperSurvives)
    {retry : BootstrapAdmissionCalls (SyncHandleRouting.Cache Handle) directory
      (bootstrapPowerLoss directory after pair keeperSurvives)}
    (nextCache : BootstrapCacheOpen retry) (nextAdmission : OpenAdmissionReports nextInput directory retry.slot)
    {metadata : IO.FS.Metadata} (marker : retry.lookup (directory.file .walBoundary) = .ok metadata)
    (visible : pair.walBoundary ≠ none)
    (reports : ∀ zero : BootstrapMarkedZero (bootstrapPowerLoss directory after pair keeperSurvives).image,
      Nonempty (BootstrapMarkedRetryOpen nextCache zero))
    (bootstrap : DiskDirectory → SyncHandleRouting.Cache Handle → EStateM IO.Error WalSegmentRotation.State Reopened) :
    Nonempty (BootstrapClientStart directory retry.slot.description (retry.run bootstrap nextAdmission)) :=
  BootstrapClientStart.ofMarkedRetry (listed.installsMarkedZeroAfterPublicationCrash admission valid localUnlock effects
    failed selected keeper nextCache nextAdmission marker visible reports bootstrap)

end Alvoki.Storage.DiskSession
