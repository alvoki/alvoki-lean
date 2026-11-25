import Alvoki.Storage.Disk.ClientReadTrace
import Alvoki.Storage.Disk.MarkedBootstrapRetryInstallation

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

end BootstrapClientStart

private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat

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
    Nonempty (BootstrapClientStart directory retry.slot.description (retry.run bootstrap nextAdmission)) := by
  obtain ⟨session, final, returned, path, description, installed, held, ready⟩ :=
    listed.installsMarkedZeroAfterPublicationError admission valid localUnlock effects failed
      nextCache nextAdmission marker visible reports bootstrap
  exact ⟨⟨session, final, ready, returned, path, description, installed, held⟩⟩

end Alvoki.Storage.DiskSession
