import Alvoki.Storage.Disk.CheckpointObservedCompletion
import Alvoki.Storage.Disk.Proofs.Read.ClientReadTrace

namespace Alvoki.Storage.DiskSession
open WalSegmentRepair

/-- Preflight rejection leaves the same ready writer available to the
existing client ledger. Its file callbacks have no effect and all
supported reads on that session still use the same replay. -/
theorem SegmentedClientReadTrace.checkpointRejected {state : Type}
    {first : LockedFileState WalSegmentRotation.State} (bootstrap : BootstrapReady first.image)
    (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads writer before)
    (session : SegmentedSession) (phase : session.phase = .ready before.installed)
    {cause : IO.Error} (preflight : CheckpointPreflight session.phase (.error cause))
    (callbacks : CheckpointFileCallbacks state) (files : state) :
    runCheckpointWithEffects (callbacks.perform directory) (session.phase, ⟨files, before.owners⟩) =
      .error cause (session.phase, ⟨files, before.owners⟩) ∧
    GuardedClientReplay log reads before session :=
  ⟨preflight.rejected (callbacks.perform directory) _, trace.guardedReplay bootstrap held phase⟩

/-- A successful native checkpoint keeps the existing session and both
client ledgers. The installed phase, settled checkpoint and supported
reads belong to the same returned writer. -/
theorem SegmentedClientReadTrace.checkpointFromObservedSteps {state : Type}
    {first : LockedFileState WalSegmentRotation.State} (bootstrap : BootstrapReady first.image)
    (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads writer before)
    {attempt : SegmentedCheckpointReport directory before} (reports : CheckpointCompletionReports state attempt)
    (session : SegmentedSession) (sameDirectory : session.directory = directory)
    (sameDescriptor : session.descriptor = writer) (phase : session.phase = .ready before.installed) :
    ∃ after, let returned : SegmentedSession := { session with phase := .ready after.installed }
      reports.Completed session.phase writer after ∧
      returned.directory = directory ∧ returned.descriptor = writer ∧
      SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
        allowCollection log reads writer after ∧
      GuardedClientReplay log reads after returned := by
  obtain ⟨after, completed, suffix⟩ :=
    (SegmentedBatchDatabaseTrace.start (directory := directory) (initialDescriptor := writer)
      (initial := before) (allowCollection := allowCollection)).checkpointFromObservedSteps
      (trace.writes.preservesRetained (bootstrap.writerReady held).toRetained).1 reports
  have continued : SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads writer after := by
    simpa only [List.append_nil] using trace.advance suffix
  exact ⟨after, phase.symm ▸ completed, sameDirectory, sameDescriptor, continued,
    continued.guardedReplay bootstrap held rfl⟩

end Alvoki.Storage.DiskSession
