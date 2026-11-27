import Alvoki.Storage.Disk.Proofs.Collection.RetainedCollectionPowerLoss
import Alvoki.Storage.Disk.Proofs.Recovery.SegmentedRetryTrace

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- The reached collection cut, the exact names and metadata that survive
it, and the next healthy bounded-open observations. -/
structure SegmentedCollectionPowerLossReport (directory : DiskDirectory) (before : SegmentedWriterState)
    (writer descriptor : Nat) where
  cut : WalSealedUnlinkImage
  pair : DirectoryPublication.Bindings
  sealed : List WalSegment
  reached : WalSealedUnlinkTrace before.wal cut
  pairSurvives : pair ∈ cut.visible.directory.crashImages
  sealedSurvives : sealed ∈ cut.crashSealed
  reopen : BoundedReopenAttempt
  raw : HealthyBoundedWalReports directory
    ((before.owners.release (directory.file .lock) writer).set (directory.file .lock) (some descriptor))
    descriptor (cut.crash pair sealed).visible pair before.target.range.watermark before.published.durable ByteArray.empty
  liveRefs : List Nat

namespace SegmentedCollectionPowerLossReport

variable {directory : DiskDirectory} {before : SegmentedWriterState} {writer descriptor : Nat}

def survivors (report : SegmentedCollectionPowerLossReport directory before writer descriptor) : WalSegmentImage :=
  (report.cut.crash report.pair report.sealed).visible

def crashed (report : SegmentedCollectionPowerLossReport directory before writer descriptor) :
    LockedFileState FileImage :=
  ⟨report.survivors.checkpointReopenFiles report.survivors.directory none,
    before.owners.release (directory.file .lock) writer⟩

structure Valid (report : SegmentedCollectionPowerLossReport directory before writer descriptor) : Prop where
  descriptorEq : report.reopen.descriptor = descriptor
  acquired : report.reopen.acquired = .ok true
  reads : report.reopen.recover directory =
    report.raw.reopen report.reopen.removeFile report.reopen.write report.reopen.sync report.reopen.renameFile
  fresh : ∀ ref ∈ report.liveRefs, ref < report.reopen.nextRef
  syncDirectory : report.reopen.sync #[directory.path] report.crashed.image = .ok () report.crashed.image.syncDirectory
  syncKeeper : report.reopen.sync #[directory.file (.walSegment report.survivors.active.first)]
      report.crashed.image.syncDirectory = .ok () report.crashed.image.syncDirectory.syncKeeper

private def reopenedWriter (report : SegmentedCollectionPowerLossReport directory before writer descriptor)
    (installed : Installed) (final : LockedFileState FileImage) : SegmentedWriterState :=
  SegmentedWriterState.ofReopen installed report.survivors before.history before.published before.target
    before.checkpoint final

structure Installs (report : SegmentedCollectionPowerLossReport directory before writer descriptor)
    (after : SegmentedWriterState) : Prop where
  opened : ∃ session final installed,
    report.reopen.run directory report.crashed = .ok session final ∧ session.phase = .ready installed ∧
    after = report.reopenedWriter installed final

/-- Replay the concrete post-crash bounded attempt to establish the retained
writer invariant from the prior writer and the observed collection cut. -/
theorem installs (report : SegmentedCollectionPowerLossReport directory before writer descriptor)
    (observed : report.Valid) (ready : before.RetainedReady directory writer) :
    ∃ after, report.Installs after ∧ after.RetainedReady directory descriptor := by
  obtain ⟨_, session, final, after, returned, _, _, phase, files, owners, _, wal, target, history, checkpoint, _,
    durable, next⟩ := ready.openAfterCollectionPowerLoss report.reached report.pairSurvives report.sealedSurvives
      report.liveRefs observed.fresh report.raw report.reopen.unlock report.reopen.removeFile report.reopen.write
      report.reopen.sync report.reopen.renameFile observed.syncDirectory observed.syncKeeper
  have actual : report.reopen.run directory report.crashed = .ok session final := by
    unfold BoundedReopenAttempt.run
    rw [observed.descriptorEq, observed.acquired, observed.reads]
    exact returned
  have manifest := next.manifestFiles.trans (congrArg (fun image : FileImage => image.directory.project .manifest) files)
  have published : after.published = { before.published with manifest := final.image.directory.project .manifest } := by
    cases nextPub : after.published
    cases prevPub : before.published
    simp only [nextPub] at manifest
    simp only [nextPub, prevPub] at durable
    exact CheckpointPublication.Image.mk.injEq .. |>.mpr ⟨manifest, durable⟩
  have same : after = report.reopenedWriter after.installed final := by
    cases after
    simp only [reopenedWriter, SegmentedWriterState.ofReopen, SegmentedWriterState.mk.injEq, true_and]
    exact ⟨wal, history, files, published, target, checkpoint, owners⟩
  exact ⟨after, ⟨session, final, after.installed, actual, phase, same⟩, next⟩

theorem Installs.unique {report : SegmentedCollectionPowerLossReport directory before writer descriptor}
    {left right : SegmentedWriterState} (a : report.Installs left) (b : report.Installs right) : left = right := by
  obtain ⟨_, _, leftInstalled, leftOpen, leftPhase, rfl⟩ := a.opened
  obtain ⟨_, _, rightInstalled, rightOpen, rightPhase, rfl⟩ := b.opened
  obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj (leftOpen.symm.trans rightOpen)
  rw [Phase.ready.inj (leftPhase.symm.trans rightPhase)]

theorem Installs.preservesRetained {report : SegmentedCollectionPowerLossReport directory before writer descriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after) (observed : report.Valid)
    (ready : before.RetainedReady directory writer) : after.RetainedReady directory descriptor := by
  obtain ⟨_, exactEndpoint, next⟩ := report.installs observed ready
  exact exactEndpoint.unique endpoint ▸ next

theorem Installs.history {report : SegmentedCollectionPowerLossReport directory before writer descriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after) : after.history = before.history := by
  obtain ⟨_, _, _, _, _, rfl⟩ := endpoint.opened
  rfl

end SegmentedCollectionPowerLossReport
end Alvoki.Storage.DiskSession
