import Alvoki.Storage.Disk.ClientReadTrace
import Alvoki.Storage.Disk.WalSealedInodeLifetime

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- The healthy collection dispatcher settles the visible names. An
already absent seal stays absent even when the retry does not select it. -/
theorem SegmentedCollectionReport.reclaimsOnSuccess {directory : DiskDirectory}
    {before : SegmentedWriterState} (report : SegmentedCollectionReport directory before)
    {remaining : WalSealedUnlinkImage} (returned : report.run = .ok () remaining) {first : Nat}
    (eligible : first ∈ report.offsets ∨ first ∉ before.wal.sealed.map WalSegment.first) :
    remaining.DurablyAbsent first := by
  let initial := WalSealedUnlinkImage.start before.wal
  have executed := (WalSealedUnlinkTrace.start (initial := before.wal)).runPaths directory report.offsets
    report.approved report.removeFile report.syncDirectory report.effects
  dsimp only at executed
  change RunCollection.run report.offsets
    (WalSealedUnlinkImage.performPaths directory report.removeFile report.syncDirectory) initial =
    .ok () remaining at returned
  rw [returned] at executed
  exact executed.1 ▸ initial.completeSealed_absent report.offsets eligible

/-- A seal hidden by the failed pass is already durably absent once the
bounded opener finishes its directory barrier. The later collector uses
this exact namespace, keeps the same installed table and introduces no
write. The caller supplies the healthy final open and retry reports. -/
theorem SegmentedClientReadTrace.reopenAndCollectHiddenSeal
    {directory : DiskDirectory} {initialDescriptor writer descriptor : Nat} {before : SegmentedWriterState}
    {first : LockedFileState WalSegmentRotation.State} {log : List DatabaseSubmissions}
    {reads : List RecordedSnapshotRead}
    (bootstrap : BootstrapReady first.image) (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      true log reads writer before)
    (reopen : SegmentedCollectionReopenReport directory before writer descriptor) (observed : reopen.Valid)
    (sizes : SizedCheckpointRunReports directory reopen.raw.reports
      reopen.pending.image.visible.directory.active.manifest before.published.durable)
    (cached : CachedWalFileReports directory reopen.raw.reports reopen.pending.image.visible
      before.target.range.watermark ByteArray.empty)
    {sealOffset : Nat} (covered : sealOffset ∈ before.wal.collectionOffsets)
    (hidden : sealOffset ∉ reopen.reached.visible.sealed.map WalSegment.first)
    (retry : ∀ reopened, reopen.Installs reopened → reopened.RetainedReady directory descriptor →
      ∃ (collect : SegmentedCollectionReport directory reopened) (remaining : WalSealedUnlinkImage),
        collect.run = .ok () remaining) :
    ∃ (reopened : SegmentedWriterState) (session : SegmentedSession)
      (final : LockedFileState (FileImage × WalSealedUnlinkImage))
      (collect : SegmentedCollectionReport directory reopened) (remaining : WalSealedUnlinkImage),
      let after := reopened.afterWalCollection remaining
      reopen.Installs reopened ∧
      runOpenWithInstallation directory reopen.reopen.descriptor reopen.reopen.nextRef reopen.reopen.acquired
        reopen.reopen.unlock (reopen.reopenCachedWithNamespace sizes cached)
        ⟨(reopen.files.image, reopen.pending.image), reopen.pending.owners⟩ = .ok session final ∧
      session.descriptor = descriptor ∧ session.phase = .ready after.installed ∧
      final.image.1 = reopened.files ∧ final.owners = after.owners ∧
      final.image.2 = WalSealedUnlinkImage.start reopened.wal ∧ final.image.2.DurablyAbsent sealOffset ∧
      sealOffset ∉ collect.offsets ∧ collect.runFrom final.image.2 = .ok () remaining ∧
      remaining = WalSealedUnlinkImage.start after.wal ∧ remaining.DurablyAbsent sealOffset ∧
      sealOffset ≠ after.wal.active.first ∧ after.wal.active = before.wal.active ∧
      after.history = before.history ∧ after.checkpoint = before.checkpoint ∧
      after.RetainedReady directory descriptor ∧ GuardedClientReplay log reads after session := by
  let initialReady := (bootstrap.writerReady held).toRetained
  have beforeReady := (trace.writes.preservesRetained initialReady).1
  obtain ⟨namespaceTrace, reopened, session, final, installed, returned, phase, files, owners, settled, _, _, _,
    history, _, checkpoint, _, ready, asStarted, exactDescriptor⟩ :=
    reopen.installsCachedWithNamespace observed beforeReady sizes cached
  have originalDir := (reopen.failed.keepsNamespace beforeReady).2
  have visible := reopen.attempts.keepsVisible (by
    change reopen.reached.visible.directory.crashImages = [reopen.reached.visible.directory.active]
    rw [originalDir]
    exact beforeReady.walDirectorySettled)
  change reopen.pending.image.visible = reopen.reached.visible at visible
  have pendingHidden : sealOffset ∉ reopen.pending.image.visible.sealed.map WalSegment.first := visible ▸ hidden
  have absentAtOpen : final.image.2.DurablyAbsent sealOffset :=
    settled ▸ reopen.pending.image.completeSealed_absent [] (.inr pendingHidden)
  have missing : sealOffset ∉ reopened.wal.sealed.map WalSegment.first := by
    simpa only [asStarted, WalSealedUnlinkImage.start] using absentAtOpen.1
  obtain ⟨collect, remaining, collected⟩ := retry reopened installed ready
  have skipped : sealOffset ∉ collect.offsets := by
    intro planned
    obtain ⟨segment, present, offset⟩ := (ready.layout.collectionOffsets_approved (collect.approved sealOffset planned)).1
    exact missing (List.mem_map.mpr ⟨segment, present, offset⟩)
  let after := reopened.afterWalCollection remaining
  have collectedReport : collect.Installs after := ⟨remaining, collected, rfl⟩
  obtain ⟨afterReady, _, active, sameInstalled, _, _, afterOwners, finalCollection⟩ := collectedReport.outcome ready
  obtain ⟨settledImage, returnedAgain, _, surviving⟩ := finalCollection
  have sameResult := (EStateM.Result.ok.inj (returnedAgain.symm.trans collected)).2
  subst settledImage
  have remainder : remaining = WalSealedUnlinkImage.start after.wal := by
    cases remaining with
    | mk visible _ => exact congrArg (WalSealedUnlinkImage.mk visible) surviving
  have preserved := collect.reclaimsOnSuccess collected (.inr missing)
  have sameActive := (namespaceTrace.projects beforeReady.layout).1.keepsActive
  rw [← settled, asStarted] at sameActive
  change reopened.wal.active = before.wal.active at sameActive
  obtain ⟨⟨segment, member, offset⟩, eligible⟩ := beforeReady.layout.collectionOffsets_approved covered
  have distinct : sealOffset ≠ after.wal.active.first := by
    rw [active, sameActive, ← offset]
    exact (eligible segment member offset).notActive
  let sameHistory : after.history = before.history := history
  let afterPhase : session.phase = .ready after.installed := phase.trans (congrArg Phase.ready sameInstalled.symm)
  let maintenance : SegmentedDatabaseTrace directory writer before true [] descriptor after :=
    .collection rfl (.collectionReopen rfl .start reopen observed installed) collect collectedReport
  let continued := trace.advance (.ordinary .start maintenance)
  obtain ⟨reference, replay, _, acknowledged, submitted, earlierReads, laterReads⟩ :=
    continued.guardedReplay bootstrap held afterPhase
  obtain ⟨_, retained, fromStart, oldRetention⟩ := trace.writes.preservesRetained initialReady
  change before.history = [] ++ retained at fromStart
  have retention : DatabaseBatchRetention log after.history := by
    rw [sameHistory, fromStart, List.nil_append]
    exact oldRetention
  have guarded : GuardedClientReplay log reads after session := by
    refine ⟨reference, replay, retention, ?_, ?_, earlierReads, laterReads⟩
    · simpa [DatabaseSubmissions.acknowledged] using acknowledged
    · simpa [DatabaseSubmissions.submitted] using submitted
  refine ⟨reopened, session, final, collect, remaining, installed, returned, exactDescriptor, afterPhase, files,
    owners.trans afterOwners.symm, asStarted, absentAtOpen, skipped, ?_, remainder, preserved, distinct,
    active.trans sameActive, sameHistory, checkpoint, afterReady, guarded⟩
  rw [asStarted]
  exact collected

end Alvoki.Storage.DiskSession
