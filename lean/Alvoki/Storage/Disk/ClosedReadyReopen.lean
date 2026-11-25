import Alvoki.Storage.Disk.BatchRecoveryPrefix
import Alvoki.Storage.Disk.ClientCachedClose
import Alvoki.Storage.Disk.RotationAuthorityRetry

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

private theorem settledDirectory {image : FileImage} {target : Target} (ready : image.Ready target) :
    image.syncDirectory = image := by
  have bindings := ready.settled.trans (congrArg (fun pair => [pair]) ready.selected.symm)
  obtain ⟨visible, durable⟩ := ready.pruned
  cases image with
  | mk directory kept keeper later =>
    cases directory
    cases later
    simp_all [FileImage.syncDirectory, DirectoryPublication.Image.syncDirectory, LaterNames.syncDirectory,
      LaterNames.settled]

private theorem exactKeeperAfterEffects {target : Target} {initial after : FileImage}
    (effects : EffectTrace target initial after)
    (original : initial.keeper.Valid (· = some target.trimmed)) :
    after.keeper.Valid (· = some target.trimmed) := by
  induction effects with
  | authorized => exact original
  | unlink _ _ prior | syncPruned _ prior => exact prior
  | scratch _ prior => exact ⟨prior.hasCrashImage, prior.activeValid, prior.crashValid⟩
  | replace _ _ ran prior =>
    unfold FileImage.replacementCut at ran
    obtain ⟨keeper, applied, rfl⟩ := Option.map_eq_some_iff.mp ran
    have same := Publication.Image.execute_cut_valid prior rfl _ applied
    split <;> exact same
  | aligned _ _ _ prior =>
    exact ⟨by simp [FileImage.syncKeeper], prior.activeValid,
      fun _ chosen => (List.mem_singleton.mp chosen).trans prior.activeValid⟩
  | crash _ _ survives _ prior =>
    exact Publication.Image.settled_valid (prior.crashValid _ survives)

/-- Every failure and modeled crash after close keeps the same marker and
retained seal bytes. The selected-target condition of the retry trace is
derived from the settled writer and each reached repair's reports. -/
theorem SegmentedWriterState.RetainedReady.refinesClosedReopenPrefix {directory writer before retry}
    (ready : SegmentedWriterState.RetainedReady directory writer before)
    (reported : ReportedReopenPrefix directory before.wal.active.first
      (SegmentedCleanReopenReport.released directory before) retry) :
    BoundedReopenTrace directory (· = before.target) (SegmentedCleanReopenReport.released directory before) retry ∧
      retry.image.directory.active = before.target.pair ∧ retry.image.kept = before.files.kept ∧
      Nonempty (ClosedReadyReopenLayout before retry) ∧ retry.image.later.visible = [] := by
  let released := SegmentedCleanReopenReport.released directory before
  obtain ⟨source⟩ := ready.cleanReopenLayout
  have selection {current} (prior : BoundedReopenTrace directory (· = before.target) released current) :
      ∃ selected : ClosedReadyReopenLayout before current,
        current.image.directory.active = before.target.pair ∧ current.image.kept = before.files.kept ∧
          current.image.later.visible = [] := by
    have effect : EffectTrace source.layout.target before.files current.image :=
      source.target.symm ▸ prior.effectsAfterFixedAuthority (settledDirectory ready.resumed.ready)
    obtain ⟨layout, nextTarget, nextRange, nextFirst, nextSeals, nextKeeper, kept, nextPrepared⟩ :=
      effect.canonicalRetryLayout source.layout source.prepared
    have next : layout.target = before.target := nextTarget.trans source.target
    have initialKeeper : before.files.keeper.Valid (· = some source.layout.target.trimmed) :=
      ⟨by simp [ready.resumed.ready.keeperDurable], source.target.symm ▸ ready.resumed.ready.keeper, by
        intro bytes chosen
        rw [ready.resumed.ready.keeperDurable] at chosen
        exact source.target.symm ▸ List.mem_singleton.mp chosen⟩
    have rawBytes := Option.some.inj (layout.visible.symm.trans (exactKeeperAfterEffects effect initialKeeper).activeValid)
    change layout.keeper.bytes ++ layout.tail = source.layout.keeper.bytes at rawBytes
    rw [nextKeeper] at rawBytes
    have size := congrArg ByteArray.size rawBytes
    rw [ByteArray.size_append] at size
    have emptyTail : layout.tail = ByteArray.empty := ByteArray.size_eq_zero_iff.mp (by omega)
    refine ⟨⟨layout, next, nextKeeper.trans source.keeper, emptyTail, ?_, ?_, nextTarget.symm ▸ nextPrepared⟩,
      nextPrepared.pair.trans (congrArg Target.pair source.target), kept, effect.emptyLater ready.resumed.ready.pruned.1⟩
    · rw [nextSeals, nextKeeper, nextRange]
      exact source.descriptors
    · rw [nextRange, nextFirst]
      exact source.offsets
  have attempts : BoundedReopenTrace directory (· = before.target) released retry := reported.refines fun prior => by
    obtain ⟨selected, _, _, _⟩ := selection prior
    exact ⟨selected.layout.target, selected.layout.plan, selected.target,
      congrArg WalSegment.first selected.keeper, selected.prepared⟩
  obtain ⟨selected, pair, kept, empty⟩ := selection attempts
  exact ⟨attempts, pair, kept, ⟨selected⟩, empty⟩

/-- Close the current ready writer, then use any reported failed marked
opens before the next healthy admission. Each attempt starts at the
previous endpoint. The final held packet uses the original durable runs
and the same physical lock and directory objects. -/
theorem SegmentedClientReadTrace.reopenAfterReportedCloseRetries {input : FilePath}
    {first : LockedFileState WalSegmentRotation.State} (bootstrap : BootstrapReady first.image)
    (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads writer before)
    {cache : Cache CheckpointOpenHandle} {descriptors : DescriptorInventory}
    {causes : List IO.Error} {closeStart : CachedCloseState CheckpointOpenHandle FileImage}
    (failed : CachedCloseFailureTrace directory writer
      ⟨.ready before.installed, ⟨(cache, before.files), before.owners⟩, descriptors⟩ causes closeStart)
    (close : CachedCloseReports directory writer closeStart) (unlocked : close.result = .ok ())
    (oldDirectory : CachedCloseDirectory closeStart) {retry : LockedFileState FileImage}
    (attempts : ReportedReopenPrefix directory before.wal.active.first
      (SegmentedCleanReopenReport.released directory before) retry)
    (observe : ∀ selected : ClosedReadyReopenLayout before retry,
      ∃ opened : PrimitiveCheckpointHeldOpen input directory selected.layout before.published,
        opened.calls.bindings (directory.file .lock) = close.bindings (directory.file .lock) ∧
        opened.calls.slot.description ≠ writer ∧
        opened.held.lifetime.namespaceView.modelObject opened.held.lifetime.root =
          closeStart.descriptors.inode oldDirectory.slot.description) :
    close.run = .ok () close.finished ∧ close.finished.phase = .closed ∧
    close.finished.files = ⟨(⟨none, none, []⟩, before.files), before.owners.set (directory.file .lock) none⟩ ∧
    close.finished.descriptors = descriptors.afterDrops (close.drops .active ++ close.drops .pending ++ close.drops .directory) ∧
    retry.image.directory.active = before.target.pair ∧ retry.image.kept = before.files.kept ∧
    ∃ (selected : ClosedReadyReopenLayout before retry)
      (opened : PrimitiveCheckpointHeldOpen input directory selected.layout before.published)
      (after : SegmentedWriterState) (session : SegmentedSession) (final : LockedFileState FileImage),
      AdmittedCleanReopen (close.cleanUnlock unlocked) opened.toHeldOpen.chunkReports opened.admission after ∧
      opened.wal.operations.runWithAdmission opened.admission = .ok session final ∧
      session.directory = directory ∧ session.descriptor = opened.calls.slot.description ∧
      session.phase = .ready after.installed ∧ session.sessionRef ∉ opened.calls.liveRefs ∧
      final.owners.Owns directory session.descriptor ∧ after.files = final.image ∧ after.owners = final.owners ∧
      opened.calls.descriptors.inode opened.held.lifetime.directorySlot.description =
        descriptors.inode oldDirectory.slot.description ∧
      opened.wal.operations.reported.inventory.reports.readOptional (directory.file .manifest) =
        .ok before.target.pair.manifest ∧
      opened.wal.operations.reads.ObservesSelected directory before.target.pair.manifest before.published.durable ∧
      SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
        allowCollection log reads opened.calls.slot.description after ∧ GuardedClientReplay log reads after session := by
  obtain ⟨same, closed, _⟩ := trace.cachedClosePrefix bootstrap held failed close
  subst closeStart
  simp only [CachedCloseReports.Reached, unlocked] at closed
  obtain ⟨returned, phase, cleared, census, _⟩ := closed
  have ready := (trace.writes.preservesRetained (bootstrap.writerReady held).toRetained).1
  obtain ⟨bounded, pair, kept, ⟨selected⟩, _⟩ := ready.refinesClosedReopenPrefix attempts
  obtain ⟨opened, lock, distinct, root⟩ := observe selected
  obtain ⟨after, endpoint⟩ := ready.admitsCleanReopenAt (close.cleanUnlock unlocked) bounded selected
    opened.toHeldOpen.chunkReports opened.admission lock distinct
  obtain ⟨session, final, reopened, path, description, nextPhase, fresh, files, owners⟩ := endpoint.reopenEffect
  have owns : final.owners.Owns directory session.descriptor :=
    description.symm ▸ owners ▸ endpoint.writer.retained.held
  have manifest := congrArg DirectoryPublication.Bindings.manifest pair
  have manifestRead := opened.metadata.callbackMetadata.manifestRead.trans (congrArg Except.ok manifest)
  have selectedRuns := manifest ▸ opened.held.chunkReads
  have continued : SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads opened.calls.slot.description after := by
    change SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads opened.toHeldOpen.chunkReports.slot.description after
    simpa only [List.append_nil] using trace.advance (.cleanReopenObserved .start (close.cleanUnlock unlocked) endpoint)
  exact ⟨returned, phase, cleared, census, pair, kept, selected, opened, after, session, final,
    endpoint, reopened, path, description, nextPhase, fresh, owns, files, owners,
    opened.held.lifetime.identifiesDirectory.symm.trans root, manifestRead, selectedRuns,
    continued, continued.guardedReplay bootstrap held nextPhase⟩

end Alvoki.Storage.DiskSession
