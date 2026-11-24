import Alvoki.Storage.Disk.RotationAuthorityRetry
import Alvoki.Storage.Disk.RotationReopenTrace

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WalSegmentRotation
open WAL.Boundary (CheckpointRepresentsPrefix)

def RotationRetryReady (directory : DiskDirectory) (descriptor : Nat) (liveRefs : List Nat)
    (published : CheckpointPublication.Image) (history : List WAL.Write) (original : WalSegmentImage)
    (state : WalSegmentRotation.State) (target : Target)
    (result : EStateM.Result IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession) : Prop :=
  ∃ checkpoint table model session final,
    result = .ok session final ∧
    SelectedIntegrityCheckpoint published.durable state.metadata.active.manifest checkpoint ∧
    recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode history) = .ok table ∧
    session.directory = directory ∧ session.descriptor = descriptor ∧
    session.phase = .ready ⟨table, (checkpoint.getD (.empty, 0)).2, (WAL.encode history).size, target.first⟩ ∧
    final.image = state.settleForReopen ∧ (final.image.settledReopenImage original).Ready target ∧
    final.owners.Owns directory descriptor ∧
    table.committed.toNat = history.length ∧ table.RowBounds ∧ table.Refines model ∧
    RepresentsWalHistory history model ∧ table.pins.active = [] ∧
    session.phaseRef ≠ session.sessionRef ∧ session.phaseRef ∉ liveRefs ∧ session.sessionRef ∉ liveRefs

/-- A rotation error leaves either the original keeper or a visible empty
successor. After a finite prefix of failed opens and allowed successor
survival choices, the next healthy bounded open reads the visible layout
and fixes it by the actual directory barrier before installing the table. -/
theorem RotationReopenFailures.installs {directory : DiskDirectory}
    {image : WalSegmentImage} {history : List WAL.Write} {initial retry : LockedFileState WalSegmentRotation.State}
    (attempts : RotationReopenFailures directory image history initial retry)
    (origin : Trace image initial.image) (rotation : CanRotate image history)
    (layout : image.ReadLayout history) (valid : image.Valid history) (ordered : WAL.OrdinalsFrom 1 history)
    (published : CheckpointPublication.Image)
    (originalPairs : ∀ pair, image.Selects pair → ∃ range, pair.walRange = some range ∧
      range.through = history.length ∧
      published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history) pair.manifest)
    {descriptor nextRef : Nat} (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < nextRef)
    (acquisition : TryLockObserves retry.owners directory (.ok true)) (unlock : UnlockReport)
    (removeFile : FilePath → EStateM IO.Error WalSegmentRotation.State (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error WalSegmentRotation.State Unit)
    (sync : Array FilePath → EStateM IO.Error WalSegmentRotation.State Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error WalSegmentRotation.State Unit) :
    let wal := retry.image.settleForReopen.visible image
    let fixed := retry.image.settledReopenImage image
    ∃ selected : CanonicalKeeperLayout fixed history,
      selected.keeper = (retry.image.visible image).active ∧
      ∀ raw : HealthyBoundedWalReports directory (retry.owners.set (directory.file .lock) (some descriptor))
          descriptor wal fixed.directory.active selected.range.watermark published.durable selected.tail,
        sync #[directory.path] retry.image = .ok () retry.image.settleForReopen →
        sync #[directory.file (.walSegment selected.keeper.first)] retry.image.settleForReopen =
          .ok () retry.image.settleForReopen →
        let attempt : BoundedReopenAttempt WalSegmentRotation.State :=
          ⟨descriptor, nextRef, .ok true, unlock, raw.reports.readOptional, raw.list,
            (fun path => .ok (raw.reports.lstat path)), raw.reports.readBin, raw.readPrefix,
            removeFile, write, sync, renameFile⟩
        RotationRetryReady directory descriptor liveRefs published history image retry.image selected.target
          (attempt.run directory retry) := by
  intro wal fixed
  have trace := attempts.rotationTrace rotation layout origin
  obtain ⟨range, decoded, atEnd, accepted⟩ := originalPairs _ (trace.selectsOriginal (List.mem_cons_self ..))
  obtain ⟨stableLayout, _, active, samePair, selected, sameRange, keeper, tail, descriptors, offsets, prepared⟩ :=
    trace.settledReopenLayout rotation layout valid decoded atEnd
  refine ⟨selected, keeper.trans active, ?_⟩
  intro raw metadata keeperSync attempt
  have watermark := congrArg MarkedWalRange.watermark sameRange
  obtain ⟨checkpoint, table, model, loaded, replayed, bounded, count, committed, bounds, refines, represents, pins⟩ :=
    selected.prepareBoundedReports stableLayout keeper (watermark.symm ▸ descriptors) (watermark.symm ▸ offsets)
      rfl (samePair.symm ▸ accepted) ordered raw
  have exactBytes : selected.plan.keeperBytes = selected.keeper.bytes := by
    change selected.keeper.bytes ++ selected.tail = selected.keeper.bytes
    rw [tail, ByteArray.append_empty]
  have size : selected.plan.keeperSize = selected.keeper.bytes.size := selected.target.trimmedSize.symm
  have exactPlan : selected.boundedPlan = selected.plan := by
    unfold CanonicalKeeperLayout.boundedPlan
    rw [← exactBytes]
  have finished : finishBoundedMarkedOpen directory selected.boundedPlan selected.plan.keeperBytes.size
      removeFile write sync renameFile retry.image = .ok () retry.image.settleForReopen := by
    rw [exactPlan]
    have empty : selected.plan.newer = [] := rfl
    have aligned : selected.plan.keeperBytes.size = selected.plan.keeperSize := by rw [exactBytes, size]
    simp only [finishBoundedMarkedOpen, prepared.valid, aligned, beq_self_eq_true, Nat.le_refl, decide_true,
      Bool.and_self, ite_true, empty, List.isEmpty_nil, Bind.bind, EStateM.bind, metadata]
    exact keeperSync
  let opened : Reopened :=
    ⟨table, (checkpoint.getD (.empty, 0)).2, (WAL.encode history).size.toUInt64, selected.keeper.first⟩
  have ran : attempt.recover directory retry.image = .ok opened retry.image.settleForReopen := by
    dsimp only [BoundedReopenAttempt.recover, attempt, reopenMarkedBoundedWith]
    rw [prepareBoundedMarkedWith_liftReports, bounded]
    simp only [liftExcept, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, finished, opened]
  obtain ⟨session, final, returned, path, lock, ready, settled, _, held, separate, freshPhase, freshSession⟩ :=
    runOpenWithInstallation_ready (descriptor := descriptor) liveRefs fresh acquisition (unlock := unlock) ran
  have finalProjection : final.image.settledReopenImage image = fixed := by
    rw [settled]
    change retry.image.settleForReopen.settledReopenImage image = retry.image.settledReopenImage image
    by_cases absent : retry.image.successor = .absent <;>
      simp [WalSegmentRotation.State.settledReopenImage, WalSegmentRotation.State.settleForReopen, absent,
        DirectoryPublication.Image.syncDirectory]
  have exactKeeper : fixed.keeper.active = some selected.target.trimmed := by
    change fixed.keeper.active = some selected.keeper.bytes
    rw [selected.visible, tail, ByteArray.append_empty]
  have pairSettled : fixed.directory.crashImages = [fixed.directory.active] := by
    change (retry.image.settleForReopen.visible image).directory.crashImages =
      [(retry.image.settleForReopen.visible image).directory.active]
    rw [WalSegmentRotation.State.visible_metadata]
    rfl
  have fixedReady : fixed.Ready selected.target := ⟨prepared.pair,
    pairSettled.trans (congrArg (fun pair => [pair]) prepared.pair), exactKeeper,
    by rw [← exactKeeper]; rfl, ⟨rfl, rfl⟩⟩
  exact ⟨checkpoint, table, model, session, final, returned, samePair ▸ loaded, replayed, path, lock,
    by simpa only [opened, count, CanonicalKeeperLayout.target] using ready, settled, finalProjection.symm ▸ fixedReady,
    held, committed, bounds, refines, represents, pins, separate, freshPhase, freshSession⟩

end Alvoki.Storage.DiskSession
