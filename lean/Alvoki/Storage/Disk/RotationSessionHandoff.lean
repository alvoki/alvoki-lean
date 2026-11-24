import Alvoki.Storage.Disk.SegmentedSessionInstall
import Alvoki.Storage.Disk.WalSegmentBoundedOpenEffects
import Alvoki.Storage.Disk.WalSegmentRotationReopen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- The visible keeper can still disappear before the directory sync.
The first preparation and concrete prefix report fix the replay and visible keeper. The
fixed-keeper durability proof starts only once the first barrier applies. -/
theorem runOpenWithInstallation_afterInterruptedRotation
    {directory : DiskDirectory} {descriptor nextRef : Nat}
    {before : LockedFileState WalSegmentRotation.State} {image : WalSegmentImage} {history : List WAL.Write}
    (layout : (before.image.visible image).ReadLayout history) {range : MarkedWalRange}
    (selected : before.image.metadata.active.walRange = some range) (atEnd : range.through = history.length)
    (acquisition : TryLockObserves before.owners directory (.ok true)) (unlock : UnlockReport)
    (readOptional : FilePath → Except IO.Error (Option ByteArray))
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → Except IO.Error ByteArray)
    (readPrefix : FilePath → Nat → Except IO.Error KeeperPrefix)
    (removeFile : FilePath → EStateM IO.Error WalSegmentRotation.State (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error WalSegmentRotation.State Unit)
    (sync : Array FilePath → EStateM IO.Error WalSegmentRotation.State Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error WalSegmentRotation.State Unit)
    (table : PackedTable) (generation count : UInt64) :
    let active := (before.image.visible image).active
    let plan : Plan := ⟨range.through, active.first, [], active.bytes⟩
    let opened : Reopened := ⟨table, generation, count, active.first⟩
    let settled := before.image.settleForReopen
    let recover := reopenMarkedBoundedWith directory (fun path => liftExcept (readOptional path))
      (fun path => liftExcept (list path)) (fun path => liftExcept (lstat path)) (fun path => liftExcept (readBin path))
      (fun path size => liftExcept (readPrefix path size)) removeFile write sync renameFile
    let installed := runOpenWithInstallation directory descriptor nextRef (.ok true) unlock recover before
    prepareMarkedWith directory readOptional list lstat readBin = .ok (plan, opened) →
    readPrefix (directory.file (.walSegment plan.keeper)) plan.keeperSize =
      .ok ⟨plan.keeperBytes.extract 0 plan.keeperSize, plan.keeperBytes.size⟩ →
    (match sync #[directory.path] before.image with
      | .ok _ after => after = settled
      | .error _ after => after = before.image ∨ after = settled) →
    (match sync #[directory.file (.walSegment active.first)] settled with
      | .ok _ after | .error _ after => after = settled) →
    ∃ target, Prepared (before.image.settledReopenImage image) target plan ∧
      (∀ error after, sync #[directory.path] before.image = .error error after →
        installed = match unlock with
          | .success => .error error ⟨after, before.owners.set (directory.file .lock) none⟩
          | .failure cleanup released => .error cleanup
            ⟨after, before.owners.set (directory.file .lock) (if released then none else some descriptor)⟩) ∧
      (match installed with
      | .ok session after =>
        session.directory = directory ∧ session.descriptor = descriptor ∧ session.phase = .ready opened.installed ∧
          before.owners (directory.file .lock) = none ∧ after.owners.Owns directory descriptor ∧
          after.image = settled ∧ (before.image.settledReopenImage image).Ready target
      | .error _ after => after.image = before.image ∨ after.image = settled) := by
  intro active plan opened settled recover installed full prefixRead directoryReport keeperReport
  obtain ⟨target, prepared, firstError, finish⟩ :=
    before.image.finishAfterRotation layout selected atEnd directory removeFile write sync renameFile
      directoryReport keeperReport
  change Prepared (before.image.settledReopenImage image) target plan at prepared
  have bounded := prepareBoundedMarkedWith_from_full directory readOptional list lstat readBin readPrefix
    prepared.valid full prefixRead
  have recovered : recover before.image =
      match finishMarkedOpen directory plan removeFile write sync renameFile before.image with
      | .ok _ after => .ok opened after
      | .error err after => .error err after := by
    dsimp only [recover]
    rw [reopenMarkedBoundedWith_eq_full directory readOptional list lstat readBin readPrefix
      removeFile write sync renameFile prepared.valid full bounded]
    unfold reopenMarkedFastWith
    rw [prepareMarkedWith_liftReports directory readOptional list lstat readBin, full]
    simp only [liftExcept, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
    cases finishMarkedOpen directory plan removeFile write sync renameFile before.image <;> rfl
  have installOutcome := runOpenWithInstallation_outcome directory descriptor nextRef (.ok true) unlock recover before
  change installed = _ at installOutcome
  rw [runOpenWithImage_acquired, recovered] at installOutcome
  refine ⟨target, prepared, ?_, ?_⟩
  · intro error after failed
    have equation := firstError error after failed
    change finishMarkedOpen directory plan removeFile write sync renameFile before.image = .error error after
      at equation
    rw [installOutcome, equation]
    cases unlock <;> rfl
  · change (match finishMarkedOpen directory plan removeFile write sync renameFile before.image with
      | .ok _ after => after = settled ∧ (before.image.settledReopenImage image).Ready target
      | .error _ after => after = before.image ∨ after = settled) at finish
    rw [installOutcome]
    cases outcome : finishMarkedOpen directory plan removeFile write sync renameFile before.image with
    | ok result after =>
      rw [outcome] at finish
      exact ⟨rfl, rfl, rfl, acquisition rfl, by simp [LockOwners.Owns, LockOwners.set], finish⟩
    | error error after =>
      rw [outcome] at finish
      cases unlock <;> exact finish

end Alvoki.Storage.DiskSession
