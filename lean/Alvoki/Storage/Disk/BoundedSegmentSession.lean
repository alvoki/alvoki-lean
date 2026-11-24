import Alvoki.Storage.Disk.SegmentedSessionInstall
import Alvoki.Storage.Disk.WalSegmentBoundedOpenEffects
import Alvoki.Storage.Disk.WalSegmentOpenFastEffects

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- A healthy bounded reopen installs the exact prepared table after the
repair barriers under the acquired lock. The read reports are fixed during
the attempt. A full-read report is a witness for the visible bytes, including
the tail that the bounded worker need never read. -/
theorem runOpenWithInstallation_bounded {directory : DiskDirectory} {descriptor nextRef : Nat}
    {before : LockedFileState FileImage} {target : Target} {plan : Plan} {opened : Reopened}
    (prepared : Prepared before.image target plan)
    (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < nextRef)
    (acquisition : TryLockObserves before.owners directory (.ok true)) (unlock : UnlockReport)
    (readOptional : FilePath → Except IO.Error (Option ByteArray))
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → Except IO.Error ByteArray)
    (readPrefix : FilePath → Nat → Except IO.Error KeeperPrefix)
    (full : prepareMarkedWith directory readOptional list lstat readBin = .ok (plan, opened))
    (bounded : prepareBoundedMarkedWith directory readOptional list lstat readBin readPrefix =
      .ok ({ plan with keeperBytes := plan.keeperBytes.extract 0 plan.keeperSize }, opened, plan.keeperBytes.size))
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit)
    (settles : sync #[directory.path] before.image = .ok () before.image.syncDirectory)
    (healthy : ∀ action prior next, ReachesAction target before.image.syncDirectory plan.finishActions action prior →
      prior.effect target action = some next →
      performPaths directory plan removeFile throw write sync renameFile action prior = .ok () next) :
    let recover := reopenMarkedBoundedWith directory (fun path => liftExcept (readOptional path))
      (fun path => liftExcept (list path)) (fun path => liftExcept (lstat path)) (fun path => liftExcept (readBin path))
      (fun path count => liftExcept (readPrefix path count)) removeFile write sync renameFile
    ∃ session final,
      runOpenWithInstallation directory descriptor nextRef (.ok true) unlock recover before = .ok session final ∧
      session.directory = directory ∧ session.descriptor = descriptor ∧
      session.phase = .ready ⟨opened.table, opened.generation, opened.walBytes.toNat, opened.keeper⟩ ∧
      final.image.Ready target ∧ final.owners.Owns directory descriptor ∧
      session.phaseRef ≠ session.sessionRef ∧ session.phaseRef ∉ liveRefs ∧ session.sessionRef ∉ liveRefs := by
  intro recover
  have observed : (prepareMarkedWith directory (fun path => liftExcept (readOptional path))
      (fun path => liftExcept (list path)) (fun path => liftExcept (lstat path)) (fun path => liftExcept (readBin path))
      : EStateM IO.Error FileImage (Plan × Reopened)) before.image = .ok (plan, opened) before.image := by
    rw [prepareMarkedWith_liftReports, full]
    rfl
  obtain ⟨after, reopened, durable⟩ := reopenMarkedFastWith_completes prepared directory _ _ _ _ removeFile
    write sync renameFile observed settles healthy
  have transport := reopenMarkedBoundedWith_eq_full directory readOptional list lstat readBin readPrefix
    removeFile write sync renameFile prepared.valid full bounded
  have selected : recover before.image = .ok opened after := by
    dsimp only [recover]
    rw [transport]
    exact reopened
  obtain ⟨session, final, installed, path, lock, phase, same, _, held, separate, freshPhase, freshSession⟩ :=
    runOpenWithInstallation_ready liveRefs fresh acquisition (unlock := unlock) selected
  exact ⟨session, final, installed, path, lock, phase, same ▸ durable, held, separate, freshPhase, freshSession⟩

end Alvoki.Storage.DiskSession
