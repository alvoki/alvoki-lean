import Alvoki.Storage.Disk.LockDescriptionLifetime
import Alvoki.Storage.Disk.BoundedReopenFailure
import Alvoki.Storage.Disk.CachedWalMarkerOpenFailure

namespace Alvoki.Storage.WalSegmentRepair

/-- Before a directory barrier has taken effect, a retry sees the original
live files or a crash choice of those files. A second power loss preserves
the selected image of an already observed power loss. -/
inductive BeforeReopenBarrier (source : FileImage) : FileImage → Prop where
  | live : BeforeReopenBarrier source source
  | crash (pair : DirectoryPublication.Bindings) (keeper : Option ByteArray) (later : List Nat)
      (metadata : pair ∈ source.directory.crashImages) (payload : keeper ∈ source.keeper.crashImages)
      (names : later ∈ source.later.crashImages) : BeforeReopenBarrier source (source.crash pair keeper later)

theorem BeforeReopenBarrier.afterCrash {source current : FileImage} (before : BeforeReopenBarrier source current)
    {pair : DirectoryPublication.Bindings} {bytes : Option ByteArray} {later : List Nat}
    (metadata : pair ∈ current.directory.crashImages) (keeper : bytes ∈ current.keeper.crashImages)
    (names : later ∈ current.later.crashImages) : BeforeReopenBarrier source (current.crash pair bytes later) := by
  cases before with
  | live => exact .crash pair bytes later metadata keeper names
  | crash saved savedBytes savedLater chosen retained found =>
    have samePair : pair = saved := List.mem_singleton.mp metadata
    have sameBytes : bytes = savedBytes := List.mem_singleton.mp keeper
    have sameLater : later = savedLater := List.mem_singleton.mp names
    subst pair
    subst bytes
    subst later
    exact .crash saved savedBytes savedLater chosen retained found

theorem BeforeReopenBarrier.keepsSealed {source current : FileImage} (before : BeforeReopenBarrier source current) :
    current.kept = source.kept := by
  cases before <;> rfl

/-- Until the directory barrier takes effect, a new power loss can still
choose the old pair. After the barrier, all attempted repairs explain their
effects using the same checked target and the exact originating image. -/
inductive ReopenLineage (source : FileImage) (admits : Target → Prop) : FileImage → Prop where
  | before {current} (admissible : BeforeReopenBarrier source current) : ReopenLineage source admits current
  | repairing {start current target plan} (admissible : BeforeReopenBarrier source start)
      (canonical : admits target) (prepared : Prepared start target plan)
      (trace : EffectTrace target start current) : ReopenLineage source admits current

theorem ReopenLineage.afterRepairEffects {source current after : FileImage} {admits : Target → Prop}
    (lineage : ReopenLineage source admits current)
    (unique : ∀ {left right}, admits left → admits right → left.pair = right.pair → left = right)
    (effects : after = current ∨ ∃ target plan, admits target ∧ Prepared current target plan ∧
      EffectTrace target current after) : ReopenLineage source admits after := by
  obtain rfl | ⟨target, plan, admitted, prepared, trace⟩ := effects
  · exact lineage
  cases lineage with
  | before start => exact .repairing start admitted prepared trace
  | repairing start canonical original earlier =>
    have observed := earlier.valid original.pair original.keeperPrefix original.newer
    have same := unique canonical admitted (observed.selected.symm.trans prepared.pair)
    subst target
    exact .repairing start canonical original (earlier.trans trace)

theorem ReopenLineage.afterPowerLoss {source current : FileImage} {admits : Target → Prop}
    (lineage : ReopenLineage source admits current)
    {pair : DirectoryPublication.Bindings} {bytes : Option ByteArray} {later : List Nat}
    (metadata : pair ∈ current.directory.crashImages) (keeper : bytes ∈ current.keeper.crashImages)
    (names : later ∈ current.later.crashImages) : ReopenLineage source admits (current.crash pair bytes later) := by
  cases lineage with
  | before start => exact .before (start.afterCrash metadata keeper names)
  | repairing start canonical original trace =>
    exact .repairing start canonical original (.crash trace metadata keeper names)

theorem ReopenLineage.keepsSealed {source current : FileImage} {admits : Target → Prop}
    (lineage : ReopenLineage source admits current) : current.kept = source.kept := by
  cases lineage with
  | before start => exact start.keepsSealed
  | repairing start _ _ trace => exact trace.keepsSealed.trans start.keepsSealed

end Alvoki.Storage.WalSegmentRepair

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- One attempt at the bounded marked route, after native path admission.
Read reports are read-only. Repair callbacks receive the reached image. -/
structure BoundedReopenAttempt (image : Type := FileImage) where
  descriptor : Nat
  nextRef : Nat
  acquired : Except IO.Error Bool
  unlock : UnlockReport
  readOptional : FilePath → Except IO.Error (Option ByteArray)
  list : FilePath → Except IO.Error (Array IO.FS.DirEntry)
  lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata)
  readBin : FilePath → Except IO.Error ByteArray
  readPrefix : FilePath → Nat → Except IO.Error KeeperPrefix
  removeFile : FilePath → EStateM IO.Error image (Except IO.Error Unit)
  write : FilePath → ByteArray → EStateM IO.Error image Unit
  sync : Array FilePath → EStateM IO.Error image Unit
  renameFile : FilePath → FilePath → EStateM IO.Error image Unit

def BoundedReopenAttempt.recover {image : Type} (attempt : BoundedReopenAttempt image) (directory : DiskDirectory) :
    EStateM IO.Error image Reopened :=
  reopenMarkedBoundedWith directory (fun path => liftExcept (attempt.readOptional path))
    (fun path => liftExcept (attempt.list path)) (fun path => liftExcept (attempt.lstat path))
    (fun path => liftExcept (attempt.readBin path)) (fun path count => liftExcept (attempt.readPrefix path count))
    attempt.removeFile attempt.write attempt.sync attempt.renameFile

def BoundedReopenAttempt.run {image : Type} (attempt : BoundedReopenAttempt image) (directory : DiskDirectory) :
    EStateM IO.Error (LockedFileState image) SegmentedSession :=
  runOpenWithInstallation directory attempt.descriptor attempt.nextRef attempt.acquired attempt.unlock
    (attempt.recover directory)

def BoundedReopenAttempt.prepare {image : Type} (attempt : BoundedReopenAttempt image) (directory : DiskDirectory) :
    Except IO.Error (Plan × Reopened × Nat) :=
  prepareBoundedMarkedWith directory attempt.readOptional attempt.list attempt.lstat attempt.readBin attempt.readPrefix

def BoundedReopenAttempt.Reports (attempt : BoundedReopenAttempt) (directory : DiskDirectory)
    (before : FileImage) (admits : Target → Prop) : Prop :=
  attempt.acquired = .ok true → match attempt.prepare directory with
  | .error _ => True
  | .ok (bounded, _, physicalSize) => ∃ target full,
    admits target ∧ Prepared before target full ∧
    bounded = { full with keeperBytes := full.keeperBytes.extract 0 full.keeperSize } ∧
    physicalSize = full.keeperBytes.size ∧ MetadataReport before (attempt.sync #[directory.path]) ∧
    EffectReports target before.syncDirectory full.finishActions
      (performPaths directory full attempt.removeFile throw attempt.write attempt.sync attempt.renameFile)

/-- Derive the exact file transition from the bounded worker and its
primitive read and reached repair reports. -/
theorem BoundedReopenAttempt.errorFiles {directory : DiskDirectory} {admits : Target → Prop}
    {before after : LockedFileState FileImage} {cause : IO.Error} (attempt : BoundedReopenAttempt)
    (acquisition : TryLockObserves before.owners directory attempt.acquired)
    (reports : attempt.Reports directory before.image admits)
    (ran : attempt.run directory before = .error cause after) :
    after.image = before.image ∨ ∃ target plan, admits target ∧ Prepared before.image target plan ∧
      EffectTrace target before.image after.image := by
  by_cases took : attempt.acquired = .ok true
  · cases reading : attempt.prepare directory with
    | error error =>
      have native := runOpenWithInstallation_boundedPreparationError directory attempt.descriptor attempt.nextRef
        attempt.acquired attempt.unlock attempt.readOptional attempt.list attempt.lstat attempt.readBin
        attempt.readPrefix attempt.removeFile attempt.write attempt.sync attempt.renameFile before (cause := error)
        (fun _ => reading)
      change attempt.run directory before = _ at native
      rw [ran, took] at native
      cases released : attempt.unlock <;> rw [released] at native <;>
        obtain ⟨_, same⟩ := EStateM.Result.error.inj native <;>
        exact Or.inl (congrArg (fun state => state.image) same)
    | ok report =>
      obtain ⟨bounded, opened, physicalSize⟩ := report
      have observed := reports took
      rw [reading] at observed
      obtain ⟨target, full, admitted, prepared, exactBounded, size, metadata, effects⟩ := observed
      have contract := runOpenWithImage_boundedSegmented directory attempt.descriptor before target attempt.acquired
        acquisition attempt.unlock attempt.readOptional attempt.list attempt.lstat attempt.readBin attempt.readPrefix
        attempt.removeFile attempt.write attempt.sync attempt.renameFile (fun _ => by
          change (match attempt.prepare directory with
            | .error _ => True
            | .ok (plan, _, length) => ∃ full, Prepared before.image target full ∧
              plan = { full with keeperBytes := full.keeperBytes.extract 0 full.keeperSize } ∧
              length = full.keeperBytes.size ∧ MetadataReport before.image (attempt.sync #[directory.path]) ∧
              EffectReports target before.image.syncDirectory full.finishActions
                (performPaths directory full attempt.removeFile throw attempt.write attempt.sync attempt.renameFile))
          rw [reading]
          exact ⟨full, prepared, exactBounded, size, metadata, effects⟩)
      rw [BoundedReopenAttempt.run, runOpenWithInstallation_outcome] at ran
      cases native : runOpenWithImage directory attempt.descriptor attempt.acquired attempt.unlock
          (attempt.recover directory) before with
      | ok session state => rw [native] at ran; contradiction
      | error error state =>
        rw [native] at ran
        obtain ⟨rfl, rfl⟩ := EStateM.Result.error.inj ran
        rw [show runOpenWithImage directory attempt.descriptor attempt.acquired attempt.unlock
          (reopenMarkedBoundedWith directory (fun path => liftExcept (attempt.readOptional path))
            (fun path => liftExcept (attempt.list path)) (fun path => liftExcept (attempt.lstat path))
            (fun path => liftExcept (attempt.readBin path)) (fun path n => liftExcept (attempt.readPrefix path n))
            attempt.removeFile attempt.write attempt.sync attempt.renameFile) before = .error error state from native]
          at contract
        rcases contract with ⟨denied, _⟩ | ⟨_, _, unchanged | trace, _⟩
        · exact False.elim (denied took)
        · exact Or.inl unchanged
        · exact Or.inr ⟨target, full, admitted, prepared, trace⟩
  · obtain ⟨error, denied⟩ := runOpenWithImage_notAcquired directory attempt.descriptor attempt.acquired
      attempt.unlock (attempt.recover directory) before took
    rw [BoundedReopenAttempt.run, runOpenWithInstallation_outcome, denied] at ran
    exact Or.inl (congrArg LockedFileState.image (EStateM.Result.error.inj ran).2.symm)

/-- A successfully acquired open stopped in its initialization or route
checks. The failed prefix records the reached state before local unlock. -/
structure CachedOpenPrefixFailure {image : Type} (files : Type) (directory : DiskDirectory)
    (before : LockedFileState image) where
  descriptor : Nat
  nextRef : Nat
  acquisition : TryLockObserves before.owners directory (.ok true)
  unlock : UnlockReport
  localUnlock : unlock.LocalFlock
  prepare : EStateM IO.Error image files
  cause : IO.Error
  reached : image
  failed : prepare before.image = .error cause reached

namespace CachedOpenPrefixFailure

variable {files image : Type} {directory : DiskDirectory} {before : LockedFileState image}

def error (failure : CachedOpenPrefixFailure files directory before) : IO.Error :=
  match failure.unlock with
  | .success => failure.cause
  | .failure cleanup _ => cleanup

def after (failure : CachedOpenPrefixFailure files directory before) : LockedFileState image :=
  ⟨failure.reached, before.owners.set (directory.file .lock)
    (match failure.unlock with
     | .success => none
     | .failure _ _ => some failure.descriptor)⟩

/-- Successful local unlock returns the prefix error and clears ownership.
A failed local unlock returns its own error and leaves the owner held. -/
theorem cleanupOutcome (failure : CachedOpenPrefixFailure files directory before) :
    match failure.unlock with
    | .success => failure.error = failure.cause ∧ failure.after.owners (directory.file .lock) = none
    | .failure cleanup _ =>
      failure.error = cleanup ∧ failure.after.owners (directory.file .lock) = some failure.descriptor := by
  cases report : failure.unlock <;> simp [error, after, report, LockOwners.set]

theorem run_error (failure : CachedOpenPrefixFailure files directory before)
    (recover : files → EStateM IO.Error image Reopened) :
    runOpenWithInstallation directory failure.descriptor failure.nextRef (.ok true) failure.unlock
      (failure.prepare >>= recover) before = .error failure.error failure.after := by
  have failed : (failure.prepare >>= recover) before.image = .error failure.cause failure.reached := by
    simp only [Bind.bind, EStateM.bind, failure.failed]
  rw [runOpenWithInstallation_acquiredRecoveryError _ _ _ _ _ _ failed]
  cases report : failure.unlock with
  | success => simp [error, after, report]
  | failure cleanup released =>
    have retained : released = false := by
      simpa [UnlockReport.LocalFlock, report] using failure.localUnlock
    simp [error, after, report, retained]

end CachedOpenPrefixFailure

/-- A finite retry can cross failed opens, interrupted repairs, drops of
lock references and power losses. An interruption records the effects at
the observation point while the opener still owns the lock. -/
inductive BoundedReopenTrace (directory : DiskDirectory) (admits : Target → Prop)
    (initial : LockedFileState FileImage) : LockedFileState FileImage → Prop where
  | empty : BoundedReopenTrace directory admits initial initial
  | failed {before after cause} (prior : BoundedReopenTrace directory admits initial before)
      (attempt : BoundedReopenAttempt) (acquisition : TryLockObserves before.owners directory attempt.acquired)
      (localUnlock : attempt.unlock.LocalFlock) (reports : attempt.Reports directory before.image admits)
      (ran : attempt.run directory before = .error cause after) : BoundedReopenTrace directory admits initial after
  | cachedPrefixFailed {before files} (prior : BoundedReopenTrace directory admits initial before)
      (failure : CachedOpenPrefixFailure files directory before) (unchanged : failure.reached = before.image) :
      BoundedReopenTrace directory admits initial failure.after
  | cachedRejected {before} (prior : BoundedReopenTrace directory admits initial before)
      (rejection : CachedOpenRejection directory before) :
      BoundedReopenTrace directory admits initial rejection.after
  | cachedAuthorizationFailed {before} (prior : BoundedReopenTrace directory admits initial before)
      (failure : CachedOpenAuthorizationFailure directory before) (admitted : admits failure.target) :
      BoundedReopenTrace directory admits initial failure.after
  | cachedRepairFailed {before target plan cause reached} (prior : BoundedReopenTrace directory admits initial before)
      (attempt : CachedOpenAttempt directory before) (admitted : admits target)
      (prepared : Prepared before.image target plan) (effects : EffectTrace target before.image reached)
      (ran : attempt.run = .error (attempt.cleanupError cause reached).1 (attempt.cleanupError cause reached).2) :
      BoundedReopenTrace directory admits initial (attempt.cleanupError cause reached).2
  | repairInterrupted {before target plan reached} (prior : BoundedReopenTrace directory admits initial before)
      (description : Nat) (acquired : TryLockObserves before.owners directory (.ok true))
      (admitted : admits target) (prepared : Prepared before.image target plan)
      (effects : EffectTrace target before.image reached) :
      BoundedReopenTrace directory admits initial
        ⟨reached, before.owners.set (directory.file .lock) (some description)⟩
  | referenceDrops {before description} (prior : BoundedReopenTrace directory admits initial before)
      (references : HeldLockReferences description) (drops : List LockReferenceDrop) :
      BoundedReopenTrace directory admits initial (references.afterFileDrops drops directory before)
  -- Machine power loss ends every reference to the observed local lock.
  | powerLoss {before pair bytes names} (prior : BoundedReopenTrace directory admits initial before)
      (metadata : pair ∈ before.image.directory.crashImages) (keeper : bytes ∈ before.image.keeper.crashImages)
      (later : names ∈ before.image.later.crashImages) :
      BoundedReopenTrace directory admits initial
        ⟨before.image.crash pair bytes names, before.owners.set (directory.file .lock) none⟩

/-- After cleanup fails, dropping the rejected opener's last reference
permits a subsequent cooperating opener to acquire the lock. -/
theorem BoundedReopenTrace.afterCachedLastDrop {directory admits initial before}
    (prior : BoundedReopenTrace directory admits initial before) (rejection : CachedOpenRejection directory before)
    {cause : IO.Error} (cleanup : rejection.attempt.unlock = .failure cause false)
    (references : HeldLockReferences rejection.attempt.descriptor) (drops : List LockReferenceDrop)
    (last : references.remaining drops = []) :
    let released := references.afterFileDrops drops directory rejection.after
    BoundedReopenTrace directory admits initial released ∧ TryLockObserves released.owners directory (.ok true) := by
  dsimp only
  have held : rejection.after.owners.Owns directory rejection.attempt.descriptor := by
    simp [CachedOpenRejection.after, CachedOpenAttempt.cleanupError, cleanup, LockOwners.Owns, LockOwners.set]
  refine ⟨.referenceDrops (.cachedRejected prior rejection) references drops, ?_⟩
  rw [references.afterFileDrops_released held last]
  simp [TryLockObserves, LockOwners.set]

/-- A decoder failure is one read-only cached preparation rejection. -/
theorem BoundedReopenTrace.cachedMarkerRejected {directory admits initial before}
    (prior : BoundedReopenTrace directory admits initial before) (rejection : CachedMarkerRejection directory before) :
    BoundedReopenTrace directory admits initial rejection.after :=
  .cachedRejected prior rejection.certified

/-- After cleanup fails, dropping the rejected opener's last reference
permits a subsequent cooperating opener to acquire the lock. -/
theorem BoundedReopenTrace.afterCachedMarkerLastDrop {directory admits initial before}
    (prior : BoundedReopenTrace directory admits initial before) (rejection : CachedMarkerRejection directory before)
    {cause : IO.Error} (cleanup : rejection.unlock = .failure cause false)
    (references : HeldLockReferences rejection.descriptor) (drops : List LockReferenceDrop)
    (last : references.remaining drops = []) :
    let released := references.afterFileDrops drops directory rejection.after
    BoundedReopenTrace directory admits initial released ∧ TryLockObserves released.owners directory (.ok true) :=
  prior.afterCachedLastDrop rejection.certified cleanup references drops last

/-- After a failed authorization and failed local cleanup, the retry
retains the reached file image and releases the owner only on its last
observed reference drop. -/
theorem BoundedReopenTrace.afterCachedAuthorizationLastDrop {directory admits initial before}
    (prior : BoundedReopenTrace directory admits initial before) (failure : CachedOpenAuthorizationFailure directory before)
    (admitted : admits failure.target) {cause : IO.Error} (cleanup : failure.attempt.unlock = .failure cause false)
    (references : HeldLockReferences failure.attempt.descriptor) (drops : List LockReferenceDrop)
    (last : references.remaining drops = []) :
    let released := references.afterFileDrops drops directory failure.after
    BoundedReopenTrace directory admits initial released ∧ TryLockObserves released.owners directory (.ok true) := by
  dsimp only
  have held : failure.after.owners.Owns directory failure.attempt.descriptor := by
    simp [CachedOpenAuthorizationFailure.after, CachedOpenAttempt.cleanupError, cleanup, LockOwners.Owns, LockOwners.set]
  refine ⟨.referenceDrops (.cachedAuthorizationFailed prior failure admitted) references drops, ?_⟩
  rw [references.afterFileDrops_released held last]
  simp [TryLockObserves, LockOwners.set]

/-- The reached state of one retry trace is the starting state of the next. -/
theorem BoundedReopenTrace.trans {directory admits initial middle after}
    (earlier : BoundedReopenTrace directory admits initial middle)
    (later : BoundedReopenTrace directory admits middle after) : BoundedReopenTrace directory admits initial after := by
  induction later with
  | empty => exact earlier
  | failed _ attempt acquisition unlock reports ran ih => exact .failed ih attempt acquisition unlock reports ran
  | cachedPrefixFailed _ failure unchanged ih => exact .cachedPrefixFailed ih failure unchanged
  | cachedRejected _ rejection ih => exact .cachedRejected ih rejection
  | cachedAuthorizationFailed _ failure admitted ih => exact .cachedAuthorizationFailed ih failure admitted
  | cachedRepairFailed _ attempt admitted prepared effects ran ih =>
    exact .cachedRepairFailed ih attempt admitted prepared effects ran
  | repairInterrupted _ description acquired admitted prepared effects ih =>
    exact .repairInterrupted ih description acquired admitted prepared effects
  | referenceDrops _ references drops ih => exact .referenceDrops ih references drops
  | powerLoss _ metadata keeper names ih => exact .powerLoss ih metadata keeper names

/-- Continue the lineage after an observed effect before the next open. -/
theorem BoundedReopenTrace.continuesLineage {directory : DiskDirectory} {admits : Target → Prop}
    {initial after : LockedFileState FileImage} {source : FileImage}
    (ran : BoundedReopenTrace directory admits initial after)
    (prior : ReopenLineage source admits initial.image)
    (unique : ∀ {left right}, admits left → admits right → left.pair = right.pair → left = right) :
    ReopenLineage source admits after.image := by
  induction ran with
  | empty => exact prior
  | failed _ attempt acquisition _ reports ran ih =>
    exact ih.afterRepairEffects unique (attempt.errorFiles acquisition reports ran)
  | cachedPrefixFailed _ failure unchanged ih =>
    change ReopenLineage source admits failure.reached
    rw [unchanged]
    exact ih
  | cachedRejected _ _ ih => exact ih
  | cachedAuthorizationFailed _ failure admitted ih => exact ih.afterRepairEffects unique (failure.errorFiles admitted)
  | cachedRepairFailed _ attempt admitted prepared effects _ ih =>
    apply ih.afterRepairEffects unique
    exact Or.inr ⟨_, _, admitted, prepared, by simpa only [CachedOpenAttempt.cleanupError_keepsFiles] using effects⟩
  | repairInterrupted _ _ _ admitted prepared effects ih =>
    exact ih.afterRepairEffects unique (.inr ⟨_, _, admitted, prepared, effects⟩)
  | referenceDrops _ _ _ ih => exact ih
  | powerLoss _ metadata keeper later ih => exact ih.afterPowerLoss metadata keeper later

theorem BoundedReopenTrace.lineage {directory : DiskDirectory} {admits : Target → Prop}
    {initial after : LockedFileState FileImage} (ran : BoundedReopenTrace directory admits initial after)
    (unique : ∀ {left right}, admits left → admits right → left.pair = right.pair → left = right) :
    ReopenLineage initial.image admits after.image :=
  ran.continuesLineage (.before .live) unique

end Alvoki.Storage.DiskSession
