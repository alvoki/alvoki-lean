import Alvoki.Storage.Disk.LockDescriptionLifetime
import Alvoki.Storage.Disk.BoundedReopenFailure

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

theorem ReopenLineage.afterFailure {source current after : FileImage} {admits : Target → Prop}
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

/-- A finite retry can cross failed opens, observed drops of lock references,
and power losses. Failed opens record their exact returned image and owner.
The callback contract determines whether the directory barrier took effect. -/
inductive BoundedReopenTrace (directory : DiskDirectory) (admits : Target → Prop)
    (initial : LockedFileState FileImage) : LockedFileState FileImage → Prop where
  | empty : BoundedReopenTrace directory admits initial initial
  | failed {before after cause} (prior : BoundedReopenTrace directory admits initial before)
      (attempt : BoundedReopenAttempt) (acquisition : TryLockObserves before.owners directory attempt.acquired)
      (localUnlock : attempt.unlock.LocalFlock) (reports : attempt.Reports directory before.image admits)
      (ran : attempt.run directory before = .error cause after) : BoundedReopenTrace directory admits initial after
  | referenceDrops {before description} (prior : BoundedReopenTrace directory admits initial before)
      (references : HeldLockReferences description) (drops : List LockReferenceDrop) :
      BoundedReopenTrace directory admits initial (references.afterFileDrops drops directory before)
  -- Machine power loss ends every reference to the observed local lock.
  | powerLoss {before pair bytes names} (prior : BoundedReopenTrace directory admits initial before)
      (metadata : pair ∈ before.image.directory.crashImages) (keeper : bytes ∈ before.image.keeper.crashImages)
      (later : names ∈ before.image.later.crashImages) :
      BoundedReopenTrace directory admits initial
        ⟨before.image.crash pair bytes names, before.owners.set (directory.file .lock) none⟩

theorem BoundedReopenTrace.lineage {directory : DiskDirectory} {admits : Target → Prop}
    {initial after : LockedFileState FileImage} (ran : BoundedReopenTrace directory admits initial after)
    (unique : ∀ {left right}, admits left → admits right → left.pair = right.pair → left = right) :
    ReopenLineage initial.image admits after.image := by
  induction ran with
  | empty => exact .before .live
  | failed _ attempt acquisition _ reports ran ih =>
    exact ih.afterFailure unique (attempt.errorFiles acquisition reports ran)
  | referenceDrops _ _ _ ih => exact ih
  | powerLoss _ metadata keeper later ih => exact ih.afterPowerLoss metadata keeper later

end Alvoki.Storage.DiskSession
