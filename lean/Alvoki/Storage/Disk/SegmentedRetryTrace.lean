import Alvoki.Storage.Disk.LockDescriptionLifetime
import Alvoki.Storage.Disk.WalSegmentOpenFastEffects

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
structure BoundedReopenAttempt where
  descriptor : Nat
  nextRef : Nat
  acquired : Except IO.Error Bool
  unlock : UnlockReport
  readOptional : FilePath → Except IO.Error (Option ByteArray)
  list : FilePath → Except IO.Error (Array IO.FS.DirEntry)
  lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata)
  readBin : FilePath → Except IO.Error ByteArray
  readPrefix : FilePath → Nat → Except IO.Error KeeperPrefix
  removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit)
  write : FilePath → ByteArray → EStateM IO.Error FileImage Unit
  sync : Array FilePath → EStateM IO.Error FileImage Unit
  renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit

def BoundedReopenAttempt.recover (attempt : BoundedReopenAttempt) (directory : DiskDirectory) :
    EStateM IO.Error FileImage Reopened :=
  reopenMarkedBoundedWith directory (fun path => liftExcept (attempt.readOptional path))
    (fun path => liftExcept (attempt.list path)) (fun path => liftExcept (attempt.lstat path))
    (fun path => liftExcept (attempt.readBin path)) (fun path count => liftExcept (attempt.readPrefix path count))
    attempt.removeFile attempt.write attempt.sync attempt.renameFile

def BoundedReopenAttempt.run (attempt : BoundedReopenAttempt) (directory : DiskDirectory) :
    EStateM IO.Error (LockedFileState FileImage) SegmentedSession :=
  runOpenWithInstallation directory attempt.descriptor attempt.nextRef attempt.acquired attempt.unlock
    (attempt.recover directory)

/-- A finite retry can cross failed opens, observed drops of lock references,
and power losses. Failed opens record their exact returned image and owner.
The callback contract determines whether the directory barrier took effect. -/
inductive BoundedReopenTrace (directory : DiskDirectory) (admits : Target → Prop)
    (initial : LockedFileState FileImage) : LockedFileState FileImage → Prop where
  | empty : BoundedReopenTrace directory admits initial initial
  | failed {before after cause} (prior : BoundedReopenTrace directory admits initial before)
      (attempt : BoundedReopenAttempt) (acquisition : TryLockObserves before.owners directory attempt.acquired)
      (localUnlock : attempt.unlock.LocalFlock) (ran : attempt.run directory before = .error cause after)
      (files : after.image = before.image ∨ ∃ target plan, admits target ∧ Prepared before.image target plan ∧
        EffectTrace target before.image after.image) : BoundedReopenTrace directory admits initial after
  | referenceDrops {before description} (prior : BoundedReopenTrace directory admits initial before)
      (references : HeldLockReferences description) (drops : List LockReferenceDrop) :
      BoundedReopenTrace directory admits initial (references.afterFileDrops drops directory before)
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
  | failed _ _ _ _ _ files ih => exact ih.afterFailure unique files
  | referenceDrops _ _ _ ih => exact ih
  | powerLoss _ metadata keeper later ih => exact ih.afterPowerLoss metadata keeper later

end Alvoki.Storage.DiskSession
