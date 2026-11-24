import Alvoki.Storage.Disk.SegmentedRetryTrace

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- The same stable open-file description and directory object can outlive
the writer's lock description. These identities come from a common object
namespace at capture and effect time. -/
structure DirectoryDescriptorIdentity where
  description : Nat
  inode : Nat

inductive DelayedDirectorySyncOutcome where
  | completed
  | errorBeforeEffect (cause : IO.Error)
  | errorAfterEffect (cause : IO.Error)

def DelayedDirectorySyncOutcome.effective : DelayedDirectorySyncOutcome → Bool
  | .completed | .errorAfterEffect _ => true
  | .errorBeforeEffect _ => false

/-- The effect-time stat observation associates the retained descriptor's
directory inode with the actual database directory. The issuing slot is
still present after the same process events that may have ended the
writer's lock. -/
structure DelayedDirectorySync (directory : DiskDirectory) where
  captured : DirectoryDescriptorIdentity
  references : HeldLockReferences captured.description
  issuer : LockReference
  drops : List LockReferenceDrop
  retained : issuer ∈ references.remaining drops
  effectTarget : DirectoryDescriptorIdentity
  sameTarget : effectTarget = captured
  statDirectory : FilePath → Option Nat
  liveTarget : statDirectory directory.path = some effectTarget.inode
  outcome : DelayedDirectorySyncOutcome

/-- Interpret the reported effect at its observed pathname binding. This
is a directory barrier only. The keeper's own file durability is separate. -/
def DelayedDirectorySync.run {directory : DiskDirectory} (report : DelayedDirectorySync directory)
    (before : LockedFileState FileImage) : EStateM.Result IO.Error (LockedFileState FileImage) Unit :=
  let settled := { before with image := before.image.syncDirectory }
  match report.outcome with
  | .completed => .ok () settled
  | .errorBeforeEffect cause => .error cause before
  | .errorAfterEffect cause => .error cause settled

def DelayedDirectorySync.after {directory : DiskDirectory} (report : DelayedDirectorySync directory)
    (before : LockedFileState FileImage) : LockedFileState FileImage :=
  match report.run before with
  | .ok () after | .error _ after => after

theorem DelayedDirectorySync.keepsFiles {directory : DiskDirectory} (report : DelayedDirectorySync directory)
    (before : LockedFileState FileImage) :
    (report.after before).owners = before.owners ∧
      (report.after before).image.kept = before.image.kept ∧
      (report.after before).image.keeper = before.image.keeper := by
  cases observed : report.outcome <;> simp [after, run, observed, FileImage.syncDirectory]

theorem DelayedDirectorySync.after_effective {directory : DiskDirectory} (report : DelayedDirectorySync directory)
    {before : LockedFileState FileImage} (effective : report.outcome.effective = true) :
    report.after before = { before with image := before.image.syncDirectory } := by
  cases observed : report.outcome <;> simp_all [after, run, DelayedDirectorySyncOutcome.effective]

/-- An effective delayed barrier fixes the currently observed pair and
later-name inventory for the next crash, even if the sync reports an error
after its effect. It does not settle the keeper's file bytes. -/
theorem DelayedDirectorySync.selectsCrashNames {directory : DiskDirectory} (report : DelayedDirectorySync directory)
    {before : LockedFileState FileImage} (effective : report.outcome.effective = true)
    {pair : DirectoryPublication.Bindings} {names : List Nat}
    (metadata : pair ∈ (report.after before).image.directory.crashImages)
    (later : names ∈ (report.after before).image.later.crashImages) :
    pair = before.image.directory.active ∧ names = before.image.later.visible := by
  rw [report.after_effective effective] at metadata later
  exact ⟨List.mem_singleton.mp metadata, List.mem_singleton.mp later⟩

/-- A retained directory descriptor can establish the first barrier before
a new opener runs. The checked target suffices for the shared repair
lineage, with no synthetic open or return from the interrupted mutation. -/
theorem DelayedDirectorySync.continuesLineage {directory : DiskDirectory} (report : DelayedDirectorySync directory)
    {source : FileImage} {before : LockedFileState FileImage} {admits : Target → Prop} {target : Target} {plan : Plan}
    (prior : ReopenLineage source admits before.image)
    (unique : ∀ {left right}, admits left → admits right → left.pair = right.pair → left = right)
    (admitted : admits target) (prepared : Prepared before.image target plan) :
    ReopenLineage source admits (report.after before).image := by
  have settled : ReopenLineage source admits before.image.syncDirectory :=
    prior.afterFailure unique (.inr ⟨target, plan, admitted, prepared, .authorized⟩)
  cases observed : report.outcome with
  | completed => simpa only [after, run, observed] using settled
  | errorBeforeEffect _ => simpa only [after, run, observed] using prior
  | errorAfterEffect _ => simpa only [after, run, observed] using settled

/-- The same process events can release the original writer's last flock
reference and leave the delayed directory descriptor live. Its modeled
effect preserves the released owner map. -/
theorem DelayedDirectorySync.afterLastWriterDrop {directory : DiskDirectory} (report : DelayedDirectorySync directory)
    {source : FileImage} {before : LockedFileState FileImage} {owner : Nat}
    {admits : Target → Prop} {target : Target} {plan : Plan}
    (references : HeldLockReferences owner) (owns : before.owners.Owns directory owner)
    (last : references.remaining report.drops = []) (separate : report.captured.description ≠ owner)
    (prior : ReopenLineage source admits before.image)
    (unique : ∀ {left right}, admits left → admits right → left.pair = right.pair → left = right)
    (admitted : admits target) (prepared : Prepared before.image target plan) :
    let released := references.afterFileDrops report.drops directory before
    let after := report.after released
    report.effectTarget.description ≠ owner ∧ after.owners (directory.file .lock) = none ∧
      ReopenLineage source admits after.image := by
  intro released after
  have noOwner : released.owners (directory.file .lock) = none := by
    simp [released, references.afterFileDrops_released owns last, LockOwners.set]
  refine ⟨by rw [report.sameTarget]; exact separate, ?_, ?_⟩
  · simpa only [after, (report.keepsFiles released).1] using noOwner
  · exact report.continuesLineage (before := released) prior unique admitted prepared

/-- Resume ordinary bounded retries after an independently observed
filesystem effect has already established the corresponding lineage. -/
theorem BoundedReopenTrace.continuesLineage {directory : DiskDirectory} {admits : Target → Prop}
    {start final : LockedFileState FileImage} {source : FileImage}
    (ran : BoundedReopenTrace directory admits start final)
    (prior : ReopenLineage source admits start.image)
    (unique : ∀ {left right}, admits left → admits right → left.pair = right.pair → left = right) :
    ReopenLineage source admits final.image := by
  induction ran with
  | empty => exact prior
  | failed _ attempt acquisition _ reports ran earlier =>
    exact earlier.afterFailure unique (attempt.errorFiles acquisition reports ran)
  | referenceDrops _ _ _ earlier => exact earlier
  | powerLoss _ metadata keeper later earlier => exact earlier.afterPowerLoss metadata keeper later

end Alvoki.Storage.DiskSession
