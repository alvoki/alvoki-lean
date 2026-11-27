import Alvoki.Storage.Disk.Proofs.WAL.WalSegmentRepairEffects
import Alvoki.Storage.Disk.WalSegmentRepairOpen

namespace Alvoki.Storage.WalSegmentRepair

open System

/-- The strict marked worker returns its checked table and offsets only
when its exact repair callbacks establish the durable ready image. A
repair error preserves the recoverable state left by the corresponding
prefix, including errors reported after the effect. -/
theorem reopenMarkedWith_safe {initial : FileImage} {target : Target} {plan : Plan} {reopened : Reopened}
    (prepared : Prepared initial target plan) (dir : DiskDirectory)
    (readOptional : FilePath → EStateM IO.Error FileImage (Option ByteArray))
    (list : FilePath → EStateM IO.Error FileImage (Array IO.FS.DirEntry))
    (lstat : FilePath → EStateM IO.Error FileImage (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → EStateM IO.Error FileImage ByteArray)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (rename : FilePath → FilePath → EStateM IO.Error FileImage Unit)
    (observed : prepareMarkedWith dir readOptional list lstat readBin initial = .ok (plan, reopened) initial)
    (metadataReport : MetadataReport initial (sync #[dir.path]))
    (reports : EffectReports target initial.syncDirectory plan.actions
      (performPaths dir plan removeFile throw write sync rename)) :
    match reopenMarkedWith dir readOptional list lstat readBin removeFile write sync rename initial with
    | .ok returned after => returned = reopened ∧ EffectTrace target initial after ∧ after.Ready target
    | .error _ after => after = initial ∨ EffectTrace target initial after := by
  rw [reopenMarkedWith_afterPreparation _ _ _ _ _ _ _ _ _ observed]
  have effect := runAt_safe prepared dir (pure plan) rfl removeFile write sync rename metadataReport reports
  cases ran : runAt dir (pure plan) removeFile write sync rename initial with
  | ok value after =>
    cases value
    exact ⟨rfl, by simpa only [ran] using effect⟩
  | error error after =>
    simpa only [ran] using effect

/-- With successful read-only preparation and healthy callbacks at every
reached action, the strict worker returns the exact table and offsets from
preparation and has durably settled them. -/
theorem reopenMarkedWith_completes {initial : FileImage} {target : Target} {plan : Plan} {reopened : Reopened}
    (prepared : Prepared initial target plan) (dir : DiskDirectory)
    (readOptional : FilePath → EStateM IO.Error FileImage (Option ByteArray))
    (list : FilePath → EStateM IO.Error FileImage (Array IO.FS.DirEntry))
    (lstat : FilePath → EStateM IO.Error FileImage (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → EStateM IO.Error FileImage ByteArray)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (rename : FilePath → FilePath → EStateM IO.Error FileImage Unit)
    (observed : prepareMarkedWith dir readOptional list lstat readBin initial = .ok (plan, reopened) initial)
    (settles : sync #[dir.path] initial = .ok () initial.syncDirectory)
    (healthy : ∀ action before next, ReachesAction target initial.syncDirectory plan.actions action before →
      before.effect target action = some next →
      performPaths dir plan removeFile throw write sync rename action before = .ok () next) :
    ∃ after, reopenMarkedWith dir readOptional list lstat readBin removeFile write sync rename initial =
      .ok reopened after ∧ after.Ready target := by
  obtain ⟨after, repaired, ready, _⟩ := runObserved_completes prepared settles healthy
  refine ⟨after, ?_, ready⟩
  rw [reopenMarkedWith_afterPreparation _ _ _ _ _ _ _ _ _ observed,
    runAt_observed prepared dir (pure plan) rfl removeFile write sync rename, repaired]

end Alvoki.Storage.WalSegmentRepair
