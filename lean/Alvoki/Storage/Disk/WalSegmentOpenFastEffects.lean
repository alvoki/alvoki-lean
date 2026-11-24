import Alvoki.Storage.Disk.WalSegmentOpenFast
import Alvoki.Storage.Disk.WalSegmentReopenEffects

namespace Alvoki.Storage.WalSegmentRepair

open System

private theorem Plan.alignedWithoutPrune_exact {plan : Plan} (fast : plan.alignedWithoutPrune = true) :
    plan.newer = [] ∧ plan.keeperBytes.size = plan.keeperSize := by
  simp only [Plan.alignedWithoutPrune, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at fast
  exact ⟨fast.1.2, fast.2⟩

/-- Actions reached after the metadata barrier on the selected route. -/
def Plan.finishActions (plan : Plan) : List Step :=
  if plan.alignedWithoutPrune then [.syncKeeper] else plan.actions

private theorem reachedAlignedKeeper {initial : FileImage} {target : Target} {plan : Plan}
    (fast : plan.alignedWithoutPrune = true) :
    ReachesAction target initial.syncDirectory plan.finishActions .syncKeeper initial.syncDirectory :=
  ⟨[], [], by simp [Plan.finishActions, fast], rfl⟩

private theorem Prepared.readyAfterAlignedSync {initial : FileImage} {target : Target} {plan : Plan}
    (prepared : Prepared initial target plan) (fast : plan.alignedWithoutPrune = true) :
    EffectTrace target initial initial.syncDirectory.syncKeeper ∧ initial.syncDirectory.syncKeeper.Ready target := by
  obtain ⟨empty, size⟩ := Plan.alignedWithoutPrune_exact fast
  have exactRead := prepared.aligned (by omega)
  have absent : initial.later.visible = [] := prepared.names.symm.trans empty
  have pruned : initial.syncDirectory.later.DurablyEmpty := by
    simp [FileImage.syncDirectory, LaterNames.syncDirectory, LaterNames.DurablyEmpty, LaterNames.settled, absent]
  exact ⟨EffectTrace.aligned .authorized pruned exactRead,
    ⟨prepared.pair, congrArg (fun pair => [pair]) prepared.pair,
      exactRead, congrArg (fun bytes => [bytes]) exactRead, pruned⟩⟩

/-- On the aligned route, one directory barrier settles the empty suffix.
The report contract then applies to the single reached keeper sync. -/
theorem finishMarkedOpen_safe {initial : FileImage} {target : Target} {plan : Plan}
    (prepared : Prepared initial target plan) (directory : DiskDirectory)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit)
    (metadataReport : MetadataReport initial (sync #[directory.path]))
    (reports : EffectReports target initial.syncDirectory plan.finishActions
      (performPaths directory plan removeFile throw write sync renameFile)) :
    match finishMarkedOpen directory plan removeFile write sync renameFile initial with
    | .ok _ after => EffectTrace target initial after ∧ after.Ready target
    | .error _ after => after = initial ∨ EffectTrace target initial after := by
  by_cases fast : plan.alignedWithoutPrune = true
  · simp only [finishMarkedOpen, fast, ite_true, Bind.bind, EStateM.bind]
    unfold MetadataReport at metadataReport
    cases directorySync : sync #[directory.path] initial with
    | error error after =>
      rw [directorySync] at metadataReport
      rcases metadataReport with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr .authorized
    | ok _ settled =>
      rw [directorySync] at metadataReport
      subst settled
      have keeperReports := reports .syncKeeper initial.syncDirectory (reachedAlignedKeeper fast)
      simp only [performPaths, FileImage.effect] at keeperReports
      have ready := prepared.readyAfterAlignedSync fast
      change (match sync #[directory.file (.walSegment plan.keeper)] initial.syncDirectory with
        | .ok _ after => EffectTrace target initial after ∧ after.Ready target
        | .error _ after => after = initial ∨ EffectTrace target initial after)
      cases keeperSync : sync #[directory.file (.walSegment plan.keeper)] initial.syncDirectory with
      | ok _ after =>
        rw [keeperSync] at keeperReports
        exact Option.some.inj keeperReports ▸ ready
      | error _ after =>
        rw [keeperSync] at keeperReports
        obtain ⟨publicResult, unchanged | synced, scratch⟩ := keeperReports
        · subst publicResult
          exact Or.inr (scratch ▸ (EffectTrace.authorized (target := target) (initial := initial)).scratch)
        · obtain rfl := Option.some.inj synced
          exact Or.inr (scratch ▸ ready.1.scratch)
  · simp only [finishMarkedOpen, ite_eq_right fast]
    have fallbackReports := reports
    simp only [Plan.finishActions, ite_eq_right fast] at fallbackReports
    have safety := runAt_safe prepared directory (pure plan) rfl removeFile write sync renameFile
      metadataReport fallbackReports
    cases ran : runAt directory (pure plan) removeFile write sync renameFile initial <;>
      simpa only [ran] using safety

theorem finishMarkedOpen_completes {initial : FileImage} {target : Target} {plan : Plan}
    (prepared : Prepared initial target plan) (directory : DiskDirectory)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit)
    (settles : sync #[directory.path] initial = .ok () initial.syncDirectory)
    (healthy : ∀ action before next, ReachesAction target initial.syncDirectory plan.finishActions action before →
      before.effect target action = some next →
      performPaths directory plan removeFile throw write sync renameFile action before = .ok () next) :
    ∃ after, finishMarkedOpen directory plan removeFile write sync renameFile initial = .ok () after ∧
      after.Ready target ∧ EffectTrace target initial after := by
  by_cases fast : plan.alignedWithoutPrune = true
  · have keeper := healthy .syncKeeper initial.syncDirectory initial.syncDirectory.syncKeeper
      (reachedAlignedKeeper fast) rfl
    change sync #[directory.file (.walSegment plan.keeper)] initial.syncDirectory = _ at keeper
    obtain ⟨trace, ready⟩ := prepared.readyAfterAlignedSync fast
    refine ⟨_, ?_, ready, trace⟩
    simp only [finishMarkedOpen, fast, ite_true, Bind.bind, EStateM.bind, settles, keeper]
  · simp only [finishMarkedOpen, ite_eq_right fast]
    rw [runAt_observed prepared directory (pure plan) rfl removeFile write sync renameFile]
    exact runObserved_completes prepared settles
      (by simpa only [Plan.finishActions, ite_eq_right fast] using healthy)

theorem reopenMarkedFastWith_afterPreparation {initial afterReads : FileImage} (directory : DiskDirectory)
    (readOptional : FilePath → EStateM IO.Error FileImage (Option ByteArray))
    (list : FilePath → EStateM IO.Error FileImage (Array IO.FS.DirEntry))
    (lstat : FilePath → EStateM IO.Error FileImage (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → EStateM IO.Error FileImage ByteArray)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit)
    {plan : Plan} {recovered : Reopened}
    (observed : prepareMarkedWith directory readOptional list lstat readBin initial =
      .ok (plan, recovered) afterReads) :
    reopenMarkedFastWith directory readOptional list lstat readBin removeFile write sync renameFile initial =
      match finishMarkedOpen directory plan removeFile write sync renameFile afterReads with
      | .ok _ after => .ok recovered after
      | .error error after => .error error after := by
  simp only [reopenMarkedFastWith, Bind.bind, EStateM.bind, observed]
  cases finishMarkedOpen directory plan removeFile write sync renameFile afterReads <;> rfl

/-- The native reopen route only returns the prepared table after its
actual barriers have established the durable file image. -/
theorem reopenMarkedFastWith_completes {initial : FileImage} {target : Target} {plan : Plan}
    {recovered : Reopened} (prepared : Prepared initial target plan) (directory : DiskDirectory)
    (readOptional : FilePath → EStateM IO.Error FileImage (Option ByteArray))
    (list : FilePath → EStateM IO.Error FileImage (Array IO.FS.DirEntry))
    (lstat : FilePath → EStateM IO.Error FileImage (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → EStateM IO.Error FileImage ByteArray)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit)
    (observed : prepareMarkedWith directory readOptional list lstat readBin initial =
      .ok (plan, recovered) initial)
    (settles : sync #[directory.path] initial = .ok () initial.syncDirectory)
    (healthy : ∀ action before next, ReachesAction target initial.syncDirectory plan.finishActions action before →
      before.effect target action = some next →
      performPaths directory plan removeFile throw write sync renameFile action before = .ok () next) :
    ∃ after, reopenMarkedFastWith directory readOptional list lstat readBin removeFile write sync renameFile initial =
      .ok recovered after ∧ after.Ready target := by
  obtain ⟨after, finished, ready, _⟩ := finishMarkedOpen_completes prepared directory removeFile write sync
    renameFile settles healthy
  refine ⟨after, ?_, ready⟩
  rw [reopenMarkedFastWith_afterPreparation _ _ _ _ _ _ _ _ _ observed, finished]

end Alvoki.Storage.WalSegmentRepair
