import Alvoki.Storage.Disk.SegmentedKeeperSyncBeforeBarrier

namespace Alvoki.Storage.WalSegmentRepair

open DiskSession WAL.Boundary

private theorem appliedPrefix {target : Target} {initial reached : FileImage}
    {perform : Step → EStateM IO.Error FileImage Unit} {earlier rest : List Step} {next : Step}
    (reports : EffectReports target initial (earlier ++ next :: rest) perform)
    (ran : (earlier.forM perform) initial = .ok () reached) :
    earlier.foldlM (fun state action => state.effect target action) initial = some reached := by
  induction earlier generalizing initial with
  | nil => cases ran; rfl
  | cons action earlier ih =>
    have head := reports action initial ⟨[], earlier ++ next :: rest, rfl, rfl⟩
    change EStateM.bind (perform action) (fun _ => earlier.forM perform) initial = _ at ran
    unfold EStateM.bind at ran
    cases effect : perform action initial with
    | error err after => rw [effect] at ran; contradiction
    | ok _ after =>
      rw [effect] at ran head
      have liftReach {step before} (reach : ReachesAction target after (earlier ++ next :: rest) step before) :
          ReachesAction target initial ((action :: earlier) ++ next :: rest) step before := by
        obtain ⟨prior, suffix, schedule, executed⟩ := reach
        refine ⟨action :: prior, suffix, congrArg (List.cons action) schedule, ?_⟩
        simpa only [List.foldlM_cons, head, Bind.bind, Option.bind] using executed
      simpa only [List.foldlM_cons, head, Bind.bind, Option.bind] using
        ih (fun step before reach => reports step before (liftReach reach)) ran

private theorem FileImage.syncDirectory_twice (files : FileImage) :
    files.syncDirectory.syncDirectory = files.syncDirectory := rfl

/-- With no later WAL names and a longer physical keeper, the accepted bounded
reader runs through rename before the final directory sync. A sync issued at
that cut by a retained old descriptor preserves the checked target, with the
actual inode outcomes accounted for in the crash cover and the next plan.
The worker equation identifies its pending callback on the uninterrupted route. -/
theorem DelayedKeeperSync.atBoundedReplacementBarrier (report : DelayedKeeperSync)
    (attempt : BoundedReopenAttempt) (directory : DiskDirectory) (before : FileImage)
    (previous : WalInodeImage) (replacement : Nat) {admits : Target → Prop}
    {bounded : Plan} {opened : Reopened} {physicalSize : Nat} {settled reached : FileImage}
    (acquired : attempt.acquired = .ok true) (reports : attempt.Reports directory before admits)
    (reading : attempt.prepare directory = .ok (bounded, opened, physicalSize))
    (noLater : bounded.newer = []) (longer : bounded.keeperSize < physicalSize)
    (barrier : attempt.sync #[directory.path] before = .ok () settled)
    (renamed : (((steps [] true).take 4).forM
      (performPaths directory bounded attempt.removeFile throw attempt.write attempt.sync attempt.renameFile))
      settled = .ok () reached)
    (projected : before.withKeeperInodes previous = before)
    (oldTarget : report.captured.inode = previous.active) (distinct : previous.active ≠ replacement)
    (fresh : replacement ∉ previous.crashBindings)
    (allowed : ∀ bytes ∈ report.outcomes, bytes = previous.visible previous.active ∨
      bytes ∈ previous.crashBytes previous.active) :
    ∃ target full cover retryPlan, admits target ∧
      bounded.keeperBytes = target.trimmed ∧
      ReachesAction target before.syncDirectory full.finishActions (.replace .syncDirectory) reached ∧
      reached = (before.syncDirectory.withScratch none).withKeeperInodes
        (previous.renameSynced replacement target.trimmed) ∧
      (attempt.recover directory before = match attempt.sync #[directory.path] reached with
        | .ok _ after => .ok opened after
        | .error cause after => .error cause after) ∧
      Prepared before.allowVisibleKeeper target full ∧
      EffectTrace target before.allowVisibleKeeper cover ∧
      let afterSync := reached.withKeeperInodes (report.effect (previous.renameSynced replacement target.trimmed))
      afterSync.KeeperCrashCover cover ∧ Prepared afterSync target retryPlan := by
  have observed := reports acquired
  rw [reading] at observed
  obtain ⟨target, full, admitted, prepared, exactBounded, size, metadata, effects⟩ := observed
  have empty : full.newer = [] := by simpa only [exactBounded] using noLater
  have short : full.keeperSize < full.keeperBytes.size := by
    simpa only [exactBounded, size, Plan.keeperSize] using longer
  have notAligned : full.alignedWithoutPrune = false := by
    simp [Plan.alignedWithoutPrune, Nat.ne_of_gt short]
  have schedule : full.finishActions = (steps [] true).take 4 ++ [.replace .syncDirectory] := by
    simp [Plan.finishActions, notAligned, Plan.actions, empty, short, steps, Publication.steps]
  have paths : performPaths directory bounded attempt.removeFile throw attempt.write attempt.sync attempt.renameFile =
      performPaths directory full attempt.removeFile throw attempt.write attempt.sync attempt.renameFile := by
    subst bounded
    funext step
    cases step with
    | replace step => cases step <;> simp [performPaths, Publication.performReplacement, Plan.keeperSize,
        ByteArray.extract_extract]
    | unlink _ | syncPruned | syncKeeper => rfl
  unfold MetadataReport at metadata
  rw [barrier] at metadata
  have ran := renamed
  rw [paths, metadata] at ran
  rw [schedule] at effects
  have applied := appliedPrefix effects ran
  have reachedNext : ReachesAction target before.syncDirectory full.finishActions (.replace .syncDirectory) reached :=
    ⟨(steps [] true).take 4, [], schedule, applied⟩
  have laterEmpty : before.syncDirectory.later.DurablyEmpty := by
    have invisible : before.later.visible = [] := prepared.names.symm.trans empty
    simp [FileImage.syncDirectory, LaterNames.syncDirectory, LaterNames.settled, LaterNames.DurablyEmpty, invisible]
  have exactReach : reached = (before.syncDirectory.withScratch none).withKeeperInodes
      (previous.renameSynced replacement target.trimmed) := by
    change some ({ before.syncDirectory.syncDirectory with keeper :=
      ⟨some target.trimmed, some target.trimmed :: before.keeper.crashImages, none⟩ } : FileImage) = some reached at applied
    rw [FileImage.syncDirectory_twice] at applied
    have renamedInode := previous.project_renameSynced before.syncDirectory.directory replacement target.trimmed fresh
    have crashBytes := congrArg (Option.map (fun image : ReopenImage => image.wal.crashImages)) renamedInode
    have priorBytes : (previous.project before.directory).wal.crashImages = before.keeper.crashImages :=
      congrArg (fun files : FileImage => files.keeper.crashImages) projected
    change some (some target.trimmed :: (previous.project before.directory).wal.crashImages) =
      some (((previous.renameSynced replacement target.trimmed).project before.syncDirectory.directory).wal.crashImages) at crashBytes
    rw [priorBytes] at crashBytes
    rw [← Option.some.inj applied]
    simp only [FileImage.withKeeperInodes, FileImage.withScratch, WalInodeImage.project, WalInodeImage.renameSynced, ite_true]
    exact congrArg (fun choices => { before.syncDirectory with keeper := ⟨some target.trimmed, choices, none⟩ })
      (Option.some.inj crashBytes)
  have recovery : attempt.recover directory before = match attempt.sync #[directory.path] reached with
      | .ok _ after => .ok opened after
      | .error cause after => .error cause after := by
    have readOutcome := reopenMarkedBoundedWith_readOutcome directory attempt.readOptional attempt.list attempt.lstat
      attempt.readBin attempt.readPrefix attempt.removeFile attempt.write attempt.sync attempt.renameFile before
    unfold BoundedReopenAttempt.prepare at reading
    unfold BoundedReopenAttempt.recover
    simp only [readOutcome, reading, exactBounded, size]
    rw [finishBoundedMarkedOpen_eq_full _ _ prepared.valid]
    simp only [finishMarkedOpen, notAligned, Bool.false_eq_true, ite_false, runAt, pure_bind, prepared.valid,
      ite_true, runRepairPlan]
    have order : steps full.newer (decide (full.keeperSize < full.keeperBytes.size)) =
        (steps [] true).take 4 ++ [.replace .syncDirectory] := by
      simpa only [Plan.finishActions, notAligned, Bool.false_eq_true, ite_false, Plan.actions] using schedule
    simp only [order, List.forM_eq_forM, List.forM_append, Bind.bind, EStateM.bind, barrier, metadata]
    simp only [← List.forM_eq_forM, ran, List.forM_cons, List.forM_nil, Bind.bind, EStateM.bind,
      performPaths, Publication.performReplacement]
    cases attempt.sync #[directory.path] reached <;> rfl
  have settledPrepared : Prepared before.syncDirectory target full := by
    refine ⟨prepared.pair, prepared.keeperPrefix, ?_, prepared.through, prepared.start, prepared.names,
      prepared.keeperRead⟩
    simp [LaterNames.Beyond, laterEmpty.1, laterEmpty.2]
  have projection : before.syncDirectory.withKeeperInodes previous = before.syncDirectory :=
    congrArg FileImage.syncDirectory projected
  obtain ⟨cover, _, trace, covers, retryPlan, retry⟩ := report.coversUnsettledReplacement previous replacement
    settledPrepared rfl laterEmpty projection oldTarget distinct fresh allowed
  have sameAfter (inodes : WalInodeImage) : reached.withKeeperInodes inodes =
      (before.syncDirectory.withScratch none).withKeeperInodes inodes := by rw [exactReach]; rfl
  have selected : bounded.keeperBytes = target.trimmed := by
    simpa only [exactBounded] using prepared.replacementBytes
  refine ⟨target, full, cover, retryPlan, admitted, selected, reachedNext, exactReach, recovery,
    prepared.allowVisibleKeeper, EffectTrace.authorized.trans trace, ?_, ?_⟩
  · simpa only [sameAfter] using covers
  · simpa only [sameAfter] using retry

end Alvoki.Storage.WalSegmentRepair
