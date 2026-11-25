import Alvoki.Storage.Disk.CheckpointRunWriteCustody
import Alvoki.Storage.Disk.SegmentedBatchDatabaseTrace
import Alvoki.Storage.Disk.RunUnlinkEffects

namespace Alvoki.Storage.CheckpointPublication

open System
open DiskSession

private theorem runSteps_returned {state : Type} (perform : Step → EStateM IO.Error state Unit)
    (count : Nat) (atRun : Nat → state)
    (pairs : ∀ index < count,
      (perform (.writeRun index) >>= fun _ => perform (.syncRun index)) (atRun index) =
        .ok () (atRun (index + 1))) :
    ((runSteps count).forM perform) (atRun 0) = .ok () (atRun count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have prior := ih (fun index within => pairs index (Nat.lt_succ_of_lt within))
    rw [show runSteps (count + 1) = runSteps count ++ [.writeRun count, .syncRun count] by
      simp [runSteps, List.range_succ], List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM]
    change EStateM.bind ((runSteps count).forM perform)
      (fun _ => ([Step.writeRun count, .syncRun count].forM perform)) (atRun 0) = _
    rw [show ([Step.writeRun count, .syncRun count].forM perform) =
      (perform (.writeRun count) >>= fun _ => perform (.syncRun count)) by
      simp [List.forM_eq_forM, List.forM_cons, List.forM_nil]]
    simp only [EStateM.bind, prior, pairs count (Nat.lt_succ_self count)]

/-- States reached after each run's adjacent write and sync and after each
of the following directory and manifest operations. Each equality is a
report of the actual callback at the state left by its predecessor. -/
structure SuccessfulCheckpointSteps {state : Type}
    (perform : Step → EStateM IO.Error state Unit) (count : Nat) where
  atRun : Nat → state
  runsSettled : state
  staged : state
  stagedSynced : state
  renamed : state
  completed : state
  pairs : ∀ index < count,
    (perform (.writeRun index) >>= fun _ => perform (.syncRun index)) (atRun index) =
      .ok () (atRun (index + 1))
  syncRunsDirectory : perform .syncRunsDirectory (atRun count) = .ok () runsSettled
  stageManifest : perform (.manifest .writeStaged) runsSettled = .ok () staged
  syncManifest : perform (.manifest .syncStaged) staged = .ok () stagedSynced
  renameManifest : perform (.manifest .renameStaged) stagedSynced = .ok () renamed
  syncManifestDirectory : perform (.manifest .syncDirectory) renamed = .ok () completed

/-- Run the actual shared writer's schedule from the individual reached
reports. No report of the whole return is needed. -/
theorem SuccessfulCheckpointSteps.returns {state : Type} {perform : Step → EStateM IO.Error state Unit}
    {count : Nat} (observed : SuccessfulCheckpointSteps perform count) :
    run count perform (observed.atRun 0) = .ok () observed.completed := by
  have pairs := runSteps_returned perform count observed.atRun observed.pairs
  simp only [run, steps, Publication.steps, List.map_cons, List.map_nil, List.forM_eq_forM, List.forM_append]
  change EStateM.bind (EStateM.bind ((runSteps count).forM perform) (fun _ => [Step.syncRunsDirectory].forM perform))
    (fun _ => ([Step.manifest .writeStaged, .manifest .syncStaged, .manifest .renameStaged,
      .manifest .syncDirectory].forM perform)) (observed.atRun 0) = _
  simp only [EStateM.bind, pairs, List.forM_eq_forM, List.forM_cons, List.forM_nil,
    Bind.bind, observed.syncRunsDirectory, observed.stageManifest, observed.syncManifest, observed.renameManifest,
    observed.syncManifestDirectory, Pure.pure, EStateM.pure]

/-- Synced run bytes accumulate before the run directory barrier. That
barrier settles the run names. The subsequent manifest callbacks preserve
the run view until the final directory barrier, which settles it again. -/
theorem SuccessfulCheckpointSteps.durableRuns {state : Type}
    {perform : Step → EStateM IO.Error state Unit} {count : Nat} {files : List ByteArray}
    (observed : SuccessfulCheckpointSteps perform count)
    (runs : state → RunUnlinkImage) (generation : UInt64)
    (synced : ∀ index < count, (runs (observed.atRun (index + 1))).visible generation index = files[index]?)
    (preserved : ∀ index < count, ∀ prior < index,
      (runs (observed.atRun (index + 1))).visible generation prior =
        (runs (observed.atRun index)).visible generation prior)
    (runNames : runs observed.runsSettled = (runs (observed.atRun count)).syncDirectory)
    (stage : runs observed.staged = runs observed.runsSettled)
    (manifestData : runs observed.stagedSynced = runs observed.staged)
    (rename : runs observed.renamed = runs observed.stagedSynced)
    (manifestNames : runs observed.completed = (runs observed.renamed).syncDirectory) :
    ∀ index < count, (runs observed.completed).guaranteed generation index = files[index]? := by
  have syncedPrefix (through : Nat) (within : through ≤ count) :
      ∀ index < through, (runs (observed.atRun through)).visible generation index = files[index]? := by
    induction through with
    | zero => omega
    | succ count ih =>
      intro index inside
      by_cases same : index = count
      · subst index
        exact synced count within
      · have prior : index < count := by omega
        rw [preserved count within index prior]
        exact ih (Nat.le_trans (Nat.le_succ _) within) index prior
  have settled : runs observed.completed = .settled (runs (observed.atRun count)).visible := by
    rw [manifestNames, rename, manifestData, stage, runNames]
    rfl
  intro index inside
  rw [settled]
  exact congrFun (congrFun (congrArg Image.durable
    (RunUnlinkImage.project_settled (runs (observed.atRun count)).visible (.settled none))) generation) index
    |>.trans (syncedPrefix count (Nat.le_refl _) index inside)

/-- The manifest's own four reached effects settle the new manifest bytes
at the same physical endpoint as the run guarantees. -/
theorem SuccessfulCheckpointSteps.manifestSettled {state : Type}
    {perform : Step → EStateM IO.Error state Unit} {count : Nat}
    (observed : SuccessfulCheckpointSteps perform count) (manifest : state → Publication.Image) (bytes : ByteArray)
    (staged : (manifest observed.runsSettled).step bytes .writeStaged = some (manifest observed.staged))
    (synced : (manifest observed.staged).step bytes .syncStaged = some (manifest observed.stagedSynced))
    (renamed : (manifest observed.stagedSynced).step bytes .renameStaged = some (manifest observed.renamed))
    (settled : (manifest observed.renamed).step bytes .syncDirectory = some (manifest observed.completed)) :
    manifest observed.completed = .settled (some bytes) := by
  have executed :
      (manifest observed.runsSettled).execute bytes Publication.steps = some (manifest observed.completed) := by
    simp only [Publication.Image.execute, Publication.steps, List.foldlM_cons, List.foldlM_nil,
      staged, synced, renamed, settled, Bind.bind, Option.bind, Pure.pure]
  exact Option.some.inj (executed.symm.trans (Publication.successful_replace _ _))

/-- Binding and durability projections of the same locally observed file
steps. Report the run at its reached file barrier, preserve earlier run
bindings, and settle names only through the corresponding barriers. -/
structure CheckpointBindingReports {state : Type} {perform : Step → EStateM IO.Error state Unit} {count : Nat}
    (observed : SuccessfulCheckpointSteps perform count)
    (runs : state → RunUnlinkImage) (manifest : state → Publication.Image)
    (generation : UInt64) (files : List ByteArray) (bytes : ByteArray) : Prop where
  syncedRun : ∀ index < count, (runs (observed.atRun (index + 1))).visible generation index = files[index]?
  previousRuns : ∀ index < count, ∀ prior < index,
    (runs (observed.atRun (index + 1))).visible generation prior =
      (runs (observed.atRun index)).visible generation prior
  runNames : runs observed.runsSettled = (runs (observed.atRun count)).syncDirectory
  stageRuns : runs observed.staged = runs observed.runsSettled
  syncRuns : runs observed.stagedSynced = runs observed.staged
  renameRuns : runs observed.renamed = runs observed.stagedSynced
  finalRuns : runs observed.completed = (runs observed.renamed).syncDirectory
  stageManifest : (manifest observed.runsSettled).step bytes .writeStaged = some (manifest observed.staged)
  syncManifest : (manifest observed.staged).step bytes .syncStaged = some (manifest observed.stagedSynced)
  renameManifest : (manifest observed.stagedSynced).step bytes .renameStaged = some (manifest observed.renamed)
  finalManifest : (manifest observed.renamed).step bytes .syncDirectory = some (manifest observed.completed)

/-- Project the reached file or cache state while retaining the reported
success or error. -/
def countReached {state : Type} (count : state → Nat) :
    EStateM.Result IO.Error state Unit → EStateM.Result IO.Error Nat Unit
  | .ok value after => .ok value (count after)
  | .error cause after => .error cause (count after)

private theorem stepCount_matches {state : Type} (count : state → Nat)
    (physical : Step → EStateM IO.Error state Unit) (modeled : Step → EStateM IO.Error Nat Unit)
    (actions : List Step) (initial : state)
    (projects : ∀ (done : List Step) step todo reached, actions = done ++ step :: todo →
      (done.forM physical) initial = .ok () reached →
      countReached count (physical step reached) = modeled step (count reached)) :
    countReached count ((actions.forM physical) initial) = (actions.forM modeled) (count initial) := by
  induction actions generalizing initial with
  | nil => rfl
  | cons step rest ih =>
    have first := projects [] step rest initial rfl rfl
    change countReached count (EStateM.bind (physical step) (fun _ => rest.forM physical) initial) =
      EStateM.bind (modeled step) (fun _ => rest.forM modeled) (count initial)
    unfold EStateM.bind
    rw [← first]
    cases next : physical step initial with
    | error cause reached => rfl
    | ok value after =>
      cases value
      change countReached count ((rest.forM physical) after) = (rest.forM modeled) (count after)
      apply ih
      intro done action todo reached order recorded
      apply projects (step :: done) action todo reached (congrArg (List.cons step) order)
      change EStateM.bind (physical step) (fun _ => done.forM physical) initial = .ok () reached
      simpa only [EStateM.bind, next] using recorded

/-- Project the exact reached operation reports to the checkpoint model's
step counts. This derives the counted successful return from the same
timeline as the physical runner. -/
theorem SuccessfulCheckpointSteps.returnsCounted {state : Type}
    {perform : Step → EStateM IO.Error state Unit} {count : Nat}
    (observed : SuccessfulCheckpointSteps perform count) (effectCount : state → Nat)
    (modeled : Step → EStateM IO.Error Nat Unit)
    (projects : ∀ (done : List Step) step todo reached, steps count = done ++ step :: todo →
      (done.forM perform) (observed.atRun 0) = .ok () reached →
      countReached effectCount (perform step reached) = modeled step (effectCount reached)) :
    run count modeled (effectCount (observed.atRun 0)) = .ok () (effectCount observed.completed) := by
  have projected := stepCount_matches effectCount perform modeled (steps count) (observed.atRun 0) projects
  change countReached effectCount (run count perform (observed.atRun 0)) = _ at projected
  rw [observed.returns] at projected
  exact projected.symm

end Alvoki.Storage.CheckpointPublication

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication

/-- A complete reached checkpoint returns the same flushed table and lock
owner as its counted publication projection. The resulting writer is
ready in the mixed trace. Its existing WAL history and the exact new
ordered checkpoint bindings follow from the selected publication. -/
theorem SegmentedBatchDatabaseTrace.checkpointFromObservedSteps {state : Type}
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (initialReady : initial.RetainedReady directory initialDescriptor)
    (attempt : SegmentedCheckpointReport directory before)
    (flushed : (flushForCheckpoint before.installed.table id : Except String PackedTable) = .ok attempt.table)
    (generationFits : before.installed.generation.toNat + 1 < UInt64.size)
    (runCountFits : attempt.table.runs.length < UInt64.size)
    (encoded : encodeCheckpointIntegrityManifest attempt.table (SegmentedCheckpointReport.generation before) = .ok attempt.manifest)
    (writeRun writeStaged : FilePath → ByteArray → EStateM IO.Error state Unit)
    (sync : Array FilePath → EStateM IO.Error state Unit)
    (rename : FilePath → FilePath → EStateM IO.Error state Unit)
    (runs : state → RunUnlinkImage) (manifest : state → Publication.Image) :
    let perform := performCheckpointFileStep directory (SegmentedCheckpointReport.generation before)
      attempt.table.runs.toArray (directory.file .stagedManifest) attempt.manifest
      (fun found => match found with
        | some run => pure run
        | none => throw (IO.userError "checkpoint run index is out of bounds"))
      writeRun writeStaged sync rename
    ∀ (observed : SuccessfulCheckpointSteps perform attempt.table.runs.length) (effectCount : state → Nat),
      effectCount (observed.atRun 0) = 0 →
      effectCount observed.completed = attempt.cut →
      ReachedFileReports attempt.report attempt.perform (steps attempt.table.runs.length) 0 →
      (∀ (done : List Step) step todo reached, steps attempt.table.runs.length = done ++ step :: todo →
        (done.forM perform) (observed.atRun 0) = .ok () reached →
        countReached effectCount (perform step reached) = attempt.perform step (effectCount reached)) →
      CheckpointBindingReports observed runs manifest (SegmentedCheckpointReport.generation before)
        attempt.plan.files attempt.manifest →
      ∃ after, attempt.Installs after ∧ after.RetainedReady directory writer ∧
        runPreparedCheckpoint attempt.prepared perform
          (.ready before.installed, ⟨observed.atRun 0, before.owners⟩) =
            .ok () (.ready after.installed, ⟨observed.completed, after.owners⟩) ∧
        manifest observed.completed = after.published.manifest ∧
        (∀ index < attempt.table.runs.length, (runs observed.completed).guaranteed after.installed.generation index =
          after.published.durable after.installed.generation index) ∧
        SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
          (log ++ [.ordinary [⟨[], none⟩]]) writer after := by
  intro perform observed effectCount initialCount finalCount reached projects bindings
  have counted := observed.returnsCounted effectCount attempt.perform projects
  rw [initialCount, finalCount] at counted
  have valid : attempt.Valid := ⟨flushed, generationFits, runCountFits, encoded, reached, counted⟩
  obtain ⟨after, installed, ready, _⟩ := attempt.installsRetained valid (trace.preservesRetained initialReady).1
  have ran := observed.returns
  have native : runPreparedCheckpoint attempt.prepared perform
      (.ready before.installed, ⟨observed.atRun 0, before.owners⟩) =
        .ok () (.ready after.installed, ⟨observed.completed, after.owners⟩) := by
    rw [installed.installed, installed.owners]
    simp only [runPreparedCheckpoint, Bind.bind, EStateM.bind, modify, modifyGet, MonadStateOf.modifyGet,
      EStateM.modifyGet, SegmentedCheckpointReport.prepared, ran]
  have published := observed.manifestSettled manifest attempt.manifest bindings.stageManifest
    bindings.syncManifest bindings.renameManifest bindings.finalManifest
  have runFiles := observed.durableRuns runs (SegmentedCheckpointReport.generation before) bindings.syncedRun
    bindings.previousRuns bindings.runNames bindings.stageRuns bindings.syncRuns bindings.renameRuns bindings.finalRuns
  refine ⟨after, installed, ready, native, published.trans installed.settled.symm, ?_,
    .ordinary trace (.writes .start (.checkpoint .empty attempt valid installed))⟩
  intro index within
  rw [installed.installed]
  exact (runFiles index within).trans (installed.runs index).symm

end Alvoki.Storage.DiskSession
