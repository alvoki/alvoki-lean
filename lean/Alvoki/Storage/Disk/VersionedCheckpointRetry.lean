import Alvoki.Storage.Disk.VersionedCheckpointPublication

namespace Alvoki.Storage.CheckpointPublication
open Manifest

/-- Count the prefix of shared schedule operations that took effect. A
reported failure ends the attempt, but can include its own effect. -/
private def reportEffect (report : Step → StepReport) (step : Step) : EStateM Unit Nat Unit :=
  fun cut =>
    match report step with
    | .success => .ok () (cut + 1)
    | .failure tookEffect => .error () (if tookEffect then cut + 1 else cut)

/-- Run the shared schedule with reported effects, then interpret the resulting
prefix using the plan's actual versioned manifest bytes. -/
def Image.runVersionedWithReports (initial : Image) (next : VersionedRunSet)
    (report : Step → StepReport) : Option (EStateM.Result Unit Image Unit) :=
  match run next.files.length (reportEffect report) 0 with
  | .ok _ cut => (initial.executeVersioned next cut).map (EStateM.Result.ok ())
  | .error _ cut => (initial.executeVersioned next cut).map (EStateM.Result.error ())

/-- A primitive report describes whether its operation took effect. The
reported error itself is retained by the caller, independently of the cut. -/
def StepReport.Observes (report : StepReport) (before : Nat)
    (result : EStateM.Result IO.Error Nat Unit) : Prop :=
  match report, result with
  | .success, .ok _ after => after = before + 1
  | .failure applied, .error _ after => after = if applied then before + 1 else before
  | _, _ => False

/-- Require a report only after the actual preceding callbacks succeeded. -/
def ReachedFileReports (report : Step → StepReport) (perform : Step → EStateM IO.Error Nat Unit)
    (actions : List Step) (start : Nat) : Prop :=
  ∀ done action todo, actions = done ++ action :: todo → ∀ before,
    (done.forM perform) start = .ok () before → (report action).Observes before (perform action before)

private def withoutCheckpointError (result : EStateM.Result IO.Error Nat Unit) : EStateM.Result Unit Nat Unit :=
  match result with
  | .ok value after => .ok value after
  | .error _ after => .error () after

private theorem reportsMatchSchedule (report : Step → StepReport) (perform : Step → EStateM IO.Error Nat Unit)
    (actions : List Step) (start : Nat)
    (observed : ReachedFileReports report perform actions start) :
    withoutCheckpointError ((actions.forM perform) start) = (actions.forM (reportEffect report)) start := by
  induction actions generalizing start with
  | nil => rfl
  | cons action rest ih =>
    have current := observed [] action rest rfl start rfl
    change withoutCheckpointError (EStateM.bind (perform action) (fun _ => rest.forM perform) start) =
      EStateM.bind (reportEffect report action) (fun _ => rest.forM (reportEffect report)) start
    cases status : report action <;> cases actual : perform action start <;>
      simp only [status, actual, StepReport.Observes] at current
    · rename_i value after
      have later : ReachedFileReports report perform rest after := by
        intro done step todo order before reached
        apply observed (action :: done) step todo (by rw [order]; rfl) before
        change EStateM.bind (perform action) (fun _ => done.forM perform) start = .ok () before
        simpa only [EStateM.bind, actual] using reached
      simpa only [EStateM.bind, actual, reportEffect, status, ← current] using ih _ later
    · simp only [EStateM.bind, actual, reportEffect, status, withoutCheckpointError, current]

/-- Match a failed file-dispatch schedule to its modeled publication cut.
The image describes selectable manifests and durable run bytes. A private
scratch file may have changed during an operation that failed. -/
theorem Image.runVersionedWithObservedFailure (initial : Image) (next : VersionedRunSet)
    (report : Step → StepReport) (perform : Step → EStateM IO.Error Nat Unit)
    (observed : ReachedFileReports report perform (steps next.files.length) 0)
    {cause : IO.Error} {cut : Nat} (failed : run next.files.length perform 0 = .error cause cut) :
    ∃ published, initial.executeVersioned next cut = some published ∧
      initial.runVersionedWithReports next report = some (.error () published) := by
  have counted := reportsMatchSchedule report perform (steps next.files.length) 0 observed
  change withoutCheckpointError (run next.files.length perform 0) =
    run next.files.length (reportEffect report) 0 at counted
  rw [failed] at counted
  obtain ⟨published, exactFiles⟩ := initial.executeVersioned_exists next cut
  refine ⟨published, exactFiles, ?_⟩
  unfold runVersionedWithReports
  rw [← counted]
  simp [withoutCheckpointError, exactFiles]

theorem Image.runVersionedWithReports_exists (initial : Image) (next : VersionedRunSet)
    (report : Step → StepReport) : ∃ result, initial.runVersionedWithReports next report = some result := by
  unfold runVersionedWithReports
  cases run next.files.length (reportEffect report) 0 with
  | ok _ cut =>
    obtain ⟨after, applied⟩ := initial.executeVersioned_exists next cut
    exact ⟨.ok () after, by simp [applied]⟩
  | error _ cut =>
    obtain ⟨after, applied⟩ := initial.executeVersioned_exists next cut
    exact ⟨.error () after, by simp [applied]⟩

private theorem reportEffect_success_length (report : Step → StepReport) (actions : List Step)
    (start : Nat) {cut : Nat} (reports : actions.forM (reportEffect report) start = .ok () cut) :
    cut = start + actions.length := by
  induction actions generalizing start with
  | nil =>
    change EStateM.Result.ok () start = EStateM.Result.ok () cut at reports
    cases reports
    simp
  | cons first rest ih =>
    change EStateM.bind (reportEffect report first) (fun _ => rest.forM (reportEffect report)) start =
      .ok () cut at reports
    cases outcome : report first with
    | failure tookEffect => simp [EStateM.bind, reportEffect, outcome] at reports
    | success =>
      have stops : rest.forM (reportEffect report) (start + 1) = .ok () cut := by
        simpa only [EStateM.bind, reportEffect, outcome] using reports
      have count := ih (start + 1) stops
      simp only [List.length_cons]
      omega

theorem Image.runVersionedWithReports_outcome (initial : Image) (next : VersionedRunSet)
    (report : Step → StepReport) {result : EStateM.Result Unit Image Unit}
    (ran : initial.runVersionedWithReports next report = some result) :
    match result with
    | .ok _ after => initial.executeVersioned next (steps next.files.length).length = some after
    | .error _ after => ∃ cut, initial.executeVersioned next cut = some after := by
  unfold runVersionedWithReports at ran
  cases counted : run next.files.length (reportEffect report) 0 with
  | ok value cut =>
    rw [counted] at ran
    obtain ⟨after, applied, rfl⟩ := Option.map_eq_some_iff.mp ran
    cases value
    have length := reportEffect_success_length report (steps next.files.length) 0 counted
    simpa only [length, Nat.zero_add] using applied
  | error failure cut =>
    rw [counted] at ran
    obtain ⟨after, applied, rfl⟩ := Option.map_eq_some_iff.mp ran
    exact ⟨cut, applied⟩

/-- A successful run of the reported callbacks takes every effect in the
shared schedule. The resulting image is the complete versioned checkpoint. -/
theorem Image.runVersionedWithObservedSuccess (initial : Image) (next : VersionedRunSet)
    (report : Step → StepReport) (perform : Step → EStateM IO.Error Nat Unit)
    (observed : ReachedFileReports report perform (steps next.files.length) 0)
    {cut : Nat} (succeeded : run next.files.length perform 0 = .ok () cut) :
    cut = (steps next.files.length).length ∧
      ∃ published, initial.executeVersioned next cut = some published ∧
        initial.runVersionedWithReports next report = some (.ok () published) := by
  have counted := reportsMatchSchedule report perform (steps next.files.length) 0 observed
  change withoutCheckpointError (run next.files.length perform 0) =
    run next.files.length (reportEffect report) 0 at counted
  rw [succeeded] at counted
  have length := reportEffect_success_length report (steps next.files.length) 0 counted.symm
  obtain ⟨published, exactFiles⟩ := initial.executeVersioned_exists next cut
  refine ⟨by simpa using length, published, exactFiles, ?_⟩
  unfold runVersionedWithReports
  rw [← counted]
  simp [withoutCheckpointError, exactFiles]

/-- Retry publication against a fixed synced WAL watermark. A failed attempt
leaves its cut visible, a power loss chooses an admitted durable binding, and
a successful reopen barrier settles the visible binding. -/
inductive VersionedRetry (walSequence : UInt64) (expected : Checkpoint → List ByteArray → Prop) :
    Image → Image → Prop where
  | refl (image) : VersionedRetry walSequence expected image image
  | attempt (prior : VersionedRetry walSequence expected initial before) (next : VersionedRunSet)
      (fresh : before.UnreachableVersioned next.manifest.header.generation)
      (decoded : VersionedCheckpoint.decode next.manifest.encode = .ok next.manifest)
      (count : next.manifest.header.runCount.toNat = next.files.length)
      (checked : next.manifest.ValidatesFiles next.files)
      (covered : next.manifest.header.committed ≤ walSequence)
      (witness : expected next.manifest.header next.files)
      (cut : Nat) (ran : before.executeVersioned next cut = some after) :
      VersionedRetry walSequence expected initial after
  | crash (prior : VersionedRetry walSequence expected initial before)
      (survives : candidate ∈ before.manifest.crashImages) :
      VersionedRetry walSequence expected initial { before with manifest := .settled candidate }
  | reopen (prior : VersionedRetry walSequence expected initial before) :
      VersionedRetry walSequence expected initial before.settleVisible

theorem VersionedRetry.reported {initial before : Image} {walSequence : UInt64}
    {expected : Checkpoint → List ByteArray → Prop}
    (prior : VersionedRetry walSequence expected initial before) (next : VersionedRunSet)
    (fresh : before.UnreachableVersioned next.manifest.header.generation)
    (decoded : VersionedCheckpoint.decode next.manifest.encode = .ok next.manifest)
    (count : next.manifest.header.runCount.toNat = next.files.length)
    (checked : next.manifest.ValidatesFiles next.files)
    (covered : next.manifest.header.committed ≤ walSequence)
    (witness : expected next.manifest.header next.files)
    (report : Step → StepReport) {result : EStateM.Result Unit Image Unit}
    (ran : before.runVersionedWithReports next report = some result) :
    match result with
    | .ok _ after | .error _ after => VersionedRetry walSequence expected initial after := by
  have effect := before.runVersionedWithReports_outcome next report ran
  cases result with
  | ok value after => exact .attempt prior next fresh decoded count checked covered witness _ effect
  | error failure after =>
    obtain ⟨cut, applied⟩ := effect
    exact .attempt prior next fresh decoded count checked covered witness cut applied

theorem checkpointVersioned_retry_valid {initial after : Image} {walSequence : UInt64}
    {expected : Checkpoint → List ByteArray → Prop}
    (valid : initial.ValidVersioned walSequence expected)
    (trace : VersionedRetry walSequence expected initial after) :
    after.ValidVersioned walSequence expected := by
  induction trace with
  | refl => exact valid
  | attempt _ _ fresh decoded count checked covered witness cut ran previous =>
    exact checkpointVersioned_cut_valid previous fresh decoded count checked covered witness cut ran
  | crash _ survives previous =>
    exact Publication.Image.settled_valid (previous.crashValid _ survives)
  | reopen _ previous => exact Publication.Image.settled_valid previous.activeValid

theorem VersionedRetry.accepts {initial after : Image} {walSequence : UInt64}
    {expected : Checkpoint → List ByteArray → Prop} {binding : Option ByteArray}
    (trace : VersionedRetry walSequence expected initial after)
    (valid : initial.ValidVersioned walSequence expected)
    (selected : after.manifest.active = binding ∨ binding ∈ after.manifest.crashImages) :
    after.AcceptsVersioned walSequence expected binding := by
  have final := checkpointVersioned_retry_valid valid trace
  rcases selected with active | survives
  · simpa only [active] using final.activeValid
  · exact final.crashValid _ survives

/-- Any selected manifest after retries decodes from its actual bytes and names
the same ordered durable run bytes checked by that manifest version. -/
theorem checkpointVersioned_retry_selected_runs {initial after : Image} {walSequence : UInt64}
    {expected : Checkpoint → List ByteArray → Prop} {bytes : ByteArray}
    (valid : initial.ValidVersioned walSequence expected)
    (trace : VersionedRetry walSequence expected initial after)
    (selected : after.manifest.active = some bytes ∨ some bytes ∈ after.manifest.crashImages) :
    ∃ manifest files, VersionedCheckpoint.decode bytes = .ok manifest ∧
      (List.range manifest.header.runCount.toNat).mapM (after.durable manifest.header.generation) = some files ∧
      expected manifest.header files ∧ manifest.ValidatesFiles files ∧ manifest.header.committed ≤ walSequence := by
  have accepted := trace.accepts valid selected
  have decodedWitness := accepted
  obtain ⟨manifest, decoded, _⟩ := decodedWitness
  obtain ⟨files, ordered, witness, checked, covered⟩ := Image.acceptsVersioned_runs accepted decoded
  exact ⟨manifest, files, decoded, ordered, witness, checked, covered⟩

/-- The shared versioned reader loads the table from the exact accepted bytes
after a retry. A successful read reports the generation that names those runs. -/
theorem VersionedRetry.loaded_lineage {initial after : Image} {walSequence : UInt64}
    {expected : Checkpoint → List ByteArray → Prop} {bytes : ByteArray} {table : PackedTable} {generation : UInt64}
    (trace : VersionedRetry walSequence expected initial after)
    (valid : initial.ValidVersioned walSequence expected)
    (active : after.manifest.active = some bytes)
    (reads : VersionedCheckpointFileReads after.durable (some bytes))
    (opened : reads.result = .ok (some (table, generation))) :
    ∃ manifest files, VersionedCheckpoint.decode bytes = .ok manifest ∧
      (List.range manifest.header.runCount.toNat).mapM (after.durable generation) = some files ∧
      (List.range manifest.header.runCount.toNat).mapM (reads.readRun generation) = .ok files ∧
      expected manifest.header files ∧ manifest.ValidatesFiles files ∧ loadRunSet manifest.header files = .ok table ∧
      generation = manifest.header.generation ∧ manifest.header.committed ≤ walSequence := by
  have accepted := trace.accepts valid (.inl active)
  have decodedWitness := accepted
  obtain ⟨manifest, decoded, _⟩ := decodedWitness
  obtain ⟨files, durable, observed, witness, checked, loaded, generationEq, covered⟩ :=
    reads.loaded_lineage accepted decoded opened
  rw [generationEq]
  exact ⟨manifest, files, decoded, durable, observed, witness, checked, loaded, rfl, covered⟩

/-- After settling the visible binding, the next generation can be reused
even if its files were left by a discarded attempt. The generation comes
from the raw manifest selected at reopen, or zero when it was absent. -/
theorem Image.nextVersionedGeneration_unreachable_after_reopen (image : Image) (installedGeneration : UInt64)
    (loaded : (image.manifest.active = none ∧ installedGeneration = 0) ∨
      ∃ bytes selected, image.manifest.active = some bytes ∧ VersionedCheckpoint.decode bytes = .ok selected ∧
        installedGeneration = selected.header.generation)
    (fits : installedGeneration.toNat + 1 < UInt64.size) :
    image.settleVisible.UnreachableVersioned (UInt64.ofNat (installedGeneration.toNat + 1)) := by
  intro bytes selectable manifest decoded
  have active : image.manifest.active = some bytes := by
    rcases selectable with same | survives
    · exact same
    · exact (List.mem_singleton.mp survives).symm
  rcases loaded with ⟨missing, _⟩ | ⟨loadedBytes, loadedManifest, visible, read, generation⟩
  · rw [missing] at active
    contradiction
  · have sameBytes : bytes = loadedBytes := Option.some.inj (active.symm.trans visible)
    rw [sameBytes, read] at decoded
    cases decoded
    intro same
    have naturals := congrArg UInt64.toNat same
    rw [UInt64.toNat_ofNat_of_lt' fits, generation] at naturals
    omega

end Alvoki.Storage.CheckpointPublication
