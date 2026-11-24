import Alvoki.Storage.Disk.VersionedCheckpointLineage

namespace Alvoki.Storage.CheckpointPublication
open Manifest

/-- The manifest supplies the semantic header for the existing run schedule. -/
structure VersionedRunSet where
  manifest : VersionedCheckpoint
  files : List ByteArray

def VersionedRunSet.runSet (plan : VersionedRunSet) : RunSet := ⟨plan.manifest.header, plan.files⟩

def VersionedRunSet.integrity (next : RunSet) : VersionedRunSet :=
  ⟨.integrity (IntegrityCheckpoint.fromRuns next.header next.files), next.files⟩

private def runBarrier (runCount : Nat) : List Step :=
  runSteps runCount ++ [.syncRunsDirectory]

private theorem schedule_split (runCount cut : Nat) :
    (steps runCount).take cut = (runBarrier runCount).take cut ++
      (Publication.steps.take (cut - (runBarrier runCount).length)).map Step.manifest := by
  rw [show steps runCount = runBarrier runCount ++ Publication.steps.map Step.manifest from rfl,
    List.take_append, ← List.map_take]

/-- Run the same checkpoint schedule, supplying the selected version's bytes
to the manifest steps. Cuts before the run barrier have an empty manifest suffix. -/
def Image.executeVersioned (initial : Image) (next : VersionedRunSet) (cut : Nat) : Option Image := do
  let barrier := runBarrier next.files.length
  let written ← initial.execute next.runSet (barrier.take cut)
  let manifest ← written.manifest.execute next.manifest.encode (Publication.steps.take (cut - barrier.length))
  return { written with manifest }

theorem Image.executeVersioned_legacy (initial : Image) (next : RunSet) (cut : Nat) :
    initial.executeVersioned ⟨.legacy next.header, next.files⟩ cut =
      initial.execute next ((steps next.files.length).take cut) := by
  rw [schedule_split, Image.execute_split_manifest]
  cases next
  rfl

theorem checkpointVersioned_complete (initial : Image) (next : VersionedRunSet) :
    ∃ after, initial.executeVersioned next (steps next.files.length).length = some after ∧
      after.manifest = .settled (some next.manifest.encode) ∧
      (∀ index, after.durable next.manifest.header.generation index = next.files[index]?) ∧
      ∀ generation, generation ≠ next.manifest.header.generation →
        ∀ index, after.durable generation index = initial.durable generation index := by
  obtain ⟨written, ran, _, durable, preserved⟩ := checkpoint_runs_complete initial next.runSet
  have length : (steps next.files.length).length =
      (runBarrier next.files.length).length + Publication.steps.length := by
    change (runBarrier next.files.length ++ Publication.steps.map Step.manifest).length = _
    simp
  have takeRuns : (runBarrier next.files.length).take (steps next.files.length).length =
      runBarrier next.files.length := by
    apply List.take_of_length_le
    rw [length]
    omega
  have takeManifest : Publication.steps.take ((steps next.files.length).length -
      (runBarrier next.files.length).length) = Publication.steps := by
    rw [length, Nat.add_sub_cancel_left, List.take_length]
  refine ⟨{ written with manifest := .settled (some next.manifest.encode) }, ?_, rfl, durable, preserved⟩
  have runPrefix : initial.execute next.runSet (runBarrier next.files.length) = some written := ran
  simp only [Image.executeVersioned, takeRuns, takeManifest, runPrefix,
    Publication.successful_replace]
  rfl

/-- A complete integrity checkpoint publishes the exact ordered runs and the
v2 manifest built from their fingerprints. WAL coverage and the caller's
semantic checkpoint witness are explicit. -/
theorem checkpointIntegrity_complete {walSequence : UInt64} {expected : Checkpoint → List ByteArray → Prop}
    (initial : Image) (next : RunSet)
    (floor : next.header.floor ≤ next.header.committed) (count : next.files.length = next.header.runCount.toNat)
    (fits : ∀ bytes ∈ next.files, bytes.size < UInt64.size)
    (covered : next.header.committed ≤ walSequence) (witness : expected next.header next.files) :
    let plan := VersionedRunSet.integrity next
    ∃ after, initial.executeVersioned plan (steps next.files.length).length = some after ∧
      after.manifest = .settled (some plan.manifest.encode) ∧
      after.AcceptsVersioned walSequence expected (some plan.manifest.encode) ∧
      ∀ index, after.durable next.header.generation index = next.files[index]? := by
  dsimp only
  let metadata := IntegrityCheckpoint.fromRuns next.header next.files
  obtain ⟨after, published, manifest, durable, _⟩ := checkpointVersioned_complete initial (VersionedRunSet.integrity next)
  have decoded : IntegrityCheckpoint.decode metadata.encode = .ok metadata :=
    IntegrityCheckpoint.decode_encode metadata floor (by simpa [metadata, IntegrityCheckpoint.fromRuns] using count)
  have checked := IntegrityCheckpoint.validateRuns_fromRuns next.header next.files count fits
  refine ⟨after, published, manifest, (Image.acceptsVersioned_integrity_iff decoded).mpr ?_, durable⟩
  exact ⟨next.header, next.files, Manifest.decode_encode next.header floor, ⟨witness, checked⟩,
    covered, count.symm, fun index _ => durable index⟩

/-- Freshness checks the actual raw bindings and recognizes both manifest versions. -/
def Image.UnreachableVersioned (image : Image) (generation : UInt64) : Prop :=
  ∀ bytes, (image.manifest.active = some bytes ∨ some bytes ∈ image.manifest.crashImages) →
    ∀ selected, VersionedCheckpoint.decode bytes = .ok selected → selected.header.generation ≠ generation

def Image.ValidVersioned (image : Image) (walSequence : UInt64)
    (expected : Checkpoint → List ByteArray → Prop) : Prop :=
  image.manifest.Valid (image.AcceptsVersioned walSequence expected)

private theorem keeps_versioned_acceptance {before written : Image} {walSequence : UInt64}
    {expected : Checkpoint → List ByteArray → Prop} {generation : UInt64}
    (preserved : ∀ other, other ≠ generation → ∀ index, written.durable other index = before.durable other index)
    (fresh : before.UnreachableVersioned generation) {binding : Option ByteArray}
    (selectable : before.manifest.active = binding ∨ binding ∈ before.manifest.crashImages)
    (accepted : before.AcceptsVersioned walSequence expected binding) :
    written.AcceptsVersioned walSequence expected binding := by
  cases binding with
  | none => trivial
  | some bytes =>
    obtain ⟨selected, decoded, witness⟩ := accepted
    obtain ⟨header, files, canonical, good, covered, count, names⟩ := witness
    have sameHeader := Except.ok.inj
      (canonical.symm.trans (Manifest.decode_encode _ (VersionedCheckpoint.decoded_floor decoded)))
    have different : header.generation ≠ generation := by
      rw [sameHeader]
      exact fresh bytes selectable selected decoded
    exact ⟨selected, decoded, header, files, canonical, good, covered, count,
      fun index inside => (preserved _ different index).trans (names index inside)⟩

/-- Every cut of the shared publication schedule preserves recoverability
for both versions. The new files are durable before the manifest suffix can
select them, and no previously selectable manifest uses the new generation. -/
theorem checkpointVersioned_cut_valid {initial after : Image} {next : VersionedRunSet} {walSequence : UInt64}
    {expected : Checkpoint → List ByteArray → Prop}
    (valid : initial.ValidVersioned walSequence expected)
    (fresh : initial.UnreachableVersioned next.manifest.header.generation)
    (decoded : VersionedCheckpoint.decode next.manifest.encode = .ok next.manifest)
    (count : next.manifest.header.runCount.toNat = next.files.length)
    (checked : next.manifest.ValidatesFiles next.files)
    (covered : next.manifest.header.committed ≤ walSequence)
    (witness : expected next.manifest.header next.files)
    (cut : Nat) (ran : initial.executeVersioned next cut = some after) : after.ValidVersioned walSequence expected := by
  by_cases early : cut < (runBarrier next.files.length).length
  · have beforeRuns : cut ≤ (runSteps next.files.length).length := by
      simp [runBarrier] at early
      omega
    have onlyRuns : (runBarrier next.files.length).take cut = (runSteps next.files.length).take cut := by
      rw [runBarrier, List.take_append, Nat.sub_eq_zero_of_le beforeRuns, List.take_zero, List.append_nil]
    have noManifest := Nat.sub_eq_zero_of_le (Nat.le_of_lt early)
    cases written : initial.execute next.runSet ((runSteps next.files.length).take cut) with
    | none => simp [Image.executeVersioned, onlyRuns, written] at ran
    | some fileImage =>
      have imageEq : fileImage = initial := Image.execute_run_cut_unchanged written
      have same : some fileImage = some after := by
        simpa [Image.executeVersioned, onlyRuns, noManifest, written, Publication.Image.execute] using ran
      have afterEq := (Option.some.inj same).symm.trans imageEq
      simpa [afterEq] using valid
  · have allRuns : (runBarrier next.files.length).take cut = runBarrier next.files.length :=
      List.take_of_length_le (Nat.le_of_not_lt early)
    obtain ⟨written, ready, sameManifest, durable, preserved⟩ := checkpoint_runs_complete initial next.runSet
    have allSteps : initial.execute next.runSet (runBarrier next.files.length) = some written := ready
    have earlier : written.ValidVersioned walSequence expected := by
      unfold Image.ValidVersioned
      rw [sameManifest]
      exact ⟨valid.hasCrashImage,
        keeps_versioned_acceptance preserved fresh (.inl rfl) valid.activeValid,
        fun _ survives => keeps_versioned_acceptance preserved fresh (.inr survives) (valid.crashValid _ survives)⟩
    have installed : written.AcceptsVersioned walSequence expected (some next.manifest.encode) :=
      ⟨next.manifest, decoded, next.manifest.header, next.files,
        Manifest.decode_encode _ (VersionedCheckpoint.decoded_floor decoded),
        ⟨witness, checked⟩, covered, count, fun index _ => durable index⟩
    let actions := Publication.steps.take (cut - (runBarrier next.files.length).length)
    change (do
      let files ← initial.execute next.runSet ((runBarrier next.files.length).take cut)
      let manifest ← files.manifest.execute next.manifest.encode actions
      pure { files with manifest }) = some after at ran
    rw [allRuns, allSteps] at ran
    cases applied : written.manifest.execute next.manifest.encode actions with
    | none => simp [applied, bind, Option.bind] at ran
    | some manifest =>
      have imageEq : { written with manifest := manifest } = after := by
        simpa [applied, bind, Option.bind] using ran
      subst after
      have path : Publication.Retry (fun _ bytes => written.AcceptsVersioned walSequence expected (some bytes))
          written.manifest manifest := .attempt (.refl _) installed _ applied
      exact Publication.retry_preserves (fun _ _ _ validReplacement => validReplacement) earlier path

end Alvoki.Storage.CheckpointPublication
