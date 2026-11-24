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

end Alvoki.Storage.CheckpointPublication
