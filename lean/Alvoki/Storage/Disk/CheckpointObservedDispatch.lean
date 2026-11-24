import Alvoki.Storage.Disk.CheckpointFileDispatch
import Alvoki.Storage.Disk.VersionedCheckpointRetry

namespace Alvoki.Storage.CheckpointPublication

open System Alvoki.Compaction

/-- Interpret a failed run of the actual native file dispatch. The callback
contract records each reported effect on the concrete generation/index or
manifest path. The resulting cut identifies the selected manifest and
durable runs in the projected publication image. -/
theorem observedIntegrityCheckpointFileFailure (initial : Image) (directory : DiskDirectory)
    (checkpoint : PackedTable) (generation : UInt64) {manifest : ByteArray}
    (encoded : encodeCheckpointIntegrityManifest checkpoint generation = .ok manifest)
    (writeRun writeStaged : FilePath → ByteArray → EStateM IO.Error Nat Unit)
    (sync : Array FilePath → EStateM IO.Error Nat Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error Nat Unit)
    (report : Step → StepReport) {cause : IO.Error} {cut : Nat} :
    let plan := VersionedRunSet.integrity
      ⟨checkpointHeader checkpoint generation, checkpoint.runs.map (·.run.bytes)⟩
    let perform := performCheckpointFileStep directory generation checkpoint.runs.toArray
      (directory.file .stagedManifest) manifest
      (fun found => match found with
        | some run => pure run
        | none => throw (IO.userError "checkpoint run index is out of bounds"))
      writeRun writeStaged sync renameFile
    ReachedFileReports report perform (steps checkpoint.runs.length) 0 →
    run checkpoint.runs.toArray.size perform 0 = .error cause cut →
    manifest = plan.manifest.encode ∧
      ∃ published, initial.executeVersioned plan cut = some published ∧
        initial.runVersionedWithReports plan report = some (.error () published) := by
  intro plan perform observed failed
  have fits : ∀ bytes ∈ checkpoint.runs.map (·.run.bytes), bytes.size < UInt64.size := by
    by_cases bounded : (checkpoint.runs.map (·.run.bytes)).all (fun bytes => decide (bytes.size < UInt64.size)) = true
    · exact fun bytes member => of_decide_eq_true (List.all_eq_true.mp bounded bytes member)
    · simp [encodeCheckpointIntegrityManifest, bounded, Bind.bind, Except.bind] at encoded
  have count : plan.files.length = checkpoint.runs.length := by
    simp [plan, VersionedRunSet.integrity]
  refine ⟨Except.ok.inj (encoded.symm.trans (encodeCheckpointIntegrityManifest_exact generation fits)), ?_⟩
  exact initial.runVersionedWithObservedFailure plan report perform (by rwa [count])
    (by simpa only [count, List.size_toArray] using failed)

end Alvoki.Storage.CheckpointPublication
