import Alvoki.Storage.Disk.MarkedCheckpointPublication
import Alvoki.Storage.Disk.MarkedSessionTrace

namespace Alvoki.WAL.Boundary
open Storage

/-- A successful checkpoint installs the prepared table and its exact run
files at the successor generation. It leaves the marked WAL history and
byte count intact. The new checkpoint covers the whole current WAL, so a
subsequent open starts with no pending writes. The live model and row
bounds must already hold before the adapter's flush decision. -/
theorem checkpointMarked_ready {writer : MarkedWriterState} {manifest : Option ByteArray}
    {initial published : CheckpointPublication.Image} {checkpoint : PackedTable}
    {model : Sequential.SnapshotTable UInt64} {installedGeneration : UInt64}
    (ready : writer.ReadyFor manifest)
    (projects : initial.manifest = writer.image.directory.project .manifest)
    (loadedGeneration : ((manifest.mapM fun bytes => (Manifest.decode bytes).map (·.generation)).map
      (·.getD 0) : Except String UInt64) = .ok installedGeneration)
    (generationFits : installedGeneration.toNat + 1 < UInt64.size)
    (prepared : (flushForCheckpoint writer.table id : Except String PackedTable) = .ok checkpoint)
    (refines : writer.table.Refines model) (runCountFits : checkpoint.runs.length < UInt64.size)
    (runBound : ∀ run ∈ writer.table.runs,
      ∀ row ∈ run.history.rows, row.sequence ≤ writer.table.committed)
    (memoryBound : ∀ row ∈ writer.table.memory.rows, row.sequence ≤ writer.table.committed) :
    let next : CheckpointPublication.RunSet :=
      ⟨checkpointHeader checkpoint (UInt64.ofNat (installedGeneration.toNat + 1)),
        checkpoint.runs.map (·.run.bytes)⟩
    initial.execute next (CheckpointPublication.steps next.files.length) = some published →
    initial.Unreachable next.header.generation ∧
    ∃ fixed : FixedMarkedCheckpoint,
      fixed.manifest = some (Manifest.encode next.header) ∧ fixed.files = next.files ∧
      fixed.image = published ∧ fixed.walSequence = writer.table.committed ∧
      fixed.table = checkpoint ∧ fixed.covered = writer.history ∧
      fixed.model = (if writer.table.memory.rows.isEmpty then model else model.flush) ∧
      ({ writer with table := checkpoint, image := published.markedReopenImage writer.image } :
        MarkedWriterState).ReadyFor fixed.manifest := by
  intro next ran
  have active : initial.manifest.active = manifest := by
    rw [projects]
    exact congrArg DirectoryPublication.Bindings.manifest ready.settled.1
  have crashes : initial.manifest.crashImages = [manifest] := by
    rw [projects]
    simp [DirectoryPublication.Image.project, DirectoryPublication.Bindings.get, ready.settled.2.1,
      ready.settled.1]
  have fresh : initial.Unreachable next.header.generation := by
    intro bytes selectable header decoded same
    have oldManifest : manifest = some bytes := by
      rw [active, crashes] at selectable
      rcases selectable with selected | survives
      · exact selected
      · exact (List.mem_singleton.mp survives).symm
    have oldGeneration : header.generation = installedGeneration := by
      rw [oldManifest] at loadedGeneration
      simpa [Option.mapM, decoded, Functor.map, Except.map] using loadedGeneration
    have sequence := congrArg UInt64.toNat same
    change header.generation.toNat = (UInt64.ofNat (installedGeneration.toNat + 1)).toNat at sequence
    rw [oldGeneration, UInt64.toNat_ofNat_of_lt' generationFits] at sequence
    omega
  obtain ⟨written, committed, relation⟩ := CheckpointForRecovery.of_flushForCheckpoint
    prepared refines runCountFits runBound memoryBound next.header.generation
  obtain ⟨_, after, completed, settled, durable⟩ :=
    CheckpointPublication.checkpointMarked_complete next ready.settled projects
  have same := Option.some.inj (completed.symm.trans ran)
  subst after
  have floor : next.header.floor ≤ next.header.committed := by
    change checkpoint.pins.floor ≤ checkpoint.committed
    rw [relation.pins, relation.committed]
    exact (if writer.table.memory.rows.isEmpty then model else model.flush).floor_committed
  have count : next.header.runCount.toNat = next.files.length := by
    change (checkpoint.runs.length.toUInt64).toNat = (checkpoint.runs.map (·.run.bytes)).length
    rw [List.length_map, UInt64.toNat_ofNat_of_lt' runCountFits]
  have covered : next.header.committed = writer.table.committed := committed
  have accepted : published.Accepts writer.table.committed (fun header files =>
      CheckpointForRecovery (some (Manifest.encode header)) files checkpoint)
      (some (Manifest.encode next.header)) :=
    ⟨next.header, next.files, Manifest.decode_encode _ floor, written,
      UInt64.le_of_eq covered, count, fun index _ => durable index⟩
  have watermark : writer.history.length = checkpoint.committed.toNat := by
    rw [committed]
    exact ready.count
  let fixed : FixedMarkedCheckpoint := {
    manifest := some (Manifest.encode next.header)
    files := next.files
    image := published
    walSequence := writer.table.committed
    table := checkpoint
    model := if writer.table.memory.rows.isEmpty then model else model.flush
    covered := writer.history
    written := written
    accepted := accepted
    represents := relation
    watermark := watermark
  }
  exact ⟨fresh, fixed, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ⟨settled, ready.ordered, watermark, ready.length, ready.fits⟩⟩

end Alvoki.WAL.Boundary
