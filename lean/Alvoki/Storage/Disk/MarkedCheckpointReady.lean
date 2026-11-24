import Alvoki.Storage.Disk.MarkedCheckpointPublication
import Alvoki.Storage.Disk.MarkedSessionTrace
import Alvoki.Storage.Disk.CheckpointHistory

namespace Alvoki.WAL.Boundary
open Storage

/-- The current directory bindings come from the live writer. The checkpoint
stores the durable run map, which ordinary writes and WAL recovery preserve. -/
def FixedMarkedCheckpoint.publicationInput (checkpoint : FixedMarkedCheckpoint)
    (writer : MarkedWriterState) : CheckpointPublication.Image :=
  { checkpoint.image with manifest := writer.image.directory.project .manifest }

private theorem checkpointSuccessorUnreachable {writer : MarkedWriterState} {manifest : Option ByteArray}
    {initial : CheckpointPublication.Image} {installedGeneration : UInt64}
    (ready : writer.ReadyFor manifest)
    (projects : initial.manifest = writer.image.directory.project .manifest)
    (loadedGeneration : ((manifest.mapM fun bytes => (Manifest.decode bytes).map (·.generation)).map
      (·.getD 0) : Except String UInt64) = .ok installedGeneration)
    (generationFits : installedGeneration.toNat + 1 < UInt64.size) :
    initial.Unreachable (UInt64.ofNat (installedGeneration.toNat + 1)) := by
  have active : initial.manifest.active = manifest := by
    rw [projects]
    exact congrArg DirectoryPublication.Bindings.manifest ready.settled.1
  have crashes : initial.manifest.crashImages = [manifest] := by
    rw [projects]
    simp [DirectoryPublication.Image.project, DirectoryPublication.Bindings.get, ready.settled.2.1,
      ready.settled.1]
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
  rw [oldGeneration, UInt64.toNat_ofNat_of_lt' generationFits] at sequence
  omega

/-- Each manifest admitted by the checkpoint attempt comes with a witness
for its exact run files and the prefix of the current WAL it represents. -/
def CheckpointRepresentsPrefix (history : List WAL.Write) (header : Manifest.Checkpoint)
    (files : List ByteArray) : Prop :=
  ∃ checkpoint model, CheckpointForRecovery (some (Manifest.encode header)) files checkpoint ∧
    checkpoint.Refines model ∧ RepresentsWalHistory (history.take checkpoint.committed.toNat) model

private theorem checkpointHeaderWatermark {bytes : ByteArray} {files : List ByteArray}
    {table : PackedTable} {header : Manifest.Checkpoint}
    (written : CheckpointForRecovery (some bytes) files table)
    (decoded : Manifest.decode bytes = .ok header) : header.committed = table.committed := by
  cases written with
  | written expected _ _ _ watermark _ floor _ =>
    have same := Except.ok.inj (decoded.symm.trans (Manifest.decode_encode expected floor))
    simpa only [same] using watermark

private theorem FixedMarkedCheckpoint.validPublicationInput (checkpoint : FixedMarkedCheckpoint)
    {writer : MarkedWriterState} {pending : List WAL.Write} (ready : writer.ReadyFor checkpoint.manifest)
    (history : writer.history = checkpoint.covered ++ pending)
    (represents : RepresentsWalHistory checkpoint.covered checkpoint.model) :
    (checkpoint.publicationInput writer).Valid writer.history.length.toUInt64
      (CheckpointRepresentsPrefix writer.history) := by
  let initial := checkpoint.publicationInput writer
  have active : initial.manifest.active = checkpoint.manifest :=
    congrArg DirectoryPublication.Bindings.manifest ready.settled.1
  have crashes : initial.manifest.crashImages = [checkpoint.manifest] := by
    simp [initial, publicationInput, DirectoryPublication.Image.project,
      DirectoryPublication.Bindings.get, ready.settled.2.1, ready.settled.1]
  have clock : writer.history.length.toUInt64 = writer.table.committed := by rw [ready.count]; simp
  have coveredPrefix : writer.history.take checkpoint.table.committed.toNat = checkpoint.covered := by
    rw [history, ← checkpoint.watermark]
    simp
  have accepted : initial.Accepts writer.history.length.toUInt64 (CheckpointRepresentsPrefix writer.history)
      checkpoint.manifest := by
    cases selected : checkpoint.manifest with
    | none => trivial
    | some bytes =>
      have old := checkpoint.accepted
      rw [selected] at old
      obtain ⟨header, files, decoded, written, _, count, durable⟩ := old
      have exactClock := checkpointHeaderWatermark (selected ▸ checkpoint.written) decoded
      have within : header.committed ≤ writer.history.length.toUInt64 := by
        rw [clock, UInt64.le_iff_toNat_le, exactClock, ← ready.count, ← checkpoint.watermark, history]
        simp
      exact ⟨header, files, decoded, ⟨checkpoint.table, checkpoint.model, written,
        checkpoint.represents, coveredPrefix.symm ▸ represents⟩, within, count, durable⟩
  refine ⟨?_, active.symm ▸ accepted, ?_⟩
  · change initial.manifest.crashImages ≠ []
    rw [crashes]
    simp
  · intro candidate survives
    rw [crashes] at survives
    exact (List.mem_singleton.mp survives).symm ▸ accepted

/-- The reports from the shared checkpoint schedule give an actual retry
transition. The old checkpoint witness comes from the input state. The new
one comes from the adapter's prepared runs and the live table's WAL history. -/
theorem checkpointMarked_reported {writer : MarkedWriterState} (old : FixedMarkedCheckpoint)
    {checkpoint : PackedTable} {pending : List WAL.Write}
    {model : Sequential.SnapshotTable UInt64} {installedGeneration : UInt64}
    (ready : writer.ReadyFor old.manifest) (history : writer.history = old.covered ++ pending)
    (oldRepresents : RepresentsWalHistory old.covered old.model)
    (loadedGeneration : ((old.manifest.mapM fun bytes => (Manifest.decode bytes).map (·.generation)).map
      (·.getD 0) : Except String UInt64) = .ok installedGeneration)
    (generationFits : installedGeneration.toNat + 1 < UInt64.size)
    (prepared : (flushForCheckpoint writer.table id : Except String PackedTable) = .ok checkpoint)
    (refines : writer.table.Refines model) (represents : RepresentsWalHistory writer.history model)
    (runCountFits : checkpoint.runs.length < UInt64.size)
    (report : CheckpointPublication.Step → CheckpointPublication.StepReport) :
    let initial := old.publicationInput writer
    let next : CheckpointPublication.RunSet :=
      ⟨checkpointHeader checkpoint (UInt64.ofNat (installedGeneration.toNat + 1)),
        checkpoint.runs.map (·.run.bytes)⟩
    let expected := CheckpointRepresentsPrefix writer.history
    initial.Valid writer.history.length.toUInt64 expected ∧
      match initial.runWithReports next report with
      | .ok _ after | .error _ after =>
        CheckpointPublication.Retry writer.history.length.toUInt64 expected initial after := by
  intro initial next expected
  refine ⟨old.validPublicationInput ready history oldRepresents, ?_⟩
  have fresh : initial.Unreachable next.header.generation :=
    checkpointSuccessorUnreachable ready rfl loadedGeneration generationFits
  obtain ⟨abstract, written, relation, canonical⟩ := CheckpointForRecovery.of_flushForCheckpoint_history
    prepared refines represents ready.rowBounds runCountFits next.header.generation
  have committed : next.header.committed ≤ writer.history.length.toUInt64 := by
    change checkpoint.committed ≤ writer.history.length.toUInt64
    have clock : writer.history.length.toUInt64 = writer.table.committed := by rw [ready.count]; simp
    rw [clock, UInt64.le_iff_toNat_le, relation.committed, canonical.committed_count, ← ready.count]
    exact List.length_take_le' ..
  have floor : next.header.floor ≤ next.header.committed := by
    change checkpoint.pins.floor ≤ checkpoint.committed
    rw [relation.pins, relation.committed]
    exact abstract.floor_committed
  have count : next.header.runCount.toNat = next.files.length := by
    change (checkpoint.runs.length.toUInt64).toNat = (checkpoint.runs.map (·.run.bytes)).length
    rw [List.length_map, UInt64.toNat_ofNat_of_lt' runCountFits]
  have intent : expected next.header next.files := ⟨checkpoint, abstract, written, relation, canonical⟩
  have outcome := initial.runWithReports_outcome next report
  cases ran : initial.runWithReports next report with
  | ok _ after =>
    rw [ran] at outcome
    apply CheckpointPublication.Retry.attempt (.refl _) next fresh committed floor count intent
      (CheckpointPublication.steps next.files.length).length
    simpa using outcome
  | error _ after =>
    rw [ran] at outcome
    obtain ⟨cut, executed⟩ := outcome
    exact CheckpointPublication.Retry.attempt (.refl _) next fresh committed floor count intent cut executed

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
    (refines : writer.table.Refines model) (runCountFits : checkpoint.runs.length < UInt64.size) :
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
  have fresh : initial.Unreachable next.header.generation :=
    checkpointSuccessorUnreachable ready projects loadedGeneration generationFits
  obtain ⟨written, committed, relation⟩ := CheckpointForRecovery.of_flushForCheckpoint
    prepared refines runCountFits ready.rowBounds.runs ready.rowBounds.memory next.header.generation
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
    ⟨settled, ready.ordered, watermark, ready.length, ready.fits, written.rowBounds⟩⟩

end Alvoki.WAL.Boundary
