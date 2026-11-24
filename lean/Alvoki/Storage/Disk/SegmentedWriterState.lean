import Alvoki.Storage.Disk.AppendCutSession
import Alvoki.Storage.Disk.ReopenedSegmentAppend
import Alvoki.Storage.Disk.WalSegmentRotation

namespace Alvoki.Storage.DiskSession

open WalSegmentRepair WAL.Boundary

/-- Proof-side state of a ready segmented writer. The complete WAL chain
includes sealed files already covered by the selected checkpoint. -/
structure SegmentedWriterState where
  installed : Installed
  wal : WalSegmentImage
  history : List WAL.Write
  files : FileImage
  published : CheckpointPublication.Image
  target : Target
  checkpoint : Option (PackedTable × UInt64)
  owners : LockOwners

structure SegmentedWriterState.Ready (directory : DiskDirectory) (descriptor : Nat)
    (state : SegmentedWriterState) : Prop where
  resumed : ResumedAppendReady state.installed state.files state.target state.history state.published state.checkpoint
  layout : state.wal.ReadLayout state.history
  chain : WalSegment.Chain state.history 0 state.wal.segments
  directoryFiles : state.files.directory = state.wal.directory
  sealedFiles : state.files.kept = (state.wal.checkpointReopenFiles state.wal.directory none).kept
  active : state.target.first = state.wal.active.first
  manifestFiles : state.published.manifest = state.files.directory.project .manifest
  held : state.owners.Owns directory descriptor

private theorem selectedGenerationRead {durable binding checkpoint}
    (selected : SelectedIntegrityCheckpoint durable binding checkpoint) :
    ((binding.mapM fun bytes =>
      (Manifest.IntegrityCheckpoint.decode bytes).map (·.header.generation)).map (·.getD 0) : Except String UInt64) =
      .ok (checkpoint.getD (.empty, 0)).2 := by
  cases selected with
  | absent => rfl
  | present decoded _ _ => rw [Option.mapM, decoded]; rfl

theorem ResumedAppendReady.generationRead {installed files target history published checkpoint}
    (ready : ResumedAppendReady installed files target history published checkpoint) :
    ((target.pair.manifest.mapM fun bytes =>
      (Manifest.IntegrityCheckpoint.decode bytes).map (·.header.generation)).map (·.getD 0) : Except String UInt64) =
      .ok installed.generation := by
  rw [ready.generation]
  exact selectedGenerationRead ready.selected

theorem SegmentedWriterState.Ready.generationRead {directory descriptor state}
    (ready : SegmentedWriterState.Ready directory descriptor state) :
    ((state.target.pair.manifest.mapM fun bytes =>
      (Manifest.IntegrityCheckpoint.decode bytes).map (·.header.generation)).map (·.getD 0) : Except String UInt64) =
      .ok state.installed.generation :=
  ready.resumed.generationRead

theorem SegmentedWriterState.Ready.walDirectorySettled {directory descriptor state}
    (ready : SegmentedWriterState.Ready directory descriptor state) :
    state.wal.directory.crashImages = [state.wal.directory.active] := by
  rw [← ready.directoryFiles, ready.resumed.ready.settled, ready.resumed.ready.selected]

/-- The expected native extent follows from the installed marker. The
no-follow metadata read still has to report a private regular file. -/
theorem SegmentedWriterState.Ready.activeExtent {directory descriptor state}
    (ready : SegmentedWriterState.Ready directory descriptor state) :
    state.wal.active.bytes.size = state.installed.walBytes - state.installed.activeFirst * WAL.frameSize := by
  rw [ready.layout.activeBytes, WAL.encode_size, List.length_drop, Nat.mul_comm WAL.frameSize,
    Nat.sub_mul, ready.resumed.bytes, WAL.encode_size, Nat.mul_comm WAL.frameSize,
    ready.resumed.keeper, ready.active]

theorem SegmentedWriterState.Ready.activeContents {directory descriptor state}
    (ready : SegmentedWriterState.Ready directory descriptor state) :
    state.files.keeper.active = some state.wal.active.bytes := by
  rw [ready.resumed.ready.keeper, ready.resumed.contents, ready.active, ready.layout.activeBytes]

theorem SegmentedWriterState.Ready.appendInput {directory descriptor state}
    (ready : SegmentedWriterState.Ready directory descriptor state) :
    AppendCutWriter state.installed state.wal state.history state.published state.target.range.watermark := by
  have samePair : state.wal.directory.active = state.target.pair :=
    congrArg DirectoryPublication.Image.active ready.directoryFiles.symm |>.trans ready.resumed.ready.selected
  have marker := congrArg Publication.Image.active ready.resumed.markerImage
  have marker : state.files.directory.active.walBoundary =
      some (WAL.Boundary.encode (WAL.encode state.history).size.toUInt64) := marker
  have rangeEq : state.target.range = ⟨state.target.range.watermark, state.history.length⟩ := by
    exact congrArg (fun through => { state.target.range with through }) ready.resumed.through
  refine ⟨ready.layout, ready.chain, ready.resumed.ordered, ready.walDirectorySettled,
    ready.directoryFiles ▸ marker, ?_, ?_, ?_, ready.resumed.bytes, ready.resumed.keeper.trans ready.active,
    ready.resumed.canonical⟩
  · rw [samePair, state.target.decoded, rangeEq]
  · rw [samePair]; exact ready.resumed.accepted
  · rw [samePair]; exact ready.generationRead

theorem SegmentedWriterState.Ready.walValid {directory descriptor state}
    (ready : SegmentedWriterState.Ready directory descriptor state) : state.wal.Valid state.history := by
  apply WalSegmentImage.Valid.of_chain ready.chain
  intro pair selected
  have exact : pair = state.wal.directory.active := by
    simpa [WalSegmentImage.Selects, ready.walDirectorySettled] using selected
  subst pair
  exact ⟨_, ready.appendInput.range, Nat.zero_le _, Nat.le_refl _⟩

theorem SegmentedWriterState.Ready.rotationInput {directory descriptor state}
    (ready : SegmentedWriterState.Ready directory descriptor state)
    (nonempty : state.installed.activeFirst < state.installed.walBytes / WAL.frameSize) :
    WalSegmentRotation.CanRotate state.wal state.history := by
  have endAt : state.installed.walBytes / WAL.frameSize = state.history.length := by
    rw [ready.resumed.bytes, WAL.encode_size, Nat.mul_comm,
      Nat.mul_div_cancel _ (by decide : 0 < WAL.frameSize)]
  refine ⟨?_, ready.layout.activeEnd, ?_⟩
  · rwa [ready.appendInput.first, endAt, ← ready.layout.activeEnd] at nonempty
  · intro segment occurs
    exact ((List.pairwise_append.mp ready.layout.ordered).2.2 segment occurs state.wal.active (by simp)).1

/-- The settled manifest's selected generation is older than the next
in-range generation. -/
theorem SegmentedWriterState.Ready.freshCheckpoint {directory descriptor state}
    (ready : SegmentedWriterState.Ready directory descriptor state)
    (fits : state.installed.generation.toNat + 1 < UInt64.size) :
    state.published.UnreachableVersioned (state.installed.generation.toNat + 1).toUInt64 := by
  intro bytes chosen manifest decoded
  have same : state.target.pair.manifest = some bytes := by
    simp [ready.manifestFiles, DirectoryPublication.Image.project, DirectoryPublication.Bindings.get,
      ready.resumed.ready.selected, ready.resumed.ready.settled] at chosen
    exact chosen.elim id Eq.symm
  have generation := ready.generationRead
  rw [same] at generation
  cases strict : Manifest.IntegrityCheckpoint.decode bytes with
  | error error => simp [Option.mapM, strict, Except.map, Functor.map] at generation
  | ok parsed =>
    have exactGeneration : parsed.header.generation = state.installed.generation := by
      rw [Option.mapM, strict] at generation
      exact Except.ok.inj generation
    have sameManifest := Except.ok.inj ((Manifest.VersionedCheckpoint.decode_integrity strict).symm.trans decoded)
    subst manifest
    change parsed.header.generation ≠ _
    rw [exactGeneration]
    intro equal
    have sameCount := congrArg UInt64.toNat equal
    rw [UInt64.toNat_ofNat_of_lt' fits] at sameCount
    omega

/-- Rebind the proof-side checkpoint projection to the actual settled
directory. The durable file map selected during recovery is preserved. -/
def SegmentedWriterState.ofReopen (installed : Installed) (wal : WalSegmentImage) (history : List WAL.Write)
    (published : CheckpointPublication.Image) (target : Target) (checkpoint : Option (PackedTable × UInt64))
    (files : LockedFileState FileImage) : SegmentedWriterState :=
  ⟨installed, { wal with directory := files.image.directory }, history, files.image,
    { published with manifest := files.image.directory.project .manifest }, target, checkpoint, files.owners⟩

/-- Carry the exact installed payload and held lock into the writer state.
The full sealed inventory comes from the preceding cut, including files
older than the selected checkpoint that this reopen did not need to read. -/
theorem AppendCutReady.writerReady {directory descriptor liveRefs history published initial target generation result}
    (opened : AppendCutReady directory descriptor liveRefs history published initial target generation result)
    {wal : WalSegmentImage} (layout : wal.ReadLayout history) (chain : WalSegment.Chain history 0 wal.segments)
    (keeper : target.first = wal.active.first)
    (sealed : initial.kept = (wal.checkpointReopenFiles wal.directory none).kept) :
    ∃ session final, ∃ writer : SegmentedWriterState,
      result = .ok session final ∧ session.directory = directory ∧ session.descriptor = descriptor ∧
      session.phase = .ready writer.installed ∧ writer.files = final.image ∧ writer.owners = final.owners ∧
      writer.wal = { wal with directory := final.image.directory } ∧ writer.target = target ∧
      writer.history = history ∧ writer.published.durable = published.durable ∧
      writer.Ready directory descriptor := by
  obtain ⟨through, trimmed, accepted, ordered, checkpoint, table, model, session, final, returned, selected,
    gen, _, path, lock, phase, durable, kept, held, _, bounds, refines, represents, _, _, _, _⟩ := opened
  let installed : Installed := ⟨table, generation, (WAL.encode history).size, target.first⟩
  refine ⟨session, final, SegmentedWriterState.ofReopen installed wal history published target checkpoint final,
    returned, path, lock, phase, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact ⟨⟨durable, through, rfl, rfl, trimmed, gen, selected, accepted, ordered, bounds, ⟨model, refines, represents⟩⟩,
    ⟨layout.ordered, layout.forward, layout.activeEnd, layout.activeBytes⟩, chain, rfl, kept.trans sealed,
    keeper, rfl, held⟩

end Alvoki.Storage.DiskSession
